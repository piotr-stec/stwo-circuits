use crate::prover::{BaseColumnPool, CircuitProof, SimdBackend, prove_circuit_assignment};
use crate::prover::{
    CircuitProofKeccak, preprare_circuit_proof_for_circuit_verifier,
    prove_circuit_assignment_keccak, prove_circuit_assignment_keccak_with_config,
};
use alloy::primitives::{Address, Bytes, FixedBytes, U256};
use alloy::providers::{Provider, ProviderBuilder};
use alloy::rpc::types::TransactionRequest;
use alloy::sol_types::SolCall;
use alloy::sol;
use circuit_air::components::{CircuitComponents, ComponentList, N_COMPONENTS};
use circuit_air::CircuitInteractionElements;
use circuit_air::lookup_sum;
use circuit_air::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuit_air::verify::{CircuitConfig, verify_circuit};
use circuit_common::finalize::finalize_context;
use circuit_common::preprocessed::PreprocessedCircuit;
use circuits::blake::blake;
use circuits::context::Var;
use circuits::poseidon2::poseidon_gate;
use circuits::eval;
use circuits::ivalue::{IValue, qm31_from_u32s};
use circuits::ops::{output, permute};
use circuits::{context::Context, ops::guess};
use circuits_stark_verifier::proof::ProofConfig;
use circuits_stark_verifier::proof_from_stark_proof::{pack_component_log_sizes, pack_enable_bits};
use expect_test::expect;
use itertools::Itertools;
use num_traits::{One, Zero};
use stwo::core::air::{Component, Components as AirComponents};
use stwo::core::channel::Channel;
use stwo::core::channel::{Blake2sM31Channel, KeccakChannel};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec};
use stwo::core::proof::StarkProof;
use stwo::core::utils::bit_reverse;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::core::vcs_lifted::keccak_merkle::{KeccakMerkleChannel, KeccakMerkleHasher};
use stwo::prover::poly::circle::SecureCirclePoly;
use stwo_constraint_framework::{FrameworkComponent, FrameworkEval};
use stwo_polynomial::verify::verify;

// Not a power of 2 so that we can test component padding.
const N: usize = 1030;
const ONCHAIN_TEST_N: usize = 64;

sol! {
    struct SolCM31 {
        uint32 real;
        uint32 imag;
    }

    struct SolQM31 {
        SolCM31 first;
        SolCM31 second;
    }

    struct SolFriConfig {
        uint32 logBlowupFactor;
        uint32 logLastLayerDegreeBound;
        uint256 nQueries;
    }

    struct SolConfig {
        uint32 powBits;
        SolFriConfig friConfig;
        uint32 liftingLogSize;
    }

    struct SolDecommitment {
        bytes32[] hashWitness;
        uint32[] columnWitness;
    }

    struct SolFriLayerProof {
        SolQM31[] friWitness;
        bytes decommitment;
        bytes32 commitment;
    }

    struct SolFriProof {
        SolFriLayerProof firstLayer;
        SolFriLayerProof[] innerLayers;
        SolQM31[] lastLayerPoly;
    }

    struct SolCompositionPoly {
        uint32[] coeffs0;
        uint32[] coeffs1;
        uint32[] coeffs2;
        uint32[] coeffs3;
    }

    struct SolProof {
        SolConfig config;
        bytes32[] commitments;
        SolQM31[][][] sampledValues;
        SolDecommitment[] decommitments;
        uint32[][] queriedValues;
        uint64 proofOfWork;
        SolFriProof friProof;
        SolCompositionPoly compositionPoly;
    }

    struct SolComponentInfo {
        uint32 maxConstraintLogDegreeBound;
        uint32 logSize;
        int32[][][] maskOffsets;
        uint256[] preprocessedColumns;
    }

    struct SolComponentParams {
        uint32 logSize;
        SolQM31 claimedSum;
        SolComponentInfo info;
    }

    struct SolClaimData {
        uint32 nComponents;
        SolQM31[] packedEnableBits;
        SolQM31[] packedComponentLogSizes;
        SolQM31[] outputValues;
    }

    struct SolInteractionClaimData {
        SolQM31[] claimedSums;
    }

    struct SolVerificationParams {
        SolComponentParams[] componentParams;
        uint256 nPreprocessedColumns;
        uint32 componentsCompositionLogDegreeBound;
        bool includeAllPreprocessedColumns;
        uint32 interactionPowBits;
        SolClaimData claim;
        SolInteractionClaimData interactionClaim;
    }

    interface IStwoVerifier {
        function verify(
            SolProof calldata proof,
            SolVerificationParams calldata params,
            uint32[][] memory treeColumnLogSizes,
            uint32 channelSalt,
            uint64 interactionPowNonce
        ) external returns (bool);
    }
}

fn qm31_to_sol(value: QM31) -> SolQM31 {
    SolQM31 {
        first: SolCM31 {
            real: value.0 .0 .0,
            imag: value.0 .1 .0,
        },
        second: SolCM31 {
            real: value.1 .0 .0,
            imag: value.1 .1 .0,
        },
    }
}

fn encode_fri_decommitment(hash_witness: &[FixedBytes<32>]) -> Bytes {
    let mut encoded = Vec::new();
    encoded.extend_from_slice(&U256::from(hash_witness.len()).to_be_bytes::<32>());
    for hash in hash_witness {
        encoded.extend_from_slice(hash.as_slice());
    }
    encoded.extend_from_slice(&U256::ZERO.to_be_bytes::<32>());
    Bytes::from(encoded)
}

fn component_to_sol_params<E: FrameworkEval>(
    component: &FrameworkComponent<E>,
    log_size: u32,
    claimed_sum: QM31,
) -> SolComponentParams {
    SolComponentParams {
        logSize: log_size,
        claimedSum: qm31_to_sol(claimed_sum),
        info: SolComponentInfo {
            maxConstraintLogDegreeBound: component.max_constraint_log_degree_bound(),
            logSize: log_size,
            maskOffsets: component
                .info()
                .mask_offsets
                .0
                .iter()
                .map(|tree| {
                    tree.iter()
                        .map(|col| col.iter().map(|&offset| offset as i32).collect())
                        .collect()
                })
                .collect(),
            preprocessedColumns: component
                .preprocessed_column_indices()
                .iter()
                .map(|&idx| U256::from(idx))
                .collect(),
        },
    }
}

fn convert_stark_proof_to_solidity(
    proof: &StarkProof<KeccakMerkleHasher>,
    composition_polynomial: SecureCirclePoly<SimdBackend>,
    config: stwo::core::pcs::PcsConfig,
) -> SolProof {
    let commitments = proof
        .0
        .commitments
        .iter()
        .map(|commitment| FixedBytes::from(commitment.0))
        .collect_vec();

    let sampled_values = proof
        .sampled_values
        .iter()
        .map(|column| {
            column
                .iter()
                .map(|row| row.iter().map(|&qm31| qm31_to_sol(qm31)).collect_vec())
                .collect_vec()
        })
        .collect_vec();

    let decommitments = proof
        .0
        .decommitments
        .iter()
        .map(|decom| SolDecommitment {
            hashWitness: decom
                .hash_witness
                .iter()
                .map(|h| FixedBytes::from(h.0))
                .collect_vec(),
            columnWitness: vec![],
        })
        .collect_vec();

    let first_layer = {
        let layer = &proof.0.fri_proof.first_layer;
        let hashes = layer
            .decommitment
            .hash_witness
            .iter()
            .map(|h| FixedBytes::from(h.0))
            .collect_vec();
        SolFriLayerProof {
            friWitness: layer.fri_witness.iter().map(|&v| qm31_to_sol(v)).collect_vec(),
            decommitment: encode_fri_decommitment(&hashes),
            commitment: FixedBytes::from(layer.commitment.0),
        }
    };

    let inner_layers = proof
        .0
        .fri_proof
        .inner_layers
        .iter()
        .map(|layer| {
            let hashes = layer
                .decommitment
                .hash_witness
                .iter()
                .map(|h| FixedBytes::from(h.0))
                .collect_vec();
            SolFriLayerProof {
                friWitness: layer.fri_witness.iter().map(|&v| qm31_to_sol(v)).collect_vec(),
                decommitment: encode_fri_decommitment(&hashes),
                commitment: FixedBytes::from(layer.commitment.0),
            }
        })
        .collect_vec();

    let mut last_layer_coefs = proof.clone().0.fri_proof.last_layer_poly.into_ordered_coefficients();
    bit_reverse(&mut last_layer_coefs);
    let last_layer_poly = last_layer_coefs.into_iter().map(qm31_to_sol).collect_vec();

    let composition_coordinates = composition_polynomial
        .into_coordinate_polys()
        .iter()
        .map(|poly| {
            let mut layer = Vec::new();
            for coeff in &poly.coeffs.data {
                layer.extend(coeff.to_array().iter().map(|m| m.0));
            }
            layer
        })
        .collect_vec();

    SolProof {
        config: SolConfig {
            powBits: config.pow_bits,
            friConfig: SolFriConfig {
                logBlowupFactor: config.fri_config.log_blowup_factor,
                logLastLayerDegreeBound: config.fri_config.log_last_layer_degree_bound,
                nQueries: U256::from(config.fri_config.n_queries),
            },
            liftingLogSize: config.lifting_log_size.unwrap_or_default(),
        },
        commitments,
        sampledValues: sampled_values,
        decommitments,
        queriedValues: proof
            .0
            .queried_values
            .iter()
            .map(|tree_values| {
                tree_values
                    .iter()
                    .flat_map(|column_values| column_values.iter().map(|value| value.0))
                    .collect_vec()
            })
            .collect_vec(),
        proofOfWork: proof.proof_of_work,
        friProof: SolFriProof {
            firstLayer: first_layer,
            innerLayers: inner_layers,
            lastLayerPoly: last_layer_poly,
        },
        compositionPoly: SolCompositionPoly {
            coeffs0: composition_coordinates[0].clone(),
            coeffs1: composition_coordinates[1].clone(),
            coeffs2: composition_coordinates[2].clone(),
            coeffs3: composition_coordinates[3].clone(),
        },
    }
}

pub fn build_fibonacci_context() -> Context<QM31> {
    build_fibonacci_context_with_n(N)
}

pub fn build_fibonacci_context_with_n(n: usize) -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    let (mut a, mut b) = (guess(&mut context, QM31::zero()), guess(&mut context, QM31::one()));
    for _ in 2..n {
        (a, b) = (b, eval!(&mut context, (a) + (b)));
    }

    if n == N {
        expect![[r#"
            (809871181 + 0i) + (0 + 0i)u
        "#]]
        .assert_debug_eq(&context.get(b));
    }
    output(&mut context, b);

    context
}

pub fn build_permutation_context() -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    let a = guess(&mut context, qm31_from_u32s(0, 2, 0, 2));
    let b = guess(&mut context, qm31_from_u32s(1, 1, 1, 1));

    let outputs = permute(&mut context, &[a, b], IValue::sort_by_u_coordinate);
    let _outputs = permute(&mut context, &outputs, IValue::sort_by_u_coordinate);

    context
}

pub fn build_blake_gate_context() -> Context<QM31> {
    let mut context = Context::<QM31>::default();
    context.enable_assert_eq_on_eval();

    let mut inputs: Vec<Var> = vec![];
    let n_inputs = 9;
    let n_bytes = n_inputs * 16;
    let n_blake_gates = 15;
    for i in 0..n_inputs {
        inputs.push(guess(
            &mut context,
            qm31_from_u32s(4 * i + 82, 4 * i + 83, 4 * i + 84, 4 * i + 85),
        ));
    }
    for _ in 0..n_blake_gates {
        let output = blake(&mut context, &inputs, n_bytes as usize);
        eval!(&mut context, (output.0) + (output.1));
    }

    context
}

#[test]
#[ignore = "Blake gate AIR removed on feat/poseidon-instead-blake branch"]
fn test_prove_and_stark_verify_blake_gate_context() {
    let mut blake_gate_context = build_blake_gate_context();
    blake_gate_context.finalize_guessed_vars();
    blake_gate_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut blake_gate_context);
    let CircuitProof {
        components,
        claim,
        interaction_claim,
        pcs_config,
        stark_proof,
        interaction_pow_nonce,
        channel_salt,
    } = prove_circuit_assignment(
        blake_gate_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    assert!(stark_proof.is_ok(), "Got error: {}", stark_proof.err().unwrap());
    let proof = stark_proof.unwrap();

    let verifier_channel = &mut Blake2sM31Channel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(verifier_channel);
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(pcs_config);

    // Retrieve the expected column sizes in each commitment interaction, from the AIR.
    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));

    commitment_scheme.commit(
        proof.proof.commitments[0],
        &preprocessed_circuit.preprocessed_trace.log_sizes(),
        verifier_channel,
    );
    claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[1], &sizes[1], verifier_channel);

    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);

    verifier_channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(verifier_channel);

    interaction_claim.mix_into(verifier_channel);

    commitment_scheme.commit(proof.proof.commitments[2], &sizes[2], verifier_channel);
    stwo::core::verifier::verify_ex(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        proof.proof,
        true,
    )
    .unwrap();

    assert_eq!(
        lookup_sum(
            &claim,
            &interaction_claim,
            &interaction_elements,
            &preprocessed_circuit.params.output_addresses,
        ),
        QM31::zero()
    );
}

#[test]
fn test_prove_and_stark_verify_permutation_context() {
    let mut permutation_context = build_permutation_context();
    permutation_context.finalize_guessed_vars();
    permutation_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut permutation_context);
    let CircuitProof {
        pcs_config,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components,
        stark_proof,
        channel_salt,
    } = prove_circuit_assignment(
        permutation_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    assert!(stark_proof.is_ok());
    let proof = stark_proof.unwrap();

    // Verify.
    let verifier_channel = &mut Blake2sM31Channel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(verifier_channel);
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(pcs_config);

    // Retrieve the expected column sizes in each commitment interaction, from the AIR.
    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));

    commitment_scheme.commit(
        proof.proof.commitments[0],
        &preprocessed_circuit.preprocessed_trace.log_sizes(),
        verifier_channel,
    );
    claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[1], &sizes[1], verifier_channel);
    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);
    verifier_channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(verifier_channel);
    interaction_claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[2], &sizes[2], verifier_channel);
    stwo::core::verifier::verify_ex(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        proof.proof,
        true,
    )
    .unwrap();

    assert_eq!(
        lookup_sum(
            &claim,
            &interaction_claim,
            &interaction_elements,
            &preprocessed_circuit.params.output_addresses,
        ),
        QM31::zero()
    );
}

#[test]
fn test_prove_and_stark_verify_fibonacci_context() {
    let mut fibonacci_context = build_fibonacci_context();
    fibonacci_context.finalize_guessed_vars();
    fibonacci_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut fibonacci_context);
    let CircuitProof {
        pcs_config,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components,
        stark_proof,
        channel_salt,
    } = prove_circuit_assignment(
        fibonacci_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    assert!(stark_proof.is_ok());
    let proof = stark_proof.unwrap();

    // Verify.
    let verifier_channel = &mut Blake2sM31Channel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(verifier_channel);
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(pcs_config);

    // Retrieve the expected column sizes in each commitment interaction, from the AIR.
    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));

    commitment_scheme.commit(
        proof.proof.commitments[0],
        &preprocessed_circuit.preprocessed_trace.log_sizes(),
        verifier_channel,
    );
    claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[1], &sizes[1], verifier_channel);
    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);
    verifier_channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(verifier_channel);
    interaction_claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[2], &sizes[2], verifier_channel);
    stwo::core::verifier::verify_ex(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        proof.proof,
        true,
    )
    .unwrap();

    assert_eq!(
        lookup_sum(
            &claim,
            &interaction_claim,
            &interaction_elements,
            &preprocessed_circuit.params.output_addresses,
        ),
        QM31::zero()
    );
}

#[test]
fn test_prove_and_stark_verify_fibonacci_context_keccak_channel() {
    let mut fibonacci_context = build_fibonacci_context();
    fibonacci_context.finalize_guessed_vars();
    fibonacci_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut fibonacci_context);

    let CircuitProofKeccak {
        pcs_config,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components,
        stark_proof,
        channel_salt,
    } = prove_circuit_assignment_keccak(
        fibonacci_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    assert!(stark_proof.is_ok());
    let proof = stark_proof.unwrap().0;
    // Verify.
    let verifier_channel = &mut KeccakChannel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(verifier_channel);
    let commitment_scheme = &mut CommitmentSchemeVerifier::<KeccakMerkleChannel>::new(pcs_config);
    // Retrieve the expected column sizes in each commitment interaction, from the AIR.
    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));

    commitment_scheme.commit(
        proof.proof.commitments[0],
        &preprocessed_circuit.preprocessed_trace.log_sizes(),
        verifier_channel,
    );
    claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[1], &sizes[1], verifier_channel);
    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);
    verifier_channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(verifier_channel);
    interaction_claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[2], &sizes[2], verifier_channel);

    stwo::core::verifier::verify_ex(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        proof.proof,
        true,
    )
    .unwrap();

    assert_eq!(
        lookup_sum(
            &claim,
            &interaction_claim,
            &interaction_elements,
            &preprocessed_circuit.params.output_addresses,
        ),
        QM31::zero()
    );
}

#[tokio::test]
#[ignore = "requires local anvil and deployed StwoVerifier"]
async fn test_prove_and_verify_on_chain() -> Result<(), Box<dyn std::error::Error>> {
    let mut permutation_context = build_permutation_context();
    permutation_context.finalize_guessed_vars();
    permutation_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut permutation_context);
    let mut onchain_pcs_config = PcsConfig::default();
    onchain_pcs_config.fri_config.n_queries = 2;

    let CircuitProofKeccak {
        pcs_config,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components,
        stark_proof,
        channel_salt,
    } = prove_circuit_assignment_keccak_with_config(
        permutation_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        onchain_pcs_config,
    );
    println!("pcs config: {:?}", pcs_config);

    assert!(stark_proof.is_ok(), "keccak proving failed");
    let (extended_stark_proof, composition_polynomial) = stark_proof.unwrap();
    let stark_proof = extended_stark_proof.clone().proof;
    let stark_proof_to_verify = extended_stark_proof.clone().proof;

    let verifier_channel = &mut KeccakChannel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    println!("Channel digest after mixing salt: {:?}", verifier_channel.digest());
    pcs_config.mix_into(verifier_channel);
    println!("Channel digest after mixing PCS config: {:?}", verifier_channel.digest());
    let commitment_scheme = &mut CommitmentSchemeVerifier::<KeccakMerkleChannel>::new(pcs_config);
    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));
    commitment_scheme.commit(
        stark_proof.commitments[0],
        &preprocessed_circuit.preprocessed_trace.log_sizes(),
        verifier_channel,
    );
    println!("Channel digest after first commitment: {:?}", verifier_channel.digest());
    claim.mix_into(verifier_channel);
    println!("Channel digest after mixing claim: {:?}", verifier_channel.digest());
    commitment_scheme.commit(stark_proof.commitments[1], &sizes[1], verifier_channel);
    println!("Channel digest after second commitment: {:?}", verifier_channel.digest());
    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);
    verifier_channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(verifier_channel);
    interaction_claim.mix_into(verifier_channel);
    commitment_scheme.commit(stark_proof.commitments[2], &sizes[2], verifier_channel);
    println!("Channel digest after third commitment: {:?}", verifier_channel.digest());
    verify(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        stark_proof_to_verify,
        &composition_polynomial,
        true,
    )
    .unwrap();

    let preprocessed_column_ids = preprocessed_circuit.preprocessed_trace.ids();
    let circuit_components = CircuitComponents::new(
        &claim,
        &interaction_elements,
        &interaction_claim,
        &preprocessed_column_ids,
    );

    let component_params = vec![
        component_to_sol_params(
            &circuit_components.eq,
            claim.log_sizes[ComponentList::Eq as usize],
            interaction_claim.claimed_sums[ComponentList::Eq as usize],
        ),
        component_to_sol_params(
            &circuit_components.qm31_ops,
            claim.log_sizes[ComponentList::Qm31Ops as usize],
            interaction_claim.claimed_sums[ComponentList::Qm31Ops as usize],
        ),
        component_to_sol_params(
            &circuit_components.poseidon_gate,
            claim.log_sizes[ComponentList::PoseidonGate as usize],
            interaction_claim.claimed_sums[ComponentList::PoseidonGate as usize],
        ),
    ];

    let component_refs = components.iter().map(|c| c.as_ref()).collect_vec();
    let components_composition_log_degree_bound = AirComponents {
        components: component_refs,
        n_preprocessed_columns: preprocessed_column_ids.len(),
    }
    .composition_log_degree_bound();

    let verification_params = SolVerificationParams {
        componentParams: component_params,
        nPreprocessedColumns: U256::from(preprocessed_column_ids.len()),
        componentsCompositionLogDegreeBound: components_composition_log_degree_bound,
        includeAllPreprocessedColumns: true,
        interactionPowBits: INTERACTION_POW_BITS,
        claim: SolClaimData {
            nComponents: N_COMPONENTS as u32,
            packedEnableBits: pack_enable_bits(
                &claim
                    .log_sizes
                    .iter()
                    .map(|&log_size| log_size > 0)
                    .collect_vec(),
            )
                .into_iter()
                .map(qm31_to_sol)
                .collect_vec(),
            packedComponentLogSizes: pack_component_log_sizes(&claim.log_sizes)
                .into_iter()
                .map(qm31_to_sol)
                .collect_vec(),
            outputValues: claim.output_values.iter().copied().map(qm31_to_sol).collect_vec(),
        },
        interactionClaim: SolInteractionClaimData {
            claimedSums: interaction_claim
                .claimed_sums
                .iter()
                .copied()
                .map(qm31_to_sol)
                .collect_vec(),
        },
    };

    let solidity_proof =
        convert_stark_proof_to_solidity(&stark_proof, composition_polynomial, pcs_config);
    let tree_column_log_sizes = vec![
        preprocessed_circuit.preprocessed_trace.log_sizes(),
        sizes[1].clone(),
        sizes[2].clone(),
    ];

    let rpc_url =
        std::env::var("STWO_RPC_URL").unwrap_or_else(|_| "http://127.0.0.1:8545".to_string());
    let verifier_address = std::env::var("STWO_VERIFIER_ADDRESS")
        .unwrap_or_else(|_| "0x5FbDB2315678afecb367f032d93F642f64180aa3".to_string());

    let provider = ProviderBuilder::new().on_http(rpc_url.parse()?);
    let contract_address = Address::parse_checksummed(&verifier_address, None)?;
    let call_data = IStwoVerifier::verifyCall {
        proof: solidity_proof,
        params: verification_params,
        treeColumnLogSizes: tree_column_log_sizes,
        channelSalt: channel_salt,
        interactionPowNonce: interaction_pow_nonce,
    };
    let mut call_input = TransactionRequest::default()
        .to(contract_address)
        .input(call_data.abi_encode().into());
    call_input.gas = None;

    let result = provider.call(&call_input).await?;
    assert_eq!(result.len(), 32, "unexpected verify() return encoding length");
    assert_eq!(result[31], 1, "on-chain verifier returned false");

    Ok(())
}

const FIBONACCI_CIRCUIT_PREPROCESSED_ROOT: [u32; 8] =
    [1799162176, 335565964, 91003826, 962817318, 881310192, 1530884903, 192868928, 56339769];


#[test]
fn test_prove_and_circuit_verify_fibonacci_context() {
    let mut fibonacci_context = build_fibonacci_context();
    fibonacci_context.finalize_guessed_vars();
    fibonacci_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut fibonacci_context);
    let circuit_proof = prove_circuit_assignment(
        fibonacci_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
    );

    let preprocessed_column_ids = preprocessed_circuit.preprocessed_trace.ids();
    let proof_config = ProofConfig::from_components(
        &all_circuit_components::<QM31>(),
        preprocessed_column_ids.len(),
        &circuit_proof.pcs_config,
        INTERACTION_POW_BITS,
    );
    let pcs_config = circuit_proof.pcs_config;
    let (proof, public_data) =
        preprare_circuit_proof_for_circuit_verifier(circuit_proof, &proof_config);
    let preprocessed_root = proof.preprocessed_root;
    let circuit_config = CircuitConfig {
        config: pcs_config,
        output_addresses: preprocessed_circuit.params.output_addresses.clone(),
        preprocessed_column_ids,
        preprocessed_root,
    };
    verify_circuit(circuit_config, proof, public_data).unwrap();
}

pub fn build_poseidon_gate_context() -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    let a = guess(&mut context, qm31_from_u32s(7, 0, 0, 0));
    let b = guess(&mut context, qm31_from_u32s(42, 0, 0, 0));

    // Hash chain: out0 = poseidon(a, b), out1 = poseidon(out0_limb0, a), etc.
    let mut prev = poseidon_gate(&mut context, a, b);
    for _ in 1..15 {
        prev = poseidon_gate(&mut context, prev, a);
    }
    output(&mut context, prev);

    context
}

#[test]
fn test_prove_and_stark_verify_poseidon_gate_context() {
    let mut ctx = build_poseidon_gate_context();
    ctx.finalize_guessed_vars();
    ctx.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut ctx);
    let CircuitProof {
        components,
        claim,
        interaction_claim,
        pcs_config,
        stark_proof,
        interaction_pow_nonce,
        channel_salt,
    } = prove_circuit_assignment(
        ctx.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    assert!(stark_proof.is_ok(), "proving failed: {}", stark_proof.err().unwrap());
    let proof = stark_proof.unwrap();

    let verifier_channel = &mut Blake2sM31Channel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(verifier_channel);
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sM31MerkleChannel>::new(pcs_config);

    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));

    commitment_scheme.commit(
        proof.proof.commitments[0],
        &preprocessed_circuit.preprocessed_trace.log_sizes(),
        verifier_channel,
    );
    claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[1], &sizes[1], verifier_channel);
    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);
    verifier_channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(verifier_channel);
    interaction_claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[2], &sizes[2], verifier_channel);

    stwo::core::verifier::verify_ex(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        proof.proof,
        true,
    )
    .unwrap();

    assert_eq!(
        lookup_sum(
            &claim,
            &interaction_claim,
            &interaction_elements,
            &preprocessed_circuit.params.output_addresses,
        ),
        QM31::zero()
    );
}

#[test]
fn test_finalize_context() {
    let mut context = build_fibonacci_context();
    finalize_context(&mut context);

    assert!(context.circuit.add.len().is_power_of_two());
    context.validate_circuit();
}
