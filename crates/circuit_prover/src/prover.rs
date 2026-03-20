use crate::witness::trace::TraceGenerator;
use crate::witness::trace::write_interaction_trace;
use crate::witness::trace::write_trace;
use circuit_air::components::CircuitComponents;
use circuit_air::statement::INTERACTION_POW_BITS;
use circuit_air::verify::CircuitPublicData;
use circuit_air::{CircuitClaim, CircuitInteractionClaim, CircuitInteractionElements, lookup_sum};
use circuit_common::CircuitParams;
use circuit_common::Qm31OpsTraceGenerator;
use circuit_common::preprocessed::PreprocessedCircuit;
use circuits::context::Context;
use circuits_stark_verifier::proof::Proof;
use circuits_stark_verifier::proof::{Claim, ProofConfig};
use circuits_stark_verifier::proof_from_stark_proof::{
    pack_component_log_sizes, pack_enable_bits, proof_from_stark_proof,
};
use itertools::Itertools;
use itertools::chain;
use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::Blake2sM31Channel;
use stwo::core::channel::Channel;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::CommitmentSchemeVerifier;
use stwo::core::pcs::PcsConfig;
use stwo::core::pcs::TreeVec;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::ExtendedStarkProof;
use stwo::core::proof_of_work::GrindOps;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleHasher;
use stwo::prover::CommitmentSchemeProver;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::ComponentProver;
pub use stwo::prover::backend::simd::SimdBackend;
pub use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::{ProvingError, prove_ex};
use stwo::prover::backend::Column;

const COMPOSITION_POLYNOMIAL_LOG_DEGREE_BOUND: u32 = 1;

pub struct CircuitProof {
    pub pcs_config: PcsConfig,
    pub claim: CircuitClaim,
    pub interaction_pow_nonce: u64,
    pub interaction_claim: CircuitInteractionClaim,
    pub components: Vec<Box<dyn Component>>,
    pub stark_proof: Result<ExtendedStarkProof<Blake2sM31MerkleHasher>, ProvingError>,
    pub channel_salt: u32,
}

#[cfg(test)]
#[path = "prover_test.rs"]
pub mod test;

#[cfg(test)]
#[path = "recursive_circuits_tests.rs"]
pub mod recursive_circuits_tests;

pub fn to_component_provers(
    components: &CircuitComponents,
) -> Vec<&dyn ComponentProver<SimdBackend>> {
    chain!([
        &components.eq as &dyn ComponentProver<SimdBackend>,
        &components.qm31_ops as &dyn ComponentProver<SimdBackend>,
        &components.blake_gate as &dyn ComponentProver<SimdBackend>,
        &components.blake_round as &dyn ComponentProver<SimdBackend>,
        &components.blake_round_sigma as &dyn ComponentProver<SimdBackend>,
        &components.blake_g as &dyn ComponentProver<SimdBackend>,
        &components.blake_output as &dyn ComponentProver<SimdBackend>,
        &components.triple_xor_32 as &dyn ComponentProver<SimdBackend>,
        &components.verify_bitwise_xor_8 as &dyn ComponentProver<SimdBackend>,
        &components.verify_bitwise_xor_12 as &dyn ComponentProver<SimdBackend>,
        &components.verify_bitwise_xor_4 as &dyn ComponentProver<SimdBackend>,
        &components.verify_bitwise_xor_7 as &dyn ComponentProver<SimdBackend>,
        &components.verify_bitwise_xor_9 as &dyn ComponentProver<SimdBackend>,
        &components.range_check_15 as &dyn ComponentProver<SimdBackend>,
        &components.range_check_16 as &dyn ComponentProver<SimdBackend>,
    ])
    .collect()
}

pub fn prove_circuit(context: &mut Context<QM31>) -> CircuitProof {
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(context);
    prove_circuit_assignment(
        context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
    )
}

pub fn prove_circuit_assignment(
    values: &[QM31],
    preprocessed_circuit: &PreprocessedCircuit,
    base_column_pool: &BaseColumnPool<SimdBackend>,
) -> CircuitProof {
    let trace_log_size = preprocessed_circuit.params.trace_log_size;
    let mut pcs_config = PcsConfig::default();
    let lifting_log_size = trace_log_size + pcs_config.fri_config.log_blowup_factor;
    pcs_config.lifting_log_size = Some(lifting_log_size);

    // Precompute twiddles.
    // Account for blowup factor and for composition polynomial calculation (taking the max since
    // the composition polynomial is split prior to LDE).
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            trace_log_size
                + std::cmp::max(
                    pcs_config.fri_config.log_blowup_factor,
                    COMPOSITION_POLYNOMIAL_LOG_DEGREE_BOUND,
                ),
        )
        .circle_domain()
        .half_coset,
    );

    let preprocessed_trace = preprocessed_circuit.preprocessed_trace.get_trace::<SimdBackend>();
    let preprocessed_trace_polys = SimdBackend::interpolate_columns(preprocessed_trace, &twiddles);

    let store_polynomials_coefficients = true;
    let preprocessed_tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        preprocessed_trace_polys,
        pcs_config.fri_config.log_blowup_factor,
        &twiddles,
        store_polynomials_coefficients,
        pcs_config.lifting_log_size,
        base_column_pool,
    );

    prove_circuit_with_precompute(
        base_column_pool,
        &twiddles,
        preprocessed_circuit,
        MaybeOwned::Owned(preprocessed_tree),
        values,
        pcs_config,
    )
}

pub fn prove_circuit_with_precompute<'a>(
    base_column_pool: &BaseColumnPool<SimdBackend>,
    twiddles: &TwiddleTree<SimdBackend>,
    preprocessed_circuit: &PreprocessedCircuit,
    preprocessed_tree: MaybeOwned<'a, CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>>,
    values: &[QM31],
    pcs_config: PcsConfig,
) -> CircuitProof {
    let PreprocessedCircuit { preprocessed_trace, params } = preprocessed_circuit;
    let CircuitParams { first_permutation_row, n_blake_gates, output_addresses, .. } = params;
    let trace_generator = TraceGenerator {
        qm31_ops_trace_generator: Qm31OpsTraceGenerator {
            first_permutation_row: *first_permutation_row,
        },
    };

    // Setup protocol.
    let channel = &mut Blake2sM31Channel::default();

    // Mix channel salt. Note that we first reduce it modulo `M31::P`, then cast it as QM31.
    let channel_salt = 0_u32;
    channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(channel);
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sM31MerkleChannel>::with_memory_pool(
            pcs_config,
            twiddles,
            base_column_pool,
        );

    commitment_scheme.set_store_polynomials_coefficients();

    // Preprocessed trace.
    commitment_scheme.commit_tree(preprocessed_tree, channel);

    // Base trace.
    let mut tree_builder = commitment_scheme.tree_builder();
    let (claim, interaction_generator) = write_trace(
        values,
        preprocessed_trace.clone(),
        output_addresses,
        &mut tree_builder,
        &trace_generator,
    );
    claim.mix_into(channel);
    tree_builder.commit(channel);

    // Draw interaction elements.
    let interaction_pow_nonce = SimdBackend::grind(channel, INTERACTION_POW_BITS);
    channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(channel);

    // Interaction trace.
    let mut tree_builder = commitment_scheme.tree_builder();
    let interaction_claim = write_interaction_trace(
        &claim,
        interaction_generator,
        &mut tree_builder,
        &interaction_elements,
    );

    // Validate lookup argument.
    assert_eq!(
        lookup_sum(
            &claim,
            &interaction_claim,
            &interaction_elements,
            output_addresses,
            *n_blake_gates
        ),
        QM31::zero()
    );

    interaction_claim.mix_into(channel);
    tree_builder.commit(channel);
    // Component provers.
    let circuit_components = CircuitComponents::new(
        &claim,
        &interaction_elements,
        &interaction_claim,
        &preprocessed_trace.ids(),
    );
    let components = to_component_provers(&circuit_components);

    // Prove stark.
    let proof = prove_ex::<SimdBackend, _>(&components, channel, commitment_scheme, true);
    CircuitProof {
        pcs_config,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components: circuit_components.components(),
        stark_proof: proof,
        channel_salt,
    }
}

pub fn preprare_circuit_proof_for_circuit_verifier(
    circuit_proof: CircuitProof,
    proof_config: &ProofConfig,
) -> (Proof<QM31>, CircuitPublicData) {
    let CircuitProof {
        pcs_config: _,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components: _,
        stark_proof,
        channel_salt,
    } = circuit_proof;
    assert!(stark_proof.is_ok());
    let stark_proof = stark_proof.unwrap();

    let public_data = CircuitPublicData { output_values: claim.output_values.clone() };

    let claim = Claim {
        packed_enable_bits: pack_enable_bits(
            &claim.log_sizes.iter().map(|log_size| *log_size > 0).collect_vec(),
        ),
        packed_component_log_sizes: pack_component_log_sizes(&claim.log_sizes),
        claimed_sums: interaction_claim.claimed_sums.to_vec(),
    };

    let proof = proof_from_stark_proof(
        &stark_proof,
        proof_config,
        claim,
        interaction_pow_nonce,
        channel_salt,
    );
    (proof, public_data)
}


pub fn verify_stwo_proof(preprocessed_circuit: &PreprocessedCircuit, circuit_proof: CircuitProof) {
    let CircuitProof {
        pcs_config,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components,
        stark_proof,
        channel_salt,
    } = circuit_proof;
    assert!(stark_proof.is_ok());
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
    println!("Claim: {claim:?}");
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
            preprocessed_circuit.params.n_blake_gates
        ),
        QM31::zero()
    );
}