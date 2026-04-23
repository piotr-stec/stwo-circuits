use std::fs::File;

use cairo_air::utils::binary_deserialize_from_file;
use circuit_air::statement::{CircuitStatement, all_circuit_components};
use circuit_air::verify::{
    CircuitConfig, CircuitPublicData, build_verification_circuit, verify_circuit,
};
use circuit_common::finalize::{add_zk_blinding, finalize_context};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_prover::prover::{
    BaseColumnPool, CircuitProof, SimdBackend, preprare_circuit_proof_for_circuit_verifier,
    prove_circuit, prove_circuit_assignment,
};
use circuits::blake::HashValue;
use circuits::context::Context;
use circuits::ivalue::{IValue, NoValue};
use circuits::stats::Stats;
use circuits_stark_verifier::proof::{ProofConfig, ProofInfo, empty_proof};
use itertools::Itertools;
use num_traits::Zero;
use stwo::core::fields::qm31::QM31;
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;

use crate::privacy::{
    PRIVACY_CAIRO_VERIFIER_CONSTS_HASH, PRIVACY_RECURSION_CIRCUIT_CONSTS_HASH,
    PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT, privacy_cairo_verifier_config, privacy_components,
};
use crate::test::{verify_cairo, verify_cairo_with_component_set};
use crate::utils::get_proof_file_path;
use crate::verify::build_cairo_verifier_circuit;

#[expect(dead_code)]
fn privacy_circuit_preprocessed_root() -> HashValue<QM31> {
    PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT.into()
}

/// Verifies with a circuit a proof of execution of another circuit.
///
/// If `preprocessed_root` is `None`, the verifier takes the preprocessed root from the input proof.
/// This is unsound and is only done to make testing easier.
fn verify_circuit_proof(
    preprocessed_circuit: &PreprocessedCircuit,
    circuit_proof: CircuitProof,
    preprocessed_root: Option<HashValue<QM31>>,
) -> Context<QM31> {
    let preprocessed_column_ids = preprocessed_circuit.preprocessed_trace.ids();
    let proof_config = ProofConfig::from_components(
        &all_circuit_components::<QM31>(),
        preprocessed_column_ids.len(),
        &circuit_proof.pcs_config,
        circuit_air::statement::INTERACTION_POW_BITS,
    );
    let mut circuit_config = CircuitConfig {
        config: circuit_proof.pcs_config,
        output_addresses: preprocessed_circuit.params.output_addresses.clone(),
        preprocessed_column_ids,
        preprocessed_root: HashValue(QM31::zero(), QM31::zero()),
    };
    let (proof, public_data) =
        preprare_circuit_proof_for_circuit_verifier(circuit_proof, &proof_config);
    circuit_config.preprocessed_root = preprocessed_root.unwrap_or(proof.preprocessed_root);
    verify_circuit(circuit_config, proof, public_data).unwrap()
}

/// Compares the topology of two contexts.
/// Note that the values are not compared.
fn compare_contexts_topology<Value: IValue, OtherValue: IValue>(
    context_a: &Context<Value>,
    context_b: &Context<OtherValue>,
) {
    // TODO(Gali): Consider comparing unused and maybe unused vars.
    assert_eq!(context_a.circuit, context_b.circuit);
    assert_eq!(context_a.stats, context_b.stats);
    assert_eq!(context_a.guessed_vars, context_b.guessed_vars);
    let constants_a = context_a.constants().iter().map(|(k, v)| (*k, v.idx)).collect_vec();
    let constants_b = context_b.constants().iter().map(|(k, v)| (*k, v.idx)).collect_vec();
    assert_eq!(constants_a, constants_b);
}

#[test]
fn test_verify_privacy() {
    let proof_path = get_proof_file_path("privacy");
    let proof_file = File::open(proof_path).unwrap();
    let cairo_proof = binary_deserialize_from_file(&proof_file).unwrap();

    // Verify the proof.
    let context = verify_cairo_with_component_set(&cairo_proof, privacy_components()).unwrap();

    // Build the verifier circuit via NoValue.
    let log_blowup_factor = 3;
    let const_config = privacy_cairo_verifier_config(log_blowup_factor);
    let novalue_context = build_cairo_verifier_circuit(&const_config);

    // Check that building the verifier circuit via NoValue produces the same topology.
    compare_contexts_topology(&context, &novalue_context);
}

#[test]
#[ignore = "Cairo not in use; blake circuit gate has no AIR support on feat/poseidon-instead-blake branch"]
fn test_verify_privacy_with_recursion() {
    let proof_path = get_proof_file_path("privacy");
    let proof_file = File::open(proof_path).unwrap();
    let cairo_proof = binary_deserialize_from_file(&proof_file).unwrap();

    let mut context = verify_cairo(&cairo_proof).unwrap();

    let trace_commitment = cairo_proof.extended_stark_proof.proof.commitments.0[1];
    add_zk_blinding(
        &mut context,
        trace_commitment.0,
        cairo_proof.extended_stark_proof.proof.config.fri_config.n_queries,
    );
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    // To test with a precomputed preprocessed root, change `None` to
    // `Some(privacy_circuit_preprocessed_root())`.
    verify_circuit_proof(&preprocessed, circuit_proof, None);
}

#[test]
#[ignore = "Cairo not in use; blake circuit gate has no AIR support on feat/poseidon-instead-blake branch"]
fn test_privacy_recursion_with_preprocessed_context() {
    // Build the verifier circuit via NoValue and preprocess it.
    let cairo_proof_log_blowup_factor = 3;
    let const_config = privacy_cairo_verifier_config(cairo_proof_log_blowup_factor);
    let mut novalue_context = build_cairo_verifier_circuit(&const_config);
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut novalue_context);

    // Verify the privacy proof to get a Context<QM31> with real values.
    let proof_path = get_proof_file_path("privacy");
    let proof_file = File::open(proof_path).unwrap();
    let cairo_proof = binary_deserialize_from_file(&proof_file).unwrap();
    let mut assignment_context =
        verify_cairo_with_component_set(&cairo_proof, privacy_components()).unwrap();

    // Prove via the assignment flow: finalize separately, then prove with pre-computed
    // preprocessed data.
    finalize_context(&mut assignment_context);
    let assignment_proof = prove_circuit_assignment(
        assignment_context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    assert!(assignment_proof.stark_proof.is_ok());

    // Prove via the full flow for comparison.
    let mut full_prove_context =
        verify_cairo_with_component_set(&cairo_proof, privacy_components()).unwrap();
    let full_proof = prove_circuit(&mut full_prove_context);
    assert!(full_proof.stark_proof.is_ok());

    // Verify both circuit proofs and compare the resulting verifier contexts.
    // TODO(Gali): Add verify fixed circuit
    // TODO(Leo): change `None` to `Some(privacy_circuit_preprocessed_root)` once the changes to the
    // circuit become less frequent.
    let assignment_verifier_context = verify_circuit_proof(&preprocessed, assignment_proof, None);

    let full_prove_preprocessed =
        PreprocessedCircuit::from_finalized_circuit(&full_prove_context.circuit);
    let full_verifier_context = verify_circuit_proof(&full_prove_preprocessed, full_proof, None);

    // Compare the verifier contexts.
    compare_contexts_topology(&assignment_verifier_context, &full_verifier_context);
    assert_eq!(assignment_verifier_context.values(), full_verifier_context.values());
}

#[test]
#[ignore = "Cairo not in use; PRIVACY_RECURSION_CIRCUIT_CONSTS_HASH is stale after switching from Blake to Poseidon gate"]
fn test_privacy_consts() {
    let cairo_proof_log_blowup_factor = 2;
    let const_config = privacy_cairo_verifier_config(cairo_proof_log_blowup_factor);
    let mut novalue_context = build_cairo_verifier_circuit(&const_config);
    let constants = novalue_context.constants().keys().cloned().collect_vec();
    let blake_value = QM31::blake(constants.as_slice(), constants.len() * 16);
    assert_eq!(blake_value, PRIVACY_CAIRO_VERIFIER_CONSTS_HASH.into());

    // Finalization should not add any new constants.
    finalize_context(&mut novalue_context);
    assert_eq!(novalue_context.constants().len(), constants.len());

    let preprocessed_circuit =
        PreprocessedCircuit::from_finalized_circuit(&novalue_context.circuit);

    let log_blowup_factor = 2;
    let lifting_log_size = preprocessed_circuit.params.trace_log_size + log_blowup_factor;
    let pcs_config = PcsConfig {
        pow_bits: 26,
        fri_config: FriConfig {
            log_blowup_factor,
            log_last_layer_degree_bound: 0,
            n_queries: 35,
            fold_step: 4,
        },
        lifting_log_size: Some(lifting_log_size),
    };
    let preprocessed_column_ids = preprocessed_circuit.preprocessed_trace.ids();
    let proof_config = ProofConfig::from_components(
        &all_circuit_components::<QM31>(),
        preprocessed_column_ids.len(),
        &pcs_config,
        circuit_air::statement::INTERACTION_POW_BITS,
    );
    let proof = empty_proof(&proof_config);
    let circuit_config = CircuitConfig {
        config: pcs_config,
        output_addresses: preprocessed_circuit.params.output_addresses.clone(),
        preprocessed_column_ids,
        preprocessed_root: PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT.into(),
    };
    let public_data = CircuitPublicData {
        output_values: vec![QM31::zero(); preprocessed_circuit.params.output_addresses.len()],
    };
    let mut verifier_context =
        build_verification_circuit(circuit_config, proof, public_data).unwrap();
    let constants = verifier_context.constants().keys().cloned().collect_vec();
    let blake_value = QM31::blake(constants.as_slice(), constants.len() * 16);
    assert_eq!(blake_value, PRIVACY_RECURSION_CIRCUIT_CONSTS_HASH.into());

    // Finalization should not add any new constants.
    finalize_context(&mut verifier_context);
    assert_eq!(verifier_context.constants().len(), constants.len());
}

#[test]
fn test_zk_padding() {
    // Build the verifier circuit via NoValue and preprocess it.
    for log_blowup_factor in 1..=3 {
        let const_config = privacy_cairo_verifier_config(log_blowup_factor);
        let mut context = build_cairo_verifier_circuit(&const_config);

        let Stats { equals: eq_before, add, sub, mul, div, pointwise_mul, .. } = context.stats;
        let qm31_ops_before = add
            + sub
            + mul
            + div
            + pointwise_mul
            + context
                .circuit
                .permutation
                .iter()
                .map(|p| p.inputs.len() + p.outputs.len())
                .sum::<usize>();

        add_zk_blinding(&mut context, [0; 32], const_config.proof_config.fri.n_queries);

        let Stats { equals: eq_after, add, sub, mul, div, pointwise_mul, .. } = context.stats;
        let qm31_ops_after = add
            + sub
            + mul
            + div
            + pointwise_mul
            + context
                .circuit
                .permutation
                .iter()
                .map(|p| p.inputs.len() + p.outputs.len())
                .sum::<usize>();

        assert_eq!(eq_after.next_power_of_two(), eq_before.next_power_of_two());
        assert_eq!(qm31_ops_after.next_power_of_two(), qm31_ops_before.next_power_of_two());
    }
}

#[test]
#[ignore = "Cairo not in use; hardcoded proof size is stale after switching from Blake to Poseidon gate"]
fn test_privacy_proof_info() {
    let cairo_proof_log_blowup_factor = 3;
    let const_config = privacy_cairo_verifier_config(cairo_proof_log_blowup_factor);

    let mut novalue_context = build_cairo_verifier_circuit(&const_config);
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut novalue_context);

    let log_blowup_factor = 2;
    let lifting_log_size = preprocessed_circuit.params.trace_log_size + log_blowup_factor;
    let pcs_config = PcsConfig {
        pow_bits: 26,
        fri_config: FriConfig {
            log_blowup_factor,
            log_last_layer_degree_bound: 0,
            n_queries: 35,
            fold_step: 4,
        },
        lifting_log_size: Some(lifting_log_size),
    };
    let preprocessed_column_ids = preprocessed_circuit.preprocessed_trace.ids();
    let circuit_config = CircuitConfig {
        config: pcs_config,
        output_addresses: preprocessed_circuit.params.output_addresses.clone(),
        preprocessed_column_ids,
        preprocessed_root: PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT.into(),
    };
    let public_data = CircuitPublicData {
        output_values: vec![QM31::zero(); preprocessed_circuit.params.output_addresses.len()],
    };
    let mut context = Context::<NoValue>::default();
    let statement = CircuitStatement::new(
        &mut context,
        &circuit_config.output_addresses,
        &public_data.output_values,
        circuit_config.preprocessed_column_ids.clone(),
        circuit_config.preprocessed_root,
    );

    let proof_config = ProofConfig::from_statement(
        &statement,
        &circuit_config.config,
        circuit_air::statement::INTERACTION_POW_BITS,
    );
    let proof_info = ProofInfo::from_config(&proof_config);
    println!("{proof_info}");
    assert_eq!(proof_info.total(), 86205);
}
