use std::sync::Arc;

use crate::witness::components::blake_g;
use crate::witness::components::blake_gate;
use crate::witness::components::blake_output;
use crate::witness::components::blake_round;
use crate::witness::components::blake_round_sigma;
use crate::witness::components::eq;
use crate::witness::components::qm31_ops;
use crate::witness::components::range_check_15;
use crate::witness::components::range_check_16;
use crate::witness::components::triple_xor_32;
use crate::witness::components::verify_bitwise_xor_4;
use crate::witness::components::verify_bitwise_xor_7;
use crate::witness::components::verify_bitwise_xor_8;
use crate::witness::components::verify_bitwise_xor_9;
use crate::witness::components::verify_bitwise_xor_12;
use circuit_air::CircuitClaim;
use circuit_air::CircuitInteractionClaim;
use circuit_air::CircuitInteractionElements;
use circuit_common::Qm31OpsTraceGenerator;
use circuit_common::preprocessed::PreProcessedTrace;
use itertools::Itertools;
use rayon::join;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::core::vcs_lifted::keccak_merkle::KeccakMerkleChannel;
use stwo::prover::TreeBuilder;
use stwo::prover::backend::simd::SimdBackend;

pub struct TraceGenerator {
    pub qm31_ops_trace_generator: Qm31OpsTraceGenerator,
}

pub fn write_trace(
    context_values: &[QM31],
    preprocessed_trace: Arc<PreProcessedTrace>,
    output_addresses: &[usize],
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, Blake2sM31MerkleChannel>,
    trace_generator: &TraceGenerator,
) -> (CircuitClaim, CircuitInteractionClaimGenerator) {
    let preprocessed_trace_ref = preprocessed_trace.as_ref();

    let (
        (
            (eq_trace, eq_log_size, eq_lookup_data),
            (qm31_ops_trace, qm31_ops_log_size, qm31_ops_lookup_data),
        ),
        (
            verify_bitwise_xor_8_state,
            verify_bitwise_xor_12_state,
            verify_bitwise_xor_4_state,
            verify_bitwise_xor_7_state,
            verify_bitwise_xor_9_state,
            range_check_16_state,
            range_check_15_state,
            mut triple_xor_32_state,
            blake_gate_claim_generator,
            mut blake_round_generator,
            blake_round_sigma_generator,
            mut blake_g_generator,
        ),
    ) = join(
        || {
            join(
                || eq::write_trace(context_values, preprocessed_trace_ref),
                || {
                    qm31_ops::write_trace(
                        context_values,
                        preprocessed_trace_ref,
                        &trace_generator.qm31_ops_trace_generator,
                    )
                },
            )
        },
        || {
            std::thread::scope(|s| {
                let verify_bitwise_xor_8_handle = s.spawn(|| {
                    verify_bitwise_xor_8::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_12_handle = s.spawn(|| {
                    verify_bitwise_xor_12::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_4_handle = s.spawn(|| {
                    verify_bitwise_xor_4::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_7_handle = s.spawn(|| {
                    verify_bitwise_xor_7::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_9_handle = s.spawn(|| {
                    verify_bitwise_xor_9::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let range_check_16_handle =
                    s.spawn(|| range_check_16::ClaimGenerator::new(preprocessed_trace.clone()));
                let range_check_15_handle =
                    s.spawn(|| range_check_15::ClaimGenerator::new(preprocessed_trace.clone()));
                let triple_xor_32_handle = s.spawn(triple_xor_32::ClaimGenerator::new);
                let blake_gate_handle =
                    s.spawn(|| blake_gate::ClaimGenerator::new(preprocessed_trace.clone()));
                let blake_round_handle = s.spawn(blake_round::ClaimGenerator::default);
                let blake_round_sigma_handle =
                    s.spawn(|| blake_round_sigma::ClaimGenerator::new(preprocessed_trace.clone()));
                let blake_g_handle = s.spawn(blake_g::ClaimGenerator::new);

                (
                    verify_bitwise_xor_8_handle
                        .join()
                        .expect("verify_bitwise_xor_8 init task failed"),
                    verify_bitwise_xor_12_handle
                        .join()
                        .expect("verify_bitwise_xor_12 init task failed"),
                    verify_bitwise_xor_4_handle
                        .join()
                        .expect("verify_bitwise_xor_4 init task failed"),
                    verify_bitwise_xor_7_handle
                        .join()
                        .expect("verify_bitwise_xor_7 init task failed"),
                    verify_bitwise_xor_9_handle
                        .join()
                        .expect("verify_bitwise_xor_9 init task failed"),
                    range_check_16_handle.join().expect("range_check_16 init task failed"),
                    range_check_15_handle.join().expect("range_check_15 init task failed"),
                    triple_xor_32_handle.join().expect("triple_xor_32 init task failed"),
                    blake_gate_handle.join().expect("blake_gate init task failed"),
                    blake_round_handle.join().expect("blake_round init task failed"),
                    blake_round_sigma_handle.join().expect("blake_round_sigma init task failed"),
                    blake_g_handle.join().expect("blake_g init task failed"),
                )
            })
        },
    );
    let mut trace_evals = eq_trace.to_evals();
    trace_evals.extend(qm31_ops_trace.to_evals());

    // Write blake gate component.
    let (
        blake_gate_trace,
        blake_gate_interaction_claim_gen,
        blake_message_state,
        blake_output_component_input,
    ) = blake_gate_claim_generator.write_trace(
        context_values,
        preprocessed_trace_ref,
        &verify_bitwise_xor_8_state,
        &range_check_16_state,
        &range_check_15_state,
        &mut blake_round_generator,
        &mut triple_xor_32_state,
    );
    trace_evals.extend(blake_gate_trace.to_evals());

    // Write blake round component.
    let (blake_round_trace, blake_round_log_size, blake_round_interaction_claim_gen) =
        blake_round_generator.write_trace(
            &blake_round_sigma_generator,
            &blake_message_state,
            &mut blake_g_generator,
        );
    trace_evals.extend(blake_round_trace.to_evals());

    // Write blake round sigma component.
    let (
        blake_round_sigma_trace,
        _blake_round_sigma_claim,
        blake_round_sigma_interaction_claim_gen,
    ) = blake_round_sigma_generator.write_trace();
    trace_evals.extend(blake_round_sigma_trace.to_evals());

    // Write blake g, blake output, and triple xor 32 components in parallel.
    let blake_output_generator =
        blake_output::ClaimGenerator::new(blake_output_component_input, preprocessed_trace);
    let (
        (blake_g_trace, blake_g_claim, blake_g_interaction_claim_gen),
        (
            (blake_output_trace, blake_output_claim, blake_output_interaction_claim_gen),
            (triple_xor_32_trace, triple_xor_32_claim, triple_xor_32_interaction_claim_gen),
        ),
    ) = join(
        || {
            blake_g_generator.write_trace(
                &verify_bitwise_xor_8_state,
                &verify_bitwise_xor_12_state,
                &verify_bitwise_xor_4_state,
                &verify_bitwise_xor_7_state,
                &verify_bitwise_xor_9_state,
            )
        },
        || {
            join(
                || blake_output_generator.write_trace(),
                || triple_xor_32_state.write_trace(&verify_bitwise_xor_8_state),
            )
        },
    );
    trace_evals.extend(blake_g_trace.to_evals());
    trace_evals.extend(blake_output_trace.to_evals());
    trace_evals.extend(triple_xor_32_trace.to_evals());

    // Write xor and range-check components in parallel.
    let (
        verify_bitwise_xor_8_result,
        verify_bitwise_xor_12_result,
        verify_bitwise_xor_4_result,
        verify_bitwise_xor_7_result,
        verify_bitwise_xor_9_result,
        range_check_15_result,
        range_check_16_result,
    ) = std::thread::scope(|s| {
        let verify_bitwise_xor_8_handle = s.spawn(move || verify_bitwise_xor_8_state.write_trace());
        let verify_bitwise_xor_12_handle =
            s.spawn(move || verify_bitwise_xor_12_state.write_trace());
        let verify_bitwise_xor_4_handle = s.spawn(move || verify_bitwise_xor_4_state.write_trace());
        let verify_bitwise_xor_7_handle = s.spawn(move || verify_bitwise_xor_7_state.write_trace());
        let verify_bitwise_xor_9_handle = s.spawn(move || verify_bitwise_xor_9_state.write_trace());
        let range_check_15_handle = s.spawn(move || range_check_15_state.write_trace());
        let range_check_16_handle = s.spawn(move || range_check_16_state.write_trace());

        (
            verify_bitwise_xor_8_handle.join().expect("verify_bitwise_xor_8 trace task failed"),
            verify_bitwise_xor_12_handle.join().expect("verify_bitwise_xor_12 trace task failed"),
            verify_bitwise_xor_4_handle.join().expect("verify_bitwise_xor_4 trace task failed"),
            verify_bitwise_xor_7_handle.join().expect("verify_bitwise_xor_7 trace task failed"),
            verify_bitwise_xor_9_handle.join().expect("verify_bitwise_xor_9 trace task failed"),
            range_check_15_handle.join().expect("range_check_15 trace task failed"),
            range_check_16_handle.join().expect("range_check_16 trace task failed"),
        )
    });

    let (
        verify_bitwise_xor_8_trace,
        _verify_bitwise_xor_8_claim,
        verify_bitwise_xor_8_interaction_claim_gen,
    ) = verify_bitwise_xor_8_result;
    trace_evals.extend(verify_bitwise_xor_8_trace.to_evals());

    let (
        verify_bitwise_xor_12_trace,
        _verify_bitwise_xor_12_claim,
        verify_bitwise_xor_12_interaction_claim_gen,
    ) = verify_bitwise_xor_12_result;
    trace_evals.extend(verify_bitwise_xor_12_trace);

    let (
        verify_bitwise_xor_4_trace,
        _verify_bitwise_xor_4_claim,
        verify_bitwise_xor_4_interaction_claim_gen,
    ) = verify_bitwise_xor_4_result;
    trace_evals.extend(verify_bitwise_xor_4_trace.to_evals());

    let (
        verify_bitwise_xor_7_trace,
        _verify_bitwise_xor_7_claim,
        verify_bitwise_xor_7_interaction_claim_gen,
    ) = verify_bitwise_xor_7_result;
    trace_evals.extend(verify_bitwise_xor_7_trace.to_evals());

    let (
        verify_bitwise_xor_9_trace,
        _verify_bitwise_xor_9_claim,
        verify_bitwise_xor_9_interaction_claim_gen,
    ) = verify_bitwise_xor_9_result;
    trace_evals.extend(verify_bitwise_xor_9_trace.to_evals());

    let (range_check_15_trace, _range_check_15_claim, range_check_15_interaction_claim_gen) =
        range_check_15_result;
    trace_evals.extend(range_check_15_trace.to_evals());

    let (range_check_16_trace, _range_check_16_claim, range_check_16_interaction_claim_gen) =
        range_check_16_result;
    trace_evals.extend(range_check_16_trace.to_evals());

    tree_builder.extend_evals(trace_evals);

    let output_values = output_addresses.iter().map(|addr| context_values[*addr]).collect_vec();

    (
        CircuitClaim {
            log_sizes: [
                eq_log_size,
                qm31_ops_log_size,
                blake_gate_interaction_claim_gen.log_size,
                blake_round_log_size.log_size,
                circuit_air::components::blake_round_sigma::LOG_SIZE,
                blake_g_claim.log_size,
                blake_output_claim.log_size,
                triple_xor_32_claim.log_size,
                circuit_air::components::verify_bitwise_xor_8::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_12::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_4::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_7::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_9::LOG_SIZE,
                circuit_air::components::range_check_15::LOG_SIZE,
                circuit_air::components::range_check_16::LOG_SIZE,
            ],
            output_values,
        },
        CircuitInteractionClaimGenerator {
            eq_lookup_data,
            qm31_ops_lookup_data,
            blake_gate: blake_gate_interaction_claim_gen,
            blake_round: blake_round_interaction_claim_gen,
            blake_round_sigma: blake_round_sigma_interaction_claim_gen,
            blake_g: blake_g_interaction_claim_gen,
            blake_output: blake_output_interaction_claim_gen,
            triple_xor_32: triple_xor_32_interaction_claim_gen,
            verify_bitwise_xor_8: verify_bitwise_xor_8_interaction_claim_gen,
            verify_bitwise_xor_12: verify_bitwise_xor_12_interaction_claim_gen,
            verify_bitwise_xor_4: verify_bitwise_xor_4_interaction_claim_gen,
            verify_bitwise_xor_7: verify_bitwise_xor_7_interaction_claim_gen,
            verify_bitwise_xor_9: verify_bitwise_xor_9_interaction_claim_gen,
            range_check_15: range_check_15_interaction_claim_gen,
            range_check_16: range_check_16_interaction_claim_gen,
        },
    )
}

pub fn write_trace_keccak(
    context_values: &[QM31],
    preprocessed_trace: Arc<PreProcessedTrace>,
    output_addresses: &[usize],
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, KeccakMerkleChannel>,
    trace_generator: &TraceGenerator,
) -> (CircuitClaim, CircuitInteractionClaimGenerator) {
    let preprocessed_trace_ref = preprocessed_trace.as_ref();

    let (
        (
            (eq_trace, eq_log_size, eq_lookup_data),
            (qm31_ops_trace, qm31_ops_log_size, qm31_ops_lookup_data),
        ),
        (
            verify_bitwise_xor_8_state,
            verify_bitwise_xor_12_state,
            verify_bitwise_xor_4_state,
            verify_bitwise_xor_7_state,
            verify_bitwise_xor_9_state,
            range_check_16_state,
            range_check_15_state,
            mut triple_xor_32_state,
            blake_gate_claim_generator,
            mut blake_round_generator,
            blake_round_sigma_generator,
            mut blake_g_generator,
        ),
    ) = join(
        || {
            join(
                || eq::write_trace(context_values, preprocessed_trace_ref),
                || {
                    qm31_ops::write_trace(
                        context_values,
                        preprocessed_trace_ref,
                        &trace_generator.qm31_ops_trace_generator,
                    )
                },
            )
        },
        || {
            std::thread::scope(|s| {
                let verify_bitwise_xor_8_handle = s.spawn(|| {
                    verify_bitwise_xor_8::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_12_handle = s.spawn(|| {
                    verify_bitwise_xor_12::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_4_handle = s.spawn(|| {
                    verify_bitwise_xor_4::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_7_handle = s.spawn(|| {
                    verify_bitwise_xor_7::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let verify_bitwise_xor_9_handle = s.spawn(|| {
                    verify_bitwise_xor_9::ClaimGenerator::new(preprocessed_trace.clone())
                });
                let range_check_16_handle =
                    s.spawn(|| range_check_16::ClaimGenerator::new(preprocessed_trace.clone()));
                let range_check_15_handle =
                    s.spawn(|| range_check_15::ClaimGenerator::new(preprocessed_trace.clone()));
                let triple_xor_32_handle = s.spawn(triple_xor_32::ClaimGenerator::new);
                let blake_gate_handle =
                    s.spawn(|| blake_gate::ClaimGenerator::new(preprocessed_trace.clone()));
                let blake_round_handle = s.spawn(blake_round::ClaimGenerator::default);
                let blake_round_sigma_handle =
                    s.spawn(|| blake_round_sigma::ClaimGenerator::new(preprocessed_trace.clone()));
                let blake_g_handle = s.spawn(blake_g::ClaimGenerator::new);

                (
                    verify_bitwise_xor_8_handle
                        .join()
                        .expect("verify_bitwise_xor_8 init task failed"),
                    verify_bitwise_xor_12_handle
                        .join()
                        .expect("verify_bitwise_xor_12 init task failed"),
                    verify_bitwise_xor_4_handle
                        .join()
                        .expect("verify_bitwise_xor_4 init task failed"),
                    verify_bitwise_xor_7_handle
                        .join()
                        .expect("verify_bitwise_xor_7 init task failed"),
                    verify_bitwise_xor_9_handle
                        .join()
                        .expect("verify_bitwise_xor_9 init task failed"),
                    range_check_16_handle.join().expect("range_check_16 init task failed"),
                    range_check_15_handle.join().expect("range_check_15 init task failed"),
                    triple_xor_32_handle.join().expect("triple_xor_32 init task failed"),
                    blake_gate_handle.join().expect("blake_gate init task failed"),
                    blake_round_handle.join().expect("blake_round init task failed"),
                    blake_round_sigma_handle.join().expect("blake_round_sigma init task failed"),
                    blake_g_handle.join().expect("blake_g init task failed"),
                )
            })
        },
    );
    let mut trace_evals = eq_trace.to_evals();
    trace_evals.extend(qm31_ops_trace.to_evals());

    // Write blake gate component.
    let (
        blake_gate_trace,
        blake_gate_interaction_claim_gen,
        blake_message_state,
        blake_output_component_input,
    ) = blake_gate_claim_generator.write_trace(
        context_values,
        preprocessed_trace_ref,
        &verify_bitwise_xor_8_state,
        &range_check_16_state,
        &range_check_15_state,
        &mut blake_round_generator,
        &mut triple_xor_32_state,
    );
    trace_evals.extend(blake_gate_trace.to_evals());

    // Write blake round component.
    let (blake_round_trace, blake_round_log_size, blake_round_interaction_claim_gen) =
        blake_round_generator.write_trace(
            &blake_round_sigma_generator,
            &blake_message_state,
            &mut blake_g_generator,
        );
    trace_evals.extend(blake_round_trace.to_evals());

    // Write blake round sigma component.
    let (
        blake_round_sigma_trace,
        _blake_round_sigma_claim,
        blake_round_sigma_interaction_claim_gen,
    ) = blake_round_sigma_generator.write_trace();
    trace_evals.extend(blake_round_sigma_trace.to_evals());

    // Write blake g, blake output, and triple xor 32 components in parallel.
    let blake_output_generator =
        blake_output::ClaimGenerator::new(blake_output_component_input, preprocessed_trace);
    let (
        (blake_g_trace, blake_g_claim, blake_g_interaction_claim_gen),
        (
            (blake_output_trace, blake_output_claim, blake_output_interaction_claim_gen),
            (triple_xor_32_trace, triple_xor_32_claim, triple_xor_32_interaction_claim_gen),
        ),
    ) = join(
        || {
            blake_g_generator.write_trace(
                &verify_bitwise_xor_8_state,
                &verify_bitwise_xor_12_state,
                &verify_bitwise_xor_4_state,
                &verify_bitwise_xor_7_state,
                &verify_bitwise_xor_9_state,
            )
        },
        || {
            join(
                || blake_output_generator.write_trace(),
                || triple_xor_32_state.write_trace(&verify_bitwise_xor_8_state),
            )
        },
    );
    trace_evals.extend(blake_g_trace.to_evals());
    trace_evals.extend(blake_output_trace.to_evals());
    trace_evals.extend(triple_xor_32_trace.to_evals());

    // Write xor and range-check components in parallel.
    let (
        verify_bitwise_xor_8_result,
        verify_bitwise_xor_12_result,
        verify_bitwise_xor_4_result,
        verify_bitwise_xor_7_result,
        verify_bitwise_xor_9_result,
        range_check_15_result,
        range_check_16_result,
    ) = std::thread::scope(|s| {
        let verify_bitwise_xor_8_handle = s.spawn(move || verify_bitwise_xor_8_state.write_trace());
        let verify_bitwise_xor_12_handle =
            s.spawn(move || verify_bitwise_xor_12_state.write_trace());
        let verify_bitwise_xor_4_handle = s.spawn(move || verify_bitwise_xor_4_state.write_trace());
        let verify_bitwise_xor_7_handle = s.spawn(move || verify_bitwise_xor_7_state.write_trace());
        let verify_bitwise_xor_9_handle = s.spawn(move || verify_bitwise_xor_9_state.write_trace());
        let range_check_15_handle = s.spawn(move || range_check_15_state.write_trace());
        let range_check_16_handle = s.spawn(move || range_check_16_state.write_trace());

        (
            verify_bitwise_xor_8_handle.join().expect("verify_bitwise_xor_8 trace task failed"),
            verify_bitwise_xor_12_handle.join().expect("verify_bitwise_xor_12 trace task failed"),
            verify_bitwise_xor_4_handle.join().expect("verify_bitwise_xor_4 trace task failed"),
            verify_bitwise_xor_7_handle.join().expect("verify_bitwise_xor_7 trace task failed"),
            verify_bitwise_xor_9_handle.join().expect("verify_bitwise_xor_9 trace task failed"),
            range_check_15_handle.join().expect("range_check_15 trace task failed"),
            range_check_16_handle.join().expect("range_check_16 trace task failed"),
        )
    });

    let (
        verify_bitwise_xor_8_trace,
        _verify_bitwise_xor_8_claim,
        verify_bitwise_xor_8_interaction_claim_gen,
    ) = verify_bitwise_xor_8_result;
    trace_evals.extend(verify_bitwise_xor_8_trace.to_evals());

    let (
        verify_bitwise_xor_12_trace,
        _verify_bitwise_xor_12_claim,
        verify_bitwise_xor_12_interaction_claim_gen,
    ) = verify_bitwise_xor_12_result;
    trace_evals.extend(verify_bitwise_xor_12_trace);

    let (
        verify_bitwise_xor_4_trace,
        _verify_bitwise_xor_4_claim,
        verify_bitwise_xor_4_interaction_claim_gen,
    ) = verify_bitwise_xor_4_result;
    trace_evals.extend(verify_bitwise_xor_4_trace.to_evals());

    let (
        verify_bitwise_xor_7_trace,
        _verify_bitwise_xor_7_claim,
        verify_bitwise_xor_7_interaction_claim_gen,
    ) = verify_bitwise_xor_7_result;
    trace_evals.extend(verify_bitwise_xor_7_trace.to_evals());

    let (
        verify_bitwise_xor_9_trace,
        _verify_bitwise_xor_9_claim,
        verify_bitwise_xor_9_interaction_claim_gen,
    ) = verify_bitwise_xor_9_result;
    trace_evals.extend(verify_bitwise_xor_9_trace.to_evals());

    let (range_check_15_trace, _range_check_15_claim, range_check_15_interaction_claim_gen) =
        range_check_15_result;
    trace_evals.extend(range_check_15_trace.to_evals());

    let (range_check_16_trace, _range_check_16_claim, range_check_16_interaction_claim_gen) =
        range_check_16_result;
    trace_evals.extend(range_check_16_trace.to_evals());

    tree_builder.extend_evals(trace_evals);

    let output_values = output_addresses.iter().map(|addr| context_values[*addr]).collect_vec();

    (
        CircuitClaim {
            log_sizes: [
                eq_log_size,
                qm31_ops_log_size,
                blake_gate_interaction_claim_gen.log_size,
                blake_round_log_size.log_size,
                circuit_air::components::blake_round_sigma::LOG_SIZE,
                blake_g_claim.log_size,
                blake_output_claim.log_size,
                triple_xor_32_claim.log_size,
                circuit_air::components::verify_bitwise_xor_8::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_12::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_4::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_7::LOG_SIZE,
                circuit_air::components::verify_bitwise_xor_9::LOG_SIZE,
                circuit_air::components::range_check_15::LOG_SIZE,
                circuit_air::components::range_check_16::LOG_SIZE,
            ],
            output_values,
        },
        CircuitInteractionClaimGenerator {
            eq_lookup_data,
            qm31_ops_lookup_data,
            blake_gate: blake_gate_interaction_claim_gen,
            blake_round: blake_round_interaction_claim_gen,
            blake_round_sigma: blake_round_sigma_interaction_claim_gen,
            blake_g: blake_g_interaction_claim_gen,
            blake_output: blake_output_interaction_claim_gen,
            triple_xor_32: triple_xor_32_interaction_claim_gen,
            verify_bitwise_xor_8: verify_bitwise_xor_8_interaction_claim_gen,
            verify_bitwise_xor_12: verify_bitwise_xor_12_interaction_claim_gen,
            verify_bitwise_xor_4: verify_bitwise_xor_4_interaction_claim_gen,
            verify_bitwise_xor_7: verify_bitwise_xor_7_interaction_claim_gen,
            verify_bitwise_xor_9: verify_bitwise_xor_9_interaction_claim_gen,
            range_check_15: range_check_15_interaction_claim_gen,
            range_check_16: range_check_16_interaction_claim_gen,
        },
    )
}

pub struct CircuitInteractionClaimGenerator {
    pub eq_lookup_data: eq::LookupData,
    pub qm31_ops_lookup_data: qm31_ops::LookupData,
    pub blake_gate: blake_gate::InteractionClaimGenerator,
    pub blake_round: blake_round::InteractionClaimGenerator,
    pub blake_round_sigma: blake_round_sigma::InteractionClaimGenerator,
    pub blake_g: blake_g::InteractionClaimGenerator,
    pub blake_output: blake_output::InteractionClaimGenerator,
    pub triple_xor_32: triple_xor_32::InteractionClaimGenerator,
    pub verify_bitwise_xor_8: verify_bitwise_xor_8::InteractionClaimGenerator,
    pub verify_bitwise_xor_12: verify_bitwise_xor_12::InteractionClaimGenerator,
    pub verify_bitwise_xor_4: verify_bitwise_xor_4::InteractionClaimGenerator,
    pub verify_bitwise_xor_7: verify_bitwise_xor_7::InteractionClaimGenerator,
    pub verify_bitwise_xor_9: verify_bitwise_xor_9::InteractionClaimGenerator,
    pub range_check_15: range_check_15::InteractionClaimGenerator,
    pub range_check_16: range_check_16::InteractionClaimGenerator,
}

pub fn write_interaction_trace(
    circuit_claim: &CircuitClaim,
    circuit_interaction_claim_generator: CircuitInteractionClaimGenerator,
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, Blake2sM31MerkleChannel>,
    interaction_elements: &CircuitInteractionElements,
) -> CircuitInteractionClaim {
    let CircuitClaim { log_sizes, output_values: _ } = circuit_claim;
    let mut component_log_size_iter = log_sizes.iter();

    let (eq_trace, eq_claimed_sum) = eq::write_interaction_trace(
        *component_log_size_iter.next().unwrap(),
        circuit_interaction_claim_generator.eq_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(eq_trace);
    let (qm31_ops_trace, qm31_ops_claimed_sum) = qm31_ops::write_interaction_trace(
        *component_log_size_iter.next().unwrap(),
        circuit_interaction_claim_generator.qm31_ops_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(qm31_ops_trace);

    // Write blake gate interaction trace.
    let (blake_gate_trace, blake_gate_interaction_claim) = circuit_interaction_claim_generator
        .blake_gate
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_gate_trace);

    // Write blake round interaction trace.
    let (blake_round_trace, blake_round_interaction_claim) = circuit_interaction_claim_generator
        .blake_round
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_round_trace);

    // Write blake round sigma interaction trace.
    let (blake_round_sigma_trace, blake_round_sigma_interaction_claim) =
        circuit_interaction_claim_generator
            .blake_round_sigma
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_round_sigma_trace);

    // Write blake g interaction trace.
    let (blake_g_trace, blake_g_interaction_claim) = circuit_interaction_claim_generator
        .blake_g
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_g_trace);

    // Write blake output interaction trace.
    let (blake_output_trace, blake_output_interaction_claim) = circuit_interaction_claim_generator
        .blake_output
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_output_trace);

    // Write triple xor 32 interaction trace.
    let (triple_xor_32_trace, triple_xor_32_interaction_claim) =
        circuit_interaction_claim_generator
            .triple_xor_32
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(triple_xor_32_trace);

    // Write verify bitwise xor 8 interaction trace.
    let (verify_bitwise_xor_8_trace, verify_bitwise_xor_8_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_8
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_8_trace);
    let (verify_bitwise_xor_12_trace, verify_bitwise_xor_12_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_12
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_12_trace);

    // Write verify bitwise xor 4 interaction trace.
    let (verify_bitwise_xor_4_trace, verify_bitwise_xor_4_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_4
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_4_trace);

    // Write verify bitwise xor 7 interaction trace.
    let (verify_bitwise_xor_7_trace, verify_bitwise_xor_7_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_7
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_7_trace);

    // Write verify bitwise xor 9 interaction trace.
    let (verify_bitwise_xor_9_trace, verify_bitwise_xor_9_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_9
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_9_trace);

    // Write range check 15 interaction trace.
    let (range_check_15_trace, range_check_15_interaction_claim) =
        circuit_interaction_claim_generator
            .range_check_15
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(range_check_15_trace);

    // Write range check 16 interaction trace.
    let (range_check_16_trace, range_check_16_interaction_claim) =
        circuit_interaction_claim_generator
            .range_check_16
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(range_check_16_trace);

    CircuitInteractionClaim {
        claimed_sums: [
            eq_claimed_sum,
            qm31_ops_claimed_sum,
            blake_gate_interaction_claim.claimed_sum,
            blake_round_interaction_claim.claimed_sum,
            blake_round_sigma_interaction_claim.claimed_sum,
            blake_g_interaction_claim.claimed_sum,
            blake_output_interaction_claim.claimed_sum,
            triple_xor_32_interaction_claim.claimed_sum,
            verify_bitwise_xor_8_interaction_claim.claimed_sum,
            verify_bitwise_xor_12_interaction_claim.claimed_sum,
            verify_bitwise_xor_4_interaction_claim.claimed_sum,
            verify_bitwise_xor_7_interaction_claim.claimed_sum,
            verify_bitwise_xor_9_interaction_claim.claimed_sum,
            range_check_15_interaction_claim.claimed_sum,
            range_check_16_interaction_claim.claimed_sum,
        ],
    }
}


pub fn write_interaction_trace_keccak(
    circuit_claim: &CircuitClaim,
    circuit_interaction_claim_generator: CircuitInteractionClaimGenerator,
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, KeccakMerkleChannel>,
    interaction_elements: &CircuitInteractionElements,
) -> CircuitInteractionClaim {
    let CircuitClaim { log_sizes, output_values: _ } = circuit_claim;
    let mut component_log_size_iter = log_sizes.iter();

    let (eq_trace, eq_claimed_sum) = eq::write_interaction_trace(
        *component_log_size_iter.next().unwrap(),
        circuit_interaction_claim_generator.eq_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(eq_trace);
    let (qm31_ops_trace, qm31_ops_claimed_sum) = qm31_ops::write_interaction_trace(
        *component_log_size_iter.next().unwrap(),
        circuit_interaction_claim_generator.qm31_ops_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(qm31_ops_trace);

    // Write blake gate interaction trace.
    let (blake_gate_trace, blake_gate_interaction_claim) = circuit_interaction_claim_generator
        .blake_gate
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_gate_trace);

    // Write blake round interaction trace.
    let (blake_round_trace, blake_round_interaction_claim) = circuit_interaction_claim_generator
        .blake_round
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_round_trace);

    // Write blake round sigma interaction trace.
    let (blake_round_sigma_trace, blake_round_sigma_interaction_claim) =
        circuit_interaction_claim_generator
            .blake_round_sigma
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_round_sigma_trace);

    // Write blake g interaction trace.
    let (blake_g_trace, blake_g_interaction_claim) = circuit_interaction_claim_generator
        .blake_g
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_g_trace);

    // Write blake output interaction trace.
    let (blake_output_trace, blake_output_interaction_claim) = circuit_interaction_claim_generator
        .blake_output
        .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(blake_output_trace);

    // Write triple xor 32 interaction trace.
    let (triple_xor_32_trace, triple_xor_32_interaction_claim) =
        circuit_interaction_claim_generator
            .triple_xor_32
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(triple_xor_32_trace);

    // Write verify bitwise xor 8 interaction trace.
    let (verify_bitwise_xor_8_trace, verify_bitwise_xor_8_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_8
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_8_trace);
    let (verify_bitwise_xor_12_trace, verify_bitwise_xor_12_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_12
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_12_trace);

    // Write verify bitwise xor 4 interaction trace.
    let (verify_bitwise_xor_4_trace, verify_bitwise_xor_4_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_4
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_4_trace);

    // Write verify bitwise xor 7 interaction trace.
    let (verify_bitwise_xor_7_trace, verify_bitwise_xor_7_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_7
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_7_trace);

    // Write verify bitwise xor 9 interaction trace.
    let (verify_bitwise_xor_9_trace, verify_bitwise_xor_9_interaction_claim) =
        circuit_interaction_claim_generator
            .verify_bitwise_xor_9
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(verify_bitwise_xor_9_trace);

    // Write range check 15 interaction trace.
    let (range_check_15_trace, range_check_15_interaction_claim) =
        circuit_interaction_claim_generator
            .range_check_15
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(range_check_15_trace);

    // Write range check 16 interaction trace.
    let (range_check_16_trace, range_check_16_interaction_claim) =
        circuit_interaction_claim_generator
            .range_check_16
            .write_interaction_trace(&interaction_elements.common_lookup_elements);
    tree_builder.extend_evals(range_check_16_trace);

    CircuitInteractionClaim {
        claimed_sums: [
            eq_claimed_sum,
            qm31_ops_claimed_sum,
            blake_gate_interaction_claim.claimed_sum,
            blake_round_interaction_claim.claimed_sum,
            blake_round_sigma_interaction_claim.claimed_sum,
            blake_g_interaction_claim.claimed_sum,
            blake_output_interaction_claim.claimed_sum,
            triple_xor_32_interaction_claim.claimed_sum,
            verify_bitwise_xor_8_interaction_claim.claimed_sum,
            verify_bitwise_xor_12_interaction_claim.claimed_sum,
            verify_bitwise_xor_4_interaction_claim.claimed_sum,
            verify_bitwise_xor_7_interaction_claim.claimed_sum,
            verify_bitwise_xor_9_interaction_claim.claimed_sum,
            range_check_15_interaction_claim.claimed_sum,
            range_check_16_interaction_claim.claimed_sum,
        ],
    }
}