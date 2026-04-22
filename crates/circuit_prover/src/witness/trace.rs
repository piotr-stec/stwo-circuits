use std::sync::Arc;

use crate::witness::components::eq;
use crate::witness::components::poseidon_gate;
use crate::witness::components::qm31_ops;
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
    let (poseidon_gate_trace, poseidon_gate_log_size, poseidon_gate_lookup_data) =
        poseidon_gate::write_trace(context_values, preprocessed_trace_ref);
    let ((eq_trace, eq_log_size, eq_lookup_data), (qm31_ops_trace, qm31_ops_log_size, qm31_ops_lookup_data)) =
        join(
            || eq::write_trace(context_values, preprocessed_trace_ref),
            || {
                qm31_ops::write_trace(
                    context_values,
                    preprocessed_trace_ref,
                    &trace_generator.qm31_ops_trace_generator,
                )
            },
        );
    let mut trace_evals = eq_trace.to_evals();
    trace_evals.extend(qm31_ops_trace.to_evals());
    trace_evals.extend(poseidon_gate_trace.to_evals());

    tree_builder.extend_evals(trace_evals);

    let output_values = output_addresses.iter().map(|addr| context_values[*addr]).collect_vec();

    (
        CircuitClaim {
            log_sizes: [eq_log_size, qm31_ops_log_size, poseidon_gate_log_size],
            output_values,
        },
        CircuitInteractionClaimGenerator {
            eq_lookup_data,
            qm31_ops_lookup_data,
            poseidon_gate_lookup_data,
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
    let (poseidon_gate_trace, poseidon_gate_log_size, poseidon_gate_lookup_data) =
        poseidon_gate::write_trace(context_values, preprocessed_trace_ref);
    let ((eq_trace, eq_log_size, eq_lookup_data), (qm31_ops_trace, qm31_ops_log_size, qm31_ops_lookup_data)) =
        join(
            || eq::write_trace(context_values, preprocessed_trace_ref),
            || {
                qm31_ops::write_trace(
                    context_values,
                    preprocessed_trace_ref,
                    &trace_generator.qm31_ops_trace_generator,
                )
            },
        );
    let mut trace_evals = eq_trace.to_evals();
    trace_evals.extend(qm31_ops_trace.to_evals());
    trace_evals.extend(poseidon_gate_trace.to_evals());

    tree_builder.extend_evals(trace_evals);

    let output_values = output_addresses.iter().map(|addr| context_values[*addr]).collect_vec();

    (
        CircuitClaim {
            log_sizes: [eq_log_size, qm31_ops_log_size, poseidon_gate_log_size],
            output_values,
        },
        CircuitInteractionClaimGenerator {
            eq_lookup_data,
            qm31_ops_lookup_data,
            poseidon_gate_lookup_data,
        },
    )
}

pub struct CircuitInteractionClaimGenerator {
    pub eq_lookup_data: eq::LookupData,
    pub qm31_ops_lookup_data: qm31_ops::LookupData,
    pub poseidon_gate_lookup_data: poseidon_gate::LookupData,
}

pub fn write_interaction_trace(
    circuit_claim: &CircuitClaim,
    circuit_interaction_claim_generator: CircuitInteractionClaimGenerator,
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, Blake2sM31MerkleChannel>,
    interaction_elements: &CircuitInteractionElements,
) -> CircuitInteractionClaim {
    let CircuitClaim { log_sizes, output_values: _ } = circuit_claim;
    let (eq_trace, eq_claimed_sum) = eq::write_interaction_trace(
        log_sizes[0],
        circuit_interaction_claim_generator.eq_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(eq_trace);
    let (qm31_ops_trace, qm31_ops_claimed_sum) = qm31_ops::write_interaction_trace(
        log_sizes[1],
        circuit_interaction_claim_generator.qm31_ops_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(qm31_ops_trace);

    // Write poseidon gate interaction trace.
    let (poseidon_gate_itrace, poseidon_gate_claimed_sum) = poseidon_gate::write_interaction_trace(
        log_sizes[2],
        circuit_interaction_claim_generator.poseidon_gate_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(poseidon_gate_itrace);

    CircuitInteractionClaim {
        claimed_sums: [eq_claimed_sum, qm31_ops_claimed_sum, poseidon_gate_claimed_sum],
    }
}


pub fn write_interaction_trace_keccak(
    circuit_claim: &CircuitClaim,
    circuit_interaction_claim_generator: CircuitInteractionClaimGenerator,
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, KeccakMerkleChannel>,
    interaction_elements: &CircuitInteractionElements,
) -> CircuitInteractionClaim {
    let CircuitClaim { log_sizes, output_values: _ } = circuit_claim;
    let (eq_trace, eq_claimed_sum) = eq::write_interaction_trace(
        log_sizes[0],
        circuit_interaction_claim_generator.eq_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(eq_trace);
    let (qm31_ops_trace, qm31_ops_claimed_sum) = qm31_ops::write_interaction_trace(
        log_sizes[1],
        circuit_interaction_claim_generator.qm31_ops_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(qm31_ops_trace);

    // Write poseidon gate interaction trace.
    let (poseidon_gate_itrace, poseidon_gate_claimed_sum) = poseidon_gate::write_interaction_trace(
        log_sizes[2],
        circuit_interaction_claim_generator.poseidon_gate_lookup_data,
        &interaction_elements.common_lookup_elements,
    );
    tree_builder.extend_evals(poseidon_gate_itrace);

    CircuitInteractionClaim {
        claimed_sums: [eq_claimed_sum, qm31_ops_claimed_sum, poseidon_gate_claimed_sum],
    }
}