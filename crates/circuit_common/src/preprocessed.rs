use crate::CircuitParams;
use crate::N_LANES;
use crate::Qm31OpsTraceGenerator;
use crate::finalize::finalize_context;
use circuits::circuit::Blake;
use circuits::circuit::{Circuit, Permutation};
use circuits::circuit::{Eq, Gate};
use circuits::context::Context;
use circuits::ivalue::IValue;
use itertools::{Itertools, zip_eq};
use std::collections::HashMap;
use std::sync::Arc;
#[cfg(feature = "prover")]
use stwo::core::fields::m31::BaseField;
#[cfg(feature = "prover")]
use stwo::core::poly::circle::CanonicCoset;
#[cfg(feature = "prover")]
use stwo::prover::backend::simd::m31::PackedM31;
#[cfg(feature = "prover")]
use stwo::prover::backend::{Backend, Col, Column};
#[cfg(feature = "prover")]
use stwo::prover::poly::BitReversedOrder;
#[cfg(feature = "prover")]
use stwo::prover::poly::circle::CircleEvaluation;
pub use stwo_cairo_common::preprocessed_columns::blake::BLAKE_SIGMA;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

#[cfg(feature = "prover")]
#[cfg(test)]
#[path = "preprocessed_test.rs"]
pub mod test;

const N_QM31_OPS_PP_COLUMNS: usize = 8;
const N_EQ_PP_COLUMNS: usize = 2;
const N_OP_CODES: usize = 4;

#[derive(Copy, Clone)]
enum OpCode {
    Add,
    Sub,
    Mul,
    PointwiseMul,
}

/// Adds the binary operation gates to the qm31 ops preprocessed trace.
fn fill_binary_op_columns<G: Gate>(
    gates: &[G],
    op_code: OpCode,
    multiplicities: &[usize],
    columns: &mut [Vec<usize>; N_QM31_OPS_PP_COLUMNS],
) {
    let op_code_idx = op_code as usize;
    for gate in gates.iter() {
        let [in0, in1] = gate.uses()[..] else { panic!("Expected 2 uses for gate") };
        let [out] = gate.yields()[..] else { panic!("Expected 1 yield for gate") };
        (0..N_OP_CODES).for_each(|i| {
            columns[i].push(if i == op_code_idx { 1 } else { 0 });
        });
        columns[4].push(in0);
        columns[5].push(in1);
        columns[6].push(out);
        // TODO(Gali): Consider negating the multiplicities.
        columns[7].push(multiplicities[out]);
    }
}

/// Implements a permutation gate with n inputs and n outputs using 2n Add gates.
///
/// Process:
/// 1. First n gates: Write inputs to permutation wire
///    - `permutation_wire = Add(0, input_i)` for each input i
/// 2. Next n gates: Read outputs from permutation wire
///    - `output_i = Add(0, permutation_wire)` for each output i
///
/// Using the same wire address for all the inputs with multiplicity 1 ensures that the outputs
/// are a permutation of the inputs.
fn fill_permutation_columns(
    gates: &[Permutation],
    multiplicities: &[usize],
    columns: &mut [Vec<usize>; N_QM31_OPS_PP_COLUMNS],
    first_unused_address: usize,
) {
    let add_op_code_idx = OpCode::Add as usize;
    let mut permutation_address = first_unused_address;
    for gate in gates.iter() {
        let inputs = gate.uses();
        let outputs = gate.yields();

        // Set flag to Add opcode.
        (0..N_OP_CODES).for_each(|i| {
            columns[i].extend(std::iter::repeat_n(
                (i == add_op_code_idx) as usize,
                inputs.len() + outputs.len(),
            ));
        });

        // TODO(alonf): Parallelize, and insert the above loop inside.
        for (input, output) in zip_eq(inputs, outputs) {
            // Input row.
            columns[4].push(0);
            columns[5].push(input);
            columns[6].push(permutation_address);
            columns[7].push(1);

            // Output row.
            columns[4].push(0);
            columns[5].push(permutation_address);
            columns[6].push(output);
            columns[7].push(multiplicities[output]);
        }

        permutation_address += 1;
    }
}

/// Adds the eq gates to the eq preprocessed trace.
fn fill_eq_columns(eq_gates: &[Eq], columns: &mut [Vec<usize>; N_EQ_PP_COLUMNS]) {
    for gate in eq_gates.iter() {
        let [in0, in1] = gate.uses()[..] else { panic!("Expected 2 uses for gate") };
        assert!(gate.yields().is_empty(), "Expected no yields for Eq gate");
        columns[0].push(in0);
        columns[1].push(in1);
    }
}

/// Adds the preprocessed columns of qm31_ops component to the preprocessed trace. If the component
/// is empty, no columns are added. Preprocessed columns are in the following format:
/// | add_flag | sub_flag | mul_flag | pointwise_mul_flag | in0_address | in1_address | out_address | mults |
fn add_qm31_ops_to_preprocessed_trace(
    circuit: &Circuit,
    multiplicities: &[usize],
    pp_trace: &mut PreProcessedTrace,
) -> Qm31OpsTraceGenerator {
    let Circuit { n_vars, add, sub, mul, pointwise_mul, eq: _, blake: _, poseidon: _, permutation, output: _ } =
        circuit;
    let mut qm31_ops_columns: [_; N_QM31_OPS_PP_COLUMNS] = std::array::from_fn(|_| vec![]);
    fill_binary_op_columns(add, OpCode::Add, multiplicities, &mut qm31_ops_columns);
    fill_binary_op_columns(sub, OpCode::Sub, multiplicities, &mut qm31_ops_columns);
    fill_binary_op_columns(mul, OpCode::Mul, multiplicities, &mut qm31_ops_columns);
    fill_binary_op_columns(
        pointwise_mul,
        OpCode::PointwiseMul,
        multiplicities,
        &mut qm31_ops_columns,
    );
    let qm31_ops_trace_generator =
        Qm31OpsTraceGenerator { first_permutation_row: qm31_ops_columns[0].len() };

    fill_permutation_columns(permutation, multiplicities, &mut qm31_ops_columns, *n_vars);

    let ids = [
        "qm31_ops_add_flag",
        "qm31_ops_sub_flag",
        "qm31_ops_mul_flag",
        "qm31_ops_pointwise_mul_flag",
        "qm31_ops_in0_address",
        "qm31_ops_in1_address",
        "qm31_ops_out_address",
        "qm31_ops_mults",
    ];
    for (id, column) in zip_eq(ids, qm31_ops_columns) {
        pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
    }
    qm31_ops_trace_generator
}

/// Adds the preprocessed columns of eq component to the preprocessed trace. If the component
/// is empty, no columns are added. Preprocessed columns are in the following format:
/// | in0_address | in1_address |
fn add_eq_to_preprocessed_trace(circuit: &Circuit, pp_trace: &mut PreProcessedTrace) {
    let Circuit {
        n_vars: _,
        add: _,
        sub: _,
        mul: _,
        pointwise_mul: _,
        eq,
        blake: _,
        poseidon: _,
        permutation: _,
        output: _,
    } = circuit;
    let mut eq_columns: [_; N_EQ_PP_COLUMNS] = std::array::from_fn(|_| vec![]);
    fill_eq_columns(eq, &mut eq_columns);

    let ids = ["eq_in0_address", "eq_in1_address"];
    for (id, column) in zip_eq(ids, eq_columns) {
        pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
    }
}

// TODO(alonf): Parallelize.
fn fill_blake_columns(
    blake: &[Blake],
    multiplicities: &[usize],
    columns: &mut [Vec<usize>; N_BLAKE_PP_COLUMNS],
) {
    // IV should be in state_address 0.
    let mut state_address = 1;
    for gate in blake.iter() {
        let mut message_length = 0;
        for (i, [in0, in1, in2, in3]) in gate.input.iter().enumerate() {
            // The current message length split to 2 u16.
            message_length = gate.n_bytes.min(message_length + 16 * 4);
            columns[0].push(message_length & 0xffff);
            columns[1].push((message_length >> 16) & 0xffff);

            // Finalize flag.
            columns[2].push(0);

            // State before and after addresses.
            let is_first_compression = i == 0;
            let state_address_before = if is_first_compression {
                // First compression starts from IV at address 0.
                0
            } else {
                state_address
            };
            columns[3].push(state_address_before);

            if !is_first_compression {
                state_address += 1;
            }
            columns[4].push(state_address);

            // Message addresses.
            columns[5].push(*in0);
            columns[6].push(*in1);
            columns[7].push(*in2);
            columns[8].push(*in3);

            // Enable
            columns[9].push(1);
        }

        // Set the finalize flag to 1 for the last compression of the gate.
        *columns[2].last_mut().unwrap() = 1;

        // Fill the preprocessed column needed by the blake_output component.
        // Set final state address.
        columns[10].push(state_address);

        let [out0, out1] = gate.yields()[..] else { panic!("Expected 2 yields for gate") };
        columns[11].push(out0);
        columns[12].push(out1);
        columns[13].push(multiplicities[out0]);
        columns[14].push(multiplicities[out1]);

        // Start a new blake chain.
        state_address += 1;
    }

    // Pad the preprocessed columns used in blake compress.
    let n_blake_compress = columns[0].len();
    let blake_compress_padding = std::cmp::max(n_blake_compress.next_power_of_two(), N_LANES);

    // TODO(Leo): remove after we remove the circuit gates padding.
    assert_eq!(
        n_blake_compress % N_LANES,
        0,
        "Only padding to multiple of N_LANES through circuit gates for now."
    );

    // Pad with the first element.
    (0..9).for_each(|i| columns[i].resize(blake_compress_padding, *columns[i].first().unwrap()));
    columns[9].resize(blake_compress_padding, 0); // Enabler columns.

    // Pad the preprocessed columns used in blake output
    let n_blake_output = columns[10].len();
    let blake_output_padding = std::cmp::max(n_blake_output.next_power_of_two(), N_LANES);

    // Pad final_state_addr with zeros, so padding rows read the Blake initial state as the final
    // state
    columns[10].resize(blake_output_padding, 0);
    (11..13).for_each(|i| columns[i].resize(blake_output_padding, *columns[i].first().unwrap()));
    (13..15).for_each(|i| columns[i].resize(blake_output_padding, 0)); // Multiplicity columns.
}

/// Builds the fixed preprocessed table for BLAKE sigma lookups.
///
/// Returns 16 columns (`blake_sigma_0..blake_sigma_15`), each with 16 rows (`LOG_SIZE = 4`).
/// For each column `i`:
/// - rows `0..10` hold `BLAKE_SIGMA[round][i]` for rounds `0..9`.
/// - rows `10..16` are padded with `BLAKE_SIGMA[0][i]`.
///
/// The padding keeps the table at a power-of-two height while preserving a valid sigma row.
fn gen_blake_sigma_columns() -> [Vec<usize>; 16] {
    std::array::from_fn(|i| {
        let mut col = Vec::with_capacity(16);
        for sigma_row in BLAKE_SIGMA.iter().take(10) {
            col.push(sigma_row[i] as usize);
        }
        // Pad rows 10..15 with round 0 values.
        for _ in 10..16 {
            col.push(BLAKE_SIGMA[0][i] as usize);
        }
        col
    })
}

// 10 columns for blake_gate and 5 columns for blake_output
const N_BLAKE_PP_COLUMNS: usize = 10 + 5;

fn add_blake_to_preprocessed_trace(
    circuit: &Circuit,
    multiplicities: &[usize],
    pp_trace: &mut PreProcessedTrace,
) {
    let Circuit {
        n_vars: _,
        add: _,
        sub: _,
        mul: _,
        pointwise_mul: _,
        eq: _,
        blake,
        poseidon: _,
        permutation: _,
        output: _,
    } = circuit;
    let mut blake_columns: [_; N_BLAKE_PP_COLUMNS] = std::array::from_fn(|_| vec![]);
    fill_blake_columns(blake, multiplicities, &mut blake_columns);

    let blake_ids = [
        "t0",
        "t1",
        "finalize_flag",
        "state_before_addr",
        "state_after_addr",
        "message0_addr",
        "message1_addr",
        "message2_addr",
        "message3_addr",
        "compress_enabler",
        "final_state_addr",
        "blake_output0_addr",
        "blake_output1_addr",
        "blake_output0_mults",
        "blake_output1_mults",
    ];
    for (id, column) in zip_eq(blake_ids, blake_columns) {
        pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
    }

    // Add blake sigma columns (16 columns of 16 rows each).
    let blake_sigma = gen_blake_sigma_columns();
    for (i, column) in blake_sigma.into_iter().enumerate() {
        pp_trace.push_column(PreProcessedColumnId { id: format!("blake_sigma_{i}") }, column);
    }
}

/// A collection of preprocessed columns, whose values are publicly acknowledged, and independent of
/// the proof.
#[derive(Clone, Debug, PartialEq)]
pub struct PreProcessedTrace {
    pub columns: Vec<Vec<usize>>,
    column_ids: Vec<PreProcessedColumnId>,
    column_indices: HashMap<PreProcessedColumnId, usize>,
}

impl PreProcessedTrace {
    fn push_column(&mut self, id: PreProcessedColumnId, column: Vec<usize>) {
        let idx = self.columns.len();
        assert!(
            self.column_indices.insert(id.clone(), idx).is_none(),
            "Duplicate preprocessed column id: {id:?}"
        );
        self.column_ids.push(id);
        self.columns.push(column);
    }

    /// Sorts preprocessed columns by size (ascending), preserving original order for ties.
    fn sort_by_size(&mut self) {
        let mut entries = std::mem::take(&mut self.columns)
            .into_iter()
            .zip(std::mem::take(&mut self.column_ids))
            .collect_vec();
        // Stable sort keeps original insertion order for equal-length columns.
        entries.sort_by_key(|(column, _)| column.len());

        self.columns = entries.iter_mut().map(|(column, _)| std::mem::take(column)).collect();
        self.column_ids = entries.into_iter().map(|(_, id)| id).collect();
        self.column_indices =
            self.column_ids.iter().cloned().enumerate().map(|(idx, id)| (id, idx)).collect();
    }
    fn add_non_circuit_preprocessed_columns(
        pp_trace: &mut PreProcessedTrace,
        log_seq_sizes: &[u32],
    ) {
        for &log_size in log_seq_sizes {
            let seq_column: Vec<usize> = (0..1_usize << log_size).collect();
            pp_trace
                .push_column(PreProcessedColumnId { id: format!("seq_{log_size}") }, seq_column);
        }
        let bitwise_xor: Vec<Vec<usize>> = [4, 7, 8, 9, 10]
            .into_iter()
            .flat_map(|n_bits| gen_xor_columns(n_bits).into_iter())
            .collect();
        let xor_col_ids = [
            "bitwise_xor_4_0",
            "bitwise_xor_4_1",
            "bitwise_xor_4_2",
            "bitwise_xor_7_0",
            "bitwise_xor_7_1",
            "bitwise_xor_7_2",
            "bitwise_xor_8_0",
            "bitwise_xor_8_1",
            "bitwise_xor_8_2",
            "bitwise_xor_9_0",
            "bitwise_xor_9_1",
            "bitwise_xor_9_2",
            "bitwise_xor_10_0",
            "bitwise_xor_10_1",
            "bitwise_xor_10_2",
        ];
        for (id, column) in zip_eq(xor_col_ids, bitwise_xor) {
            pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
        }
    }

    pub fn log_sizes(&self) -> Vec<u32> {
        self.columns.iter().map(|c| c.len().ilog2()).collect()
    }

    pub fn ids(&self) -> Vec<PreProcessedColumnId> {
        self.column_ids.clone()
    }

    #[cfg(feature = "prover")]
    pub fn get_trace<B: Backend>(&self) -> Vec<CircleEvaluation<B, BaseField, BitReversedOrder>> {
        let to_evaluation = |vec: &[usize]| {
            let col = Col::<B, BaseField>::from_iter(vec.iter().cloned().map(BaseField::from));
            CircleEvaluation::new(CanonicCoset::new(col.len().ilog2()).circle_domain(), col)
        };

        self.columns.iter().map(|c| to_evaluation(c)).collect()
    }

    pub fn get_column(&self, id: &PreProcessedColumnId) -> &Vec<usize> {
        &self.columns[*self
            .column_indices
            .get(id)
            .unwrap_or_else(|| panic!("Missing preprocessed column {id:?}"))]
    }

    #[cfg(feature = "prover")]
    pub fn get_packed_column(&self, id: &PreProcessedColumnId) -> Vec<PackedM31> {
        let column = self.get_column(id);
        column
            .chunks_exact(N_LANES)
            .map(|c| PackedM31::from_array(std::array::from_fn(|i| BaseField::from(c[i]))))
            .collect::<Vec<_>>()
    }
}

#[derive(Debug, PartialEq)]
pub struct PreprocessedCircuit {
    pub preprocessed_trace: Arc<PreProcessedTrace>,
    pub params: CircuitParams,
}

impl PreprocessedCircuit {
    /// Finalizes the context, then builds the preprocessed circuit.
    pub fn preprocess_circuit(context: &mut Context<impl IValue>) -> Self {
        finalize_context(context);
        Self::from_finalized_circuit(&context.circuit)
    }

    /// Builds the preprocessed circuit data (trace + params) from a finalized circuit.
    pub fn from_finalized_circuit(circuit: &Circuit) -> Self {
        let mut pp_trace = PreProcessedTrace {
            columns: vec![],
            column_ids: vec![],
            column_indices: HashMap::new(),
        };

        // Adjust multiplicities to account for the use of the constant 0 in the permutation gate
        // implementation. See `fill_permutation_columns` for details.
        let mut multiplicities = circuit.compute_multiplicities().0;
        let additional_zero_multiplicity: usize =
            circuit.permutation.iter().map(|gate| gate.inputs.len() + gate.outputs.len()).sum();
        multiplicities[0] += additional_zero_multiplicity;

        // Add Eq columns.
        add_eq_to_preprocessed_trace(circuit, &mut pp_trace);
        // Add QM31 operations columns.
        let qm31_ops_trace_generator =
            add_qm31_ops_to_preprocessed_trace(circuit, &multiplicities, &mut pp_trace);
        // Add Blake columns.
        add_blake_to_preprocessed_trace(circuit, &multiplicities, &mut pp_trace);
        let log_n_blake_updates = pp_trace
            .get_column(&PreProcessedColumnId { id: "finalize_flag".to_owned() })
            .len()
            .ilog2();

        // Generate seq columns for sizes needed by circuit components:
        // - 15, 16: needed by range_check_15 and range_check_16.
        // - 4: needed by blake_sigma.
        // - log_sizes of existing preprocessed columns: needed by components using
        //   seq_of_component_size (e.g. blake_gate).
        let mut log_seq_sizes: Vec<u32> = pp_trace.log_sizes();
        log_seq_sizes.extend([log_n_blake_updates, 4, 15, 16]);
        log_seq_sizes.sort();
        log_seq_sizes.dedup();
        PreProcessedTrace::add_non_circuit_preprocessed_columns(&mut pp_trace, &log_seq_sizes);
        pp_trace.sort_by_size();

        // The trace size is the max between:
        // 1. The largest preprocessed column size.
        // 2. BlakeG trace size (= number of blake updates * 2^7).
        let max_pp_trace_log_size = pp_trace.log_sizes().into_iter().max().unwrap();
        let blake_g_log_size = log_n_blake_updates + 7;
        let trace_log_size = std::cmp::max(max_pp_trace_log_size, blake_g_log_size);

        let params = CircuitParams {
            trace_log_size,
            first_permutation_row: qm31_ops_trace_generator.first_permutation_row,
            n_blake_gates: circuit.blake.len(),
            output_addresses: circuit.output.iter().map(|out| out.in0).collect(),
        };

        Self { preprocessed_trace: Arc::new(pp_trace), params }
    }
}

/// Generates three columns of size (2^n_bits)^2. The first two columns are all ordered pairs of
/// n-bit values, and the third column contains the bitwise XOR of each pair.
fn gen_xor_columns(n_bits: usize) -> [Vec<usize>; 3] {
    let size = 1_usize << (2 * n_bits);
    let mask = (1_usize << n_bits) - 1;
    let mut columns: [Vec<usize>; 3] = std::array::from_fn(|_| vec![0; size]);
    for i in 0..size {
        let lhs = i & mask;
        let rhs = i >> n_bits;
        columns[0][i] = rhs;
        columns[1][i] = lhs;
        columns[2][i] = lhs ^ rhs;
    }
    columns
}
