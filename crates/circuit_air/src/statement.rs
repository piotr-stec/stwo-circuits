use crate::circuit_eval_components::{
    blake_g, blake_gate, blake_output, blake_round, blake_round_sigma, poseidon_gate,
    range_check_15, range_check_16, triple_xor_32, verify_bitwise_xor_4, verify_bitwise_xor_7,
    verify_bitwise_xor_8, verify_bitwise_xor_9, verify_bitwise_xor_12,
};
use crate::components::{eq, qm31_ops};
use circuits::blake::HashValue;
use circuits::context::{Context, Var};
use circuits::eval;
use circuits::ivalue::IValue;
use circuits::ops::{Guess, div, eq as eq_op};
use circuits::simd::Simd;
use circuits::wrappers::M31Wrapper;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::logup::{combine_term, logup_use_term};
use circuits_stark_verifier::proof::Claim;
use circuits_stark_verifier::statement::Statement;
use itertools::{Itertools, zip_eq};
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

// TODO(ilya): Update this to to correct values.
pub const INTERACTION_POW_BITS: u32 = 20;

pub struct CircuitStatement<Value: IValue> {
    pub components: Vec<Box<dyn CircuitEval<Value>>>,
    /// The variable indices (addresses) of the output gates.
    pub output_addresses: Vec<M31Wrapper<Var>>,
    /// The values of the output gates.
    pub output_values: Vec<Var>,
    /// The number of blake gates in the circuit.
    pub n_blake_gates: usize,
    /// Preprocessed column ids in the exact order used by the prover's preprocessed trace.
    pub preprocessed_column_ids: Vec<PreProcessedColumnId>,
    /// The preprocessed trace root.
    pub preprocessed_root: HashValue<QM31>,
}
impl<Value: IValue> CircuitStatement<Value> {
    pub fn new(
        context: &mut Context<Value>,
        output_addresses: &[usize],
        output_values: &[QM31],
        n_blake_gates: usize,
        preprocessed_column_ids: Vec<PreProcessedColumnId>,
        preprocessed_root: HashValue<QM31>,
    ) -> Self {
        let output_addresses = output_addresses
            .iter()
            .map(|&addr| M31Wrapper::new_unsafe(context.constant(addr.into())))
            .collect_vec();
        let output_values =
            output_values.iter().map(|value| Value::from_qm31(*value).guess(context)).collect_vec();
        Self {
            components: all_circuit_components(),
            output_addresses,
            output_values,
            n_blake_gates,
            preprocessed_column_ids,
            preprocessed_root,
        }
    }
}
impl<Value: IValue> Statement<Value> for CircuitStatement<Value> {
    fn claims_to_mix(&self, _context: &mut Context<Value>) -> Vec<Vec<Var>> {
        vec![self.output_values.clone()]
    }

    fn get_components(&self) -> &[Box<dyn CircuitEval<Value>>] {
        &self.components
    }

    fn public_logup_sum(
        &self,
        context: &mut Context<Value>,
        interaction_elements: [Var; 2],
        _claim: &Claim<Var>,
    ) -> Var {
        let mut sum = context.zero();

        // Output gates public logup sum contribution.
        let gate_relation_id = eval!(context, 378353459);
        for (output_address, output_value) in zip_eq(&self.output_addresses, &self.output_values) {
            let [output_value_0, output_value_1, output_value_2, output_value_3] =
                Simd::unpack(context, &Simd::from_packed(vec![*output_value], 4))
                    .try_into()
                    .unwrap();
            let term = logup_use_term(
                context,
                &[
                    gate_relation_id,
                    *output_address.get(),
                    output_value_0,
                    output_value_1,
                    output_value_2,
                    output_value_3,
                ],
                interaction_elements,
            );
            sum = eval!(context, (sum) + (term));
        }

        // Blake IV public logup sum contribution.
        if self.n_blake_gates > 0 {
            let initial_state = crate::blake2s_initial_state();
            let iv_state_id = context.constant(1061955672.into());
            let iv_state_address = context.zero();
            let mut blake_iv_elements = vec![iv_state_id, iv_state_address];
            for &word in &initial_state {
                let low = context.constant((word & 0xffff).into());
                let high = context.constant(((word >> 16) & 0xffff).into());
                blake_iv_elements.push(low);
                blake_iv_elements.push(high);
            }
            let blake_iv_denom = combine_term(context, &blake_iv_elements, interaction_elements);
            let n_iv_uses = self.n_blake_gates.next_power_of_two();
            let n_blakes = context.constant((n_iv_uses as u32).into());
            let blake_iv_yield = div(context, n_blakes, blake_iv_denom);
            sum = eval!(context, (sum) - (blake_iv_yield));
        }

        sum
    }

    fn get_preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        self.preprocessed_column_ids.clone()
    }

    fn verify_preprocessed_root(
        &self,
        context: &mut Context<Value>,
        preprocessed_root: HashValue<Var>,
    ) {
        let expected_preprocessed_root = HashValue(
            context.constant(self.preprocessed_root.0),
            context.constant(self.preprocessed_root.1),
        );
        eq_op(context, preprocessed_root.0, expected_preprocessed_root.0);
        eq_op(context, preprocessed_root.1, expected_preprocessed_root.1);
    }
}

pub fn all_circuit_components<Value: IValue>() -> Vec<Box<dyn CircuitEval<Value>>> {
    vec![
        Box::new(eq::CircuitEqComponent {}),
        Box::new(qm31_ops::CircuitQm31OpsComponent {}),
        Box::new(poseidon_gate::Component {}),
        Box::new(blake_gate::Component {}),
        Box::new(blake_round::Component {}),
        Box::new(blake_round_sigma::Component {}),
        Box::new(blake_g::Component {}),
        Box::new(blake_output::Component {}),
        Box::new(triple_xor_32::Component {}),
        Box::new(verify_bitwise_xor_8::Component {}),
        Box::new(verify_bitwise_xor_12::Component {}),
        Box::new(verify_bitwise_xor_4::Component {}),
        Box::new(verify_bitwise_xor_7::Component {}),
        Box::new(verify_bitwise_xor_9::Component {}),
        Box::new(range_check_15::Component {}),
        Box::new(range_check_16::Component {}),
    ]
}
