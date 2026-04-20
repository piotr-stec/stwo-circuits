use crate::components::prelude::*;
use circuits_stark_verifier::constraint_eval::{ComponentDataTrait, RelationUse};

pub const N_TRACE_COLUMNS: usize = 12;
pub const N_INTERACTION_COLUMNS: usize = 4;
pub const RELATION_USES_PER_ROW: [RelationUse; 1] = [RelationUse {
    relation_id: "gate",
    uses: 3,
}];

pub struct Eval {
    pub claim: Claim,
    pub common_lookup_elements: relations::CommonLookupElements,
}

#[derive(Copy, Clone, Serialize, Deserialize)]
pub struct Claim {
    pub log_size: u32,
}
impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size; N_TRACE_COLUMNS];
        let interaction_log_sizes = vec![self.log_size; N_INTERACTION_COLUMNS];
        TreeVec::new(vec![vec![], trace_log_sizes, interaction_log_sizes])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Copy, Clone, Serialize, Deserialize)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}
impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub type Component = FrameworkComponent<Eval>;

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let gate_relation_id = E::F::from(M31::from(378353459));

        let in0_address = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_in0_address".to_owned(),
        });
        let in1_address = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_in1_address".to_owned(),
        });
        let out_address = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_out_address".to_owned(),
        });
        let out_mults = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_out_mults".to_owned(),
        });

        // in0 limbs
        let in0_limb0 = eval.next_trace_mask();
        let in0_limb1 = eval.next_trace_mask();
        let in0_limb2 = eval.next_trace_mask();
        let in0_limb3 = eval.next_trace_mask();
        // in1 limbs
        let in1_limb0 = eval.next_trace_mask();
        let in1_limb1 = eval.next_trace_mask();
        let in1_limb2 = eval.next_trace_mask();
        let in1_limb3 = eval.next_trace_mask();
        // out limbs
        let out_limb0 = eval.next_trace_mask();
        let out_limb1 = eval.next_trace_mask();
        let out_limb2 = eval.next_trace_mask();
        let out_limb3 = eval.next_trace_mask();

        // TODO: Add Poseidon2 transition constraints here.

        // use(in0)
        eval.add_to_relation(RelationEntry::new(
            &self.common_lookup_elements,
            E::EF::one(),
            &[
                gate_relation_id.clone(),
                in0_address,
                in0_limb0,
                in0_limb1,
                in0_limb2,
                in0_limb3,
            ],
        ));

        // use(in1)
        eval.add_to_relation(RelationEntry::new(
            &self.common_lookup_elements,
            E::EF::one(),
            &[
                gate_relation_id.clone(),
                in1_address,
                in1_limb0,
                in1_limb1,
                in1_limb2,
                in1_limb3,
            ],
        ));

        // yield(out)
        eval.add_to_relation(RelationEntry::new(
            &self.common_lookup_elements,
            -E::EF::from(out_mults),
            &[gate_relation_id, out_address, out_limb0, out_limb1, out_limb2, out_limb3],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub struct CircuitPoseidonGateComponent;

impl<Value: IValue> CircuitEval<Value> for CircuitPoseidonGateComponent {
    fn name(&self) -> String {
        "poseidon_gate".to_string()
    }

    fn trace_columns(&self) -> usize {
        N_TRACE_COLUMNS
    }

    fn interaction_columns(&self) -> usize {
        N_INTERACTION_COLUMNS
    }

    fn evaluate(
        &self,
        context: &mut Context<Value>,
        component_data: &dyn ComponentDataTrait<Value>,
        acc: &mut CompositionConstraintAccumulator,
    ) {
        let gate_relation_id = context.constant(SecureField::from(M31::from(378353459)));
        let in0_address = acc.get_preprocessed_column(&PreProcessedColumnId {
            id: "poseidon_in0_address".to_owned(),
        });
        let in1_address = acc.get_preprocessed_column(&PreProcessedColumnId {
            id: "poseidon_in1_address".to_owned(),
        });
        let out_address = acc.get_preprocessed_column(&PreProcessedColumnId {
            id: "poseidon_out_address".to_owned(),
        });
        let out_mults = acc.get_preprocessed_column(&PreProcessedColumnId {
            id: "poseidon_out_mults".to_owned(),
        });

        let [
            in0_limb0,
            in0_limb1,
            in0_limb2,
            in0_limb3,
            in1_limb0,
            in1_limb1,
            in1_limb2,
            in1_limb3,
            out_limb0,
            out_limb1,
            out_limb2,
            out_limb3,
        ] = *component_data.trace_columns()
        else {
            panic!("Expected {N_TRACE_COLUMNS} trace columns")
        };

        // TODO: Add Poseidon2 transition constraints here.

        acc.add_to_relation(
            context,
            context.one(),
            &[
                gate_relation_id,
                in0_address,
                in0_limb0,
                in0_limb1,
                in0_limb2,
                in0_limb3,
            ],
        );

        acc.add_to_relation(
            context,
            context.one(),
            &[
                gate_relation_id,
                in1_address,
                in1_limb0,
                in1_limb1,
                in1_limb2,
                in1_limb3,
            ],
        );

        let neg_mults = eval!(context, (context.zero()) - (out_mults));
        acc.add_to_relation(
            context,
            neg_mults,
            &[
                gate_relation_id,
                out_address,
                out_limb0,
                out_limb1,
                out_limb2,
                out_limb3,
            ],
        );
    }

    fn relation_uses_per_row(&self) -> &[RelationUse] {
        &RELATION_USES_PER_ROW
    }
}
