pub mod blake_g;
pub mod blake_gate;
pub mod blake_output;
pub mod blake_round;
pub mod blake_round_sigma;
pub mod eq;
pub mod prelude;
pub mod qm31_ops;
pub mod range_check_15;
pub mod range_check_16;
pub mod subroutines;
pub mod triple_xor_32;
pub mod verify_bitwise_xor_12;
pub mod verify_bitwise_xor_4;
pub mod verify_bitwise_xor_7;
pub mod verify_bitwise_xor_8;
pub mod verify_bitwise_xor_9;
pub mod poseidon_gate;

use crate::{CircuitClaim, CircuitInteractionClaim, CircuitInteractionElements};
use stwo::core::air::Component;
use stwo_constraint_framework::TraceLocationAllocator;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

macro_rules! define_component_list {
    ($($variant:ident),* $(,)?) => {
        pub enum ComponentList {
            $($variant),*
        }
        pub const N_COMPONENTS: usize = [$(stringify!($variant)),*].len();
    };
}

define_component_list! {
    Eq,
    Qm31Ops,
    PoseidonGate,
    BlakeGate,
    BlakeRound,
    BlakeRoundSigma,
    BlakeG,
    BlakeOutput,
    TripleXor32,
    VerifyBitwiseXor8,
    VerifyBitwiseXor12,
    VerifyBitwiseXor4,
    VerifyBitwiseXor7,
    VerifyBitwiseXor9,
    RangeCheck15,
    RangeCheck16,
}

pub struct CircuitComponents {
    pub eq: eq::Component,
    pub qm31_ops: qm31_ops::Component,
    pub blake_gate: blake_gate::Component,
    pub blake_round: blake_round::Component,
    pub blake_round_sigma: blake_round_sigma::Component,
    pub blake_g: blake_g::Component,
    pub blake_output: blake_output::Component,
    pub triple_xor_32: triple_xor_32::Component,
    pub verify_bitwise_xor_8: verify_bitwise_xor_8::Component,
    pub verify_bitwise_xor_12: verify_bitwise_xor_12::Component,
    pub verify_bitwise_xor_4: verify_bitwise_xor_4::Component,
    pub verify_bitwise_xor_7: verify_bitwise_xor_7::Component,
    pub verify_bitwise_xor_9: verify_bitwise_xor_9::Component,
    pub poseidon_gate: poseidon_gate::Component,
    pub range_check_15: range_check_15::Component,
    pub range_check_16: range_check_16::Component,
}
impl CircuitComponents {
    pub fn new(
        circuit_claim: &CircuitClaim,
        interaction_elements: &CircuitInteractionElements,
        interaction_claim: &CircuitInteractionClaim,
        // Describes the structure of the preprocessed trace. Sensitive to order.
        preprocessed_column_ids: &[PreProcessedColumnId],
    ) -> Self {
        let tree_span_provider =
            &mut TraceLocationAllocator::new_with_preprocessed_columns(preprocessed_column_ids);

        let eq_component = eq::Component::new(
            tree_span_provider,
            eq::Eval {
                log_size: circuit_claim.log_sizes[ComponentList::Eq as usize],
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::Eq as usize],
        );
        let qm31_ops_component = qm31_ops::Component::new(
            tree_span_provider,
            qm31_ops::Eval {
                log_size: circuit_claim.log_sizes[ComponentList::Qm31Ops as usize],
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::Qm31Ops as usize],
        );
        let poseidon_gate_component = poseidon_gate::Component::new(
            tree_span_provider,
            poseidon_gate::Eval {
                claim: poseidon_gate::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::PoseidonGate as usize],
                },
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::PoseidonGate as usize],
        );
        let blake_gate_component = blake_gate::Component::new(
            tree_span_provider,
            blake_gate::Eval {
                claim: blake_gate::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::BlakeGate as usize],
                },
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::BlakeGate as usize],
        );
        let blake_round_component = blake_round::Component::new(
            tree_span_provider,
            blake_round::Eval {
                claim: blake_round::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::BlakeRound as usize],
                },
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::BlakeRound as usize],
        );
        let blake_round_sigma_component = blake_round_sigma::Component::new(
            tree_span_provider,
            blake_round_sigma::Eval {
                claim: blake_round_sigma::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::BlakeRoundSigma as usize],
        );
        let blake_g_component = blake_g::Component::new(
            tree_span_provider,
            blake_g::Eval {
                claim: blake_g::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::BlakeG as usize],
                },
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::BlakeG as usize],
        );
        let blake_output_component = blake_output::Component::new(
            tree_span_provider,
            blake_output::Eval {
                claim: blake_output::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::BlakeOutput as usize],
                },
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::BlakeOutput as usize],
        );
        let triple_xor_32_component = triple_xor_32::Component::new(
            tree_span_provider,
            triple_xor_32::Eval {
                claim: triple_xor_32::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::TripleXor32 as usize],
                },
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::TripleXor32 as usize],
        );
        let verify_bitwise_xor_8_component = verify_bitwise_xor_8::Component::new(
            tree_span_provider,
            verify_bitwise_xor_8::Eval {
                claim: verify_bitwise_xor_8::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::VerifyBitwiseXor8 as usize],
        );
        let verify_bitwise_xor_12_component = verify_bitwise_xor_12::Component::new(
            tree_span_provider,
            verify_bitwise_xor_12::Eval {
                claim: verify_bitwise_xor_12::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::VerifyBitwiseXor12 as usize],
        );
        let verify_bitwise_xor_4_component = verify_bitwise_xor_4::Component::new(
            tree_span_provider,
            verify_bitwise_xor_4::Eval {
                claim: verify_bitwise_xor_4::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::VerifyBitwiseXor4 as usize],
        );
        let verify_bitwise_xor_7_component = verify_bitwise_xor_7::Component::new(
            tree_span_provider,
            verify_bitwise_xor_7::Eval {
                claim: verify_bitwise_xor_7::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::VerifyBitwiseXor7 as usize],
        );
        let verify_bitwise_xor_9_component = verify_bitwise_xor_9::Component::new(
            tree_span_provider,
            verify_bitwise_xor_9::Eval {
                claim: verify_bitwise_xor_9::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::VerifyBitwiseXor9 as usize],
        );
        let range_check_15_component = range_check_15::Component::new(
            tree_span_provider,
            range_check_15::Eval {
                claim: range_check_15::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::RangeCheck15 as usize],
        );
        let range_check_16_component = range_check_16::Component::new(
            tree_span_provider,
            range_check_16::Eval {
                claim: range_check_16::Claim {},
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::RangeCheck16 as usize],
        );
        Self {
            eq: eq_component,
            qm31_ops: qm31_ops_component,
            poseidon_gate: poseidon_gate_component,
            blake_gate: blake_gate_component,
            blake_round: blake_round_component,
            blake_round_sigma: blake_round_sigma_component,
            blake_g: blake_g_component,
            blake_output: blake_output_component,
            triple_xor_32: triple_xor_32_component,
            verify_bitwise_xor_8: verify_bitwise_xor_8_component,
            verify_bitwise_xor_12: verify_bitwise_xor_12_component,
            verify_bitwise_xor_4: verify_bitwise_xor_4_component,
            verify_bitwise_xor_7: verify_bitwise_xor_7_component,
            verify_bitwise_xor_9: verify_bitwise_xor_9_component,
            range_check_15: range_check_15_component,
            range_check_16: range_check_16_component,
        }
    }

    pub fn components(self) -> Vec<Box<dyn Component>> {
        vec![
            Box::new(self.eq) as Box<dyn Component>,
            Box::new(self.qm31_ops) as Box<dyn Component>,
            Box::new(self.poseidon_gate) as Box<dyn Component>,
            Box::new(self.blake_gate) as Box<dyn Component>,
            Box::new(self.blake_round) as Box<dyn Component>,
            Box::new(self.blake_round_sigma) as Box<dyn Component>,
            Box::new(self.blake_g) as Box<dyn Component>,
            Box::new(self.blake_output) as Box<dyn Component>,
            Box::new(self.triple_xor_32) as Box<dyn Component>,
            Box::new(self.verify_bitwise_xor_8) as Box<dyn Component>,
            Box::new(self.verify_bitwise_xor_12) as Box<dyn Component>,
            Box::new(self.verify_bitwise_xor_4) as Box<dyn Component>,
            Box::new(self.verify_bitwise_xor_7) as Box<dyn Component>,
            Box::new(self.verify_bitwise_xor_9) as Box<dyn Component>,
            Box::new(self.range_check_15) as Box<dyn Component>,
            Box::new(self.range_check_16) as Box<dyn Component>,
        ]
    }
}
