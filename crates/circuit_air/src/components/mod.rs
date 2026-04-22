pub mod eq;
pub mod poseidon_gate;
pub mod prelude;
pub mod qm31_ops;
pub mod subroutines;

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
}

pub struct CircuitComponents {
    pub eq: eq::Component,
    pub qm31_ops: qm31_ops::Component,
    pub poseidon_gate: poseidon_gate::Component,
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
        Self {
            eq: eq_component,
            qm31_ops: qm31_ops_component,
            poseidon_gate: poseidon_gate_component,
        }
    }

    pub fn components(self) -> Vec<Box<dyn Component>> {
        vec![
            Box::new(self.eq) as Box<dyn Component>,
            Box::new(self.qm31_ops) as Box<dyn Component>,
            Box::new(self.poseidon_gate) as Box<dyn Component>,
        ]
    }
}
