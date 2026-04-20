use crate::circuit_eval_components::prelude::*;

pub struct Component {}

impl<Value: IValue> CircuitEval<Value> for Component {
    fn name(&self) -> String {
        "poseidon_gate".to_string()
    }

    fn trace_columns(&self) -> usize {
        crate::components::poseidon_gate::N_TRACE_COLUMNS
    }

    fn interaction_columns(&self) -> usize {
        crate::components::poseidon_gate::N_INTERACTION_COLUMNS
    }

    fn evaluate(
        &self,
        _context: &mut Context<Value>,
        _component_data: &dyn ComponentDataTrait<Value>,
        _acc: &mut CompositionConstraintAccumulator,
    ) {
        // Minimal mirror component: constraints are defined in AIR component.
    }

    fn relation_uses_per_row(&self) -> &[RelationUse] {
        &crate::components::poseidon_gate::RELATION_USES_PER_ROW
    }
}
