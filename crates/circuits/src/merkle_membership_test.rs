use crate::merkle_membership::build_merkle_membership_context;

#[test]
fn test_merkle_membership_context_depth_0() {
    let context = build_merkle_membership_context(0);

    context.check_vars_used();
    context.circuit.check_yields();
    assert!(context.is_circuit_valid());
    assert_eq!(context.circuit.output.len(), 1);
}

#[test]
fn test_merkle_membership_context_depth_3_with_poseidon() {
    let context = build_merkle_membership_context(3);

    context.check_vars_used();
    context.circuit.check_yields();
    assert!(context.is_circuit_valid());

    assert!(context.circuit.mul.len() > 10);
    assert!(context.circuit.eq.len() >= 4);
    assert_eq!(context.circuit.output.len(), 1);
}
