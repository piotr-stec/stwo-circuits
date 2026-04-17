use super::*;

#[test]
fn test_full_flow() {
    let balance_str: &[u8; 12] = b"100         ";
    let blinder: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

    let committed_hash = compute_commitment(balance_str, &blinder);
    let ctx = build_balance_commitment_circuit(balance_str, &blinder, committed_hash);

    assert!(ctx.is_circuit_valid());
    assert_eq!(ctx.circuit.output.len(), 2);
}

#[test]
fn test_full_flow_wrong_blinder_fails() {
    let balance_str: &[u8; 12] = b"100         ";
    let correct_blinder: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let wrong_blinder: [u8; 16] = [99; 16];

    let committed_hash = compute_commitment(balance_str, &correct_blinder);
    let ctx = build_balance_commitment_circuit(balance_str, &wrong_blinder, committed_hash);

    assert!(!ctx.is_circuit_valid());
}

#[test]
fn test_full_flow_wrong_balance_fails() {
    let real_balance: &[u8; 12] = b"100         ";
    let fake_balance: &[u8; 12] = b"999         ";
    let blinder: [u8; 16] = [1; 16];

    let committed_hash = compute_commitment(real_balance, &blinder);
    let ctx = build_balance_commitment_circuit(fake_balance, &blinder, committed_hash);

    assert!(!ctx.is_circuit_valid());
}
