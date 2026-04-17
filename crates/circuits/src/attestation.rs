use crate::blake::blake;
use crate::context::Context;
use crate::ivalue::qm31_from_u32s;
use crate::ops::{eq, guess, output};
use crate::poseidon2::poseidon2_hash_two;
use stwo::core::fields::qm31::QM31;

pub const ATTESTATION_LEN: usize = 32;
const TX_ID_WIDTH: usize = 10;
const USER_ID_WIDTH: usize = 10;
const AMOUNT_WIDTH: usize = 12;

pub fn attestation_bytes(tx_id: u64, to_user_id: u64, amount: u64) -> [u8; ATTESTATION_LEN] {
    let s = format!(
        "{:0>width_tx$}{:0>width_user$}{:0>width_amount$}",
        tx_id,
        to_user_id,
        amount,
        width_tx = TX_ID_WIDTH,
        width_user = USER_ID_WIDTH,
        width_amount = AMOUNT_WIDTH,
    );
    s.as_bytes().try_into().expect("attestation must be 32 bytes")
}

fn pack_bytes16(bytes: &[u8; 16]) -> QM31 {
    qm31_from_u32s(
        u32::from_le_bytes(bytes[0..4].try_into().unwrap()),
        u32::from_le_bytes(bytes[4..8].try_into().unwrap()),
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        u32::from_le_bytes(bytes[12..16].try_into().unwrap()),
    )
}

/// Compute Poseidon2 commitment natively (same path as inside circuit).
/// h1 = P2(att[0..16], att[16..32]), h2 = P2(h1, blinder) → single QM31.
pub fn compute_attestation_commitment(
    attestation: &[u8; ATTESTATION_LEN],
    blinder: &[u8; 16],
) -> QM31 {
    let mut ctx = Context::<QM31>::default();
    let att0 = ctx.constant(pack_bytes16(attestation[0..16].try_into().unwrap()));
    let att1 = ctx.constant(pack_bytes16(attestation[16..32].try_into().unwrap()));
    let b = ctx.constant(pack_bytes16(blinder));
    let h1 = poseidon2_hash_two(&mut ctx, att0, att1);
    let h2 = poseidon2_hash_two(&mut ctx, h1, b);
    ctx.get(h2)
}

pub fn build_attestation_circuit(
    attestation: &[u8; ATTESTATION_LEN],
    blinder: &[u8; 16],
    commitment: QM31,
    tx_id: u64,
    to_user_id: u64,
    amount: u64,
) -> Context<QM31> {
    let mut ctx = Context::<QM31>::default();

    // Private witnesses: the two halves of attestation and the blinder.
    let att0_var = guess(&mut ctx, pack_bytes16(attestation[0..16].try_into().unwrap()));
    let att1_var = guess(&mut ctx, pack_bytes16(attestation[16..32].try_into().unwrap()));
    let blinder_var = guess(&mut ctx, pack_bytes16(blinder));

    // Constrain attestation fields match public tx data.
    let expected_att = attestation_bytes(tx_id, to_user_id, amount);
    let expected_att0 = ctx.constant(pack_bytes16(expected_att[0..16].try_into().unwrap()));
    let expected_att1 = ctx.constant(pack_bytes16(expected_att[16..32].try_into().unwrap()));
    eq(&mut ctx, att0_var, expected_att0);
    eq(&mut ctx, att1_var, expected_att1);

    // Poseidon2: h1 = P2(att0, att1), h2 = P2(h1, blinder).
    let h1 = poseidon2_hash_two(&mut ctx, att0_var, att1_var);
    let h2 = poseidon2_hash_two(&mut ctx, h1, blinder_var);

    // Constrain Poseidon2 hash matches public commitment.
    let commitment_var = ctx.constant(commitment);
    eq(&mut ctx, h2, commitment_var);

    // Public outputs: [0] poseidon2_commitment, [1] tx_id, [2] to_user_id, [3] amount.
    let tx_id_var = ctx.constant(qm31_from_u32s(tx_id as u32, 0, 0, 0));
    let to_user_id_var = ctx.constant(qm31_from_u32s(to_user_id as u32, 0, 0, 0));
    let amount_var = ctx.constant(qm31_from_u32s(amount as u32, 0, 0, 0));
    output(&mut ctx, commitment_var);
    output(&mut ctx, tx_id_var);
    output(&mut ctx, to_user_id_var);
    output(&mut ctx, amount_var);

    ctx.finalize_guessed_vars();
    ctx
}

pub fn pad_attestation_blake_rows(ctx: &mut Context<QM31>) {
    const N_LANES: usize = 16;
    let zero = ctx.zero();

    let n_constants = ctx.constants().len();
    let n_hash_compressions = (n_constants + 3) / 4;

    let mut extra = 0usize;
    loop {
        let total_compressions = n_hash_compressions + extra;
        let rounded = ((total_compressions + N_LANES - 1) / N_LANES).max(1) * N_LANES;
        let pad_count = rounded - total_compressions;
        let total_gates = 1 + extra + pad_count;
        if total_gates >= N_LANES {
            break;
        }
        extra += 1;
    }

    for _ in 0..extra {
        let out = blake(ctx, &[zero], 1);
        ctx.mark_as_maybe_unused(&out.0);
        ctx.mark_as_maybe_unused(&out.1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attestation_bytes_format() {
        let att = attestation_bytes(1, 3, 25);
        assert_eq!(std::str::from_utf8(&att).unwrap(), "00000000010000000003000000000025");
    }

    #[test]
    fn test_commitment_deterministic() {
        let att = attestation_bytes(1, 3, 25);
        let blinder = [1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let c1 = compute_attestation_commitment(&att, &blinder);
        let c2 = compute_attestation_commitment(&att, &blinder);
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_wrong_attestation_different_commitment() {
        let blinder = [1u8; 16];
        let h1 = compute_attestation_commitment(&attestation_bytes(1, 3, 25), &blinder);
        let h2 = compute_attestation_commitment(&attestation_bytes(999, 3, 25), &blinder);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_build_attestation_circuit() {
        let attestation = attestation_bytes(1, 3, 25);
        let blinder = [1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let commitment = compute_attestation_commitment(&attestation, &blinder);
        let ctx = build_attestation_circuit(&attestation, &blinder, commitment, 1, 3, 25);
        ctx.check_vars_used();
    }
}
