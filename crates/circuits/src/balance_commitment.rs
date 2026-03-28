use stwo::core::fields::qm31::QM31;

use crate::blake::{HashValue, blake, blake_qm31};
use crate::context::Context;
use crate::ivalue::qm31_from_u32s;
use crate::ops::{eq, guess, output};

#[cfg(test)]
#[path = "balance_commitment_test.rs"]
mod test;

pub const COMMITTED_PART_LEN: usize = 12;

/// Packs 12 ASCII bytes into a QM31.
///
/// Layout: `coord0 = bytes[0..4]`, `coord1 = bytes[4..8]`, `coord2 = bytes[8..12]`, `coord3 = 0`.
pub fn pack_balance_str(bytes: &[u8; COMMITTED_PART_LEN]) -> QM31 {
    qm31_from_u32s(
        u32::from_le_bytes(bytes[0..4].try_into().unwrap()),
        u32::from_le_bytes(bytes[4..8].try_into().unwrap()),
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        0,
    )
}

/// Packs 16 blinder bytes into a QM31.
pub fn pack_blinder(bytes: &[u8; 16]) -> QM31 {
    qm31_from_u32s(
        u32::from_le_bytes(bytes[0..4].try_into().unwrap()),
        u32::from_le_bytes(bytes[4..8].try_into().unwrap()),
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        u32::from_le_bytes(bytes[12..16].try_into().unwrap()),
    )
}

pub fn compute_commitment(
    balance_str: &[u8; COMMITTED_PART_LEN],
    blinder: &[u8; 16],
) -> HashValue<QM31> {
    blake_qm31(&[pack_balance_str(balance_str), pack_blinder(blinder)], 32)
}


pub fn build_balance_commitment_circuit(
    balance_str: &[u8; COMMITTED_PART_LEN],
    blinder: &[u8; 16],
    committed_hash: HashValue<QM31>,
) -> Context<QM31> {
    let mut ctx = Context::<QM31>::default();

    // Private inputs
    let balance_var = guess(&mut ctx, pack_balance_str(balance_str));
    let blinder_var = guess(&mut ctx, pack_blinder(blinder));

    // Compute hash inside the circuit
    let hash_out = blake(&mut ctx, &[balance_var, blinder_var], 32);

    // Constrain computed hash == public committed_hash
    let committed0 = guess(&mut ctx, committed_hash.0);
    let committed1 = guess(&mut ctx, committed_hash.1);
    eq(&mut ctx, hash_out.0, committed0);
    eq(&mut ctx, hash_out.1, committed1);

    // Public outputs
    output(&mut ctx, committed0);
    output(&mut ctx, committed1);

    ctx.finalize_guessed_vars();
    ctx
}
