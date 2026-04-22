use crate::context::Context;
use crate::ivalue::qm31_from_u32s;
use crate::ops::{Guess, eq, guess};
use crate::poseidon2::{poseidon2_hash_two, poseidon2_value, poseidon2_value_full, poseidon_gate};

#[test]
fn test_poseidon2_hash_two_7_42() {
    let mut context = Context::default();
    let a = qm31_from_u32s(7, 0, 0, 0).guess(&mut context);
    let b = qm31_from_u32s(42, 0, 0, 0).guess(&mut context);

    let out = poseidon2_hash_two(&mut context, a, b);
    let expected = guess(&mut context, qm31_from_u32s(430726115, 0, 0, 0));
    eq(&mut context, out, expected);

    context.finalize_guessed_vars();
    assert!(context.is_circuit_valid());
}

#[test]
fn test_poseidon2_value_full_matches_reference() {
    use stwo::core::fields::m31::M31;
    let a = M31::from_u32_unchecked(7);
    let b = M31::from_u32_unchecked(42);

    // state[0] must match the known reference output
    let [s0, _, _, _] = poseidon2_value_full(a, b);
    assert_eq!(s0, poseidon2_value(a, b));
    assert_eq!(s0, M31::from_u32_unchecked(430726115));

    // poseidon2_value is just a wrapper — consistency check
    assert_eq!(poseidon2_value(a, b), poseidon2_value_full(a, b)[0]);
}

#[test]
fn test_poseidon_gate_consistent_with_hash_two() {
    use stwo::core::fields::qm31::QM31;
    let a_val = qm31_from_u32s(7, 0, 0, 0);
    let b_val = qm31_from_u32s(42, 0, 0, 0);

    // poseidon_gate output: state[0..3] packed as QM31
    let mut ctx1 = Context::<QM31>::default();
    let a1 = a_val.guess(&mut ctx1);
    let b1 = b_val.guess(&mut ctx1);
    let gate_out = poseidon_gate(&mut ctx1, a1, b1);
    let gate_val = ctx1.get(gate_out);

    // poseidon2_hash_two output: only state[0] as QM31 scalar
    let mut ctx2 = Context::<QM31>::default();
    let a2 = a_val.guess(&mut ctx2);
    let b2 = b_val.guess(&mut ctx2);
    let hash_two_out = poseidon2_hash_two(&mut ctx2, a2, b2);
    let hash_two_val = ctx2.get(hash_two_out);

    // state[0] must match between both
    assert_eq!(gate_val.0.0, hash_two_val.0.0, "state[0] mismatch");
    // poseidon_gate additionally exposes state[1..3] in upper limbs
    let [s0, s1, s2, s3] = poseidon2_value_full(
        stwo::core::fields::m31::M31::from_u32_unchecked(7),
        stwo::core::fields::m31::M31::from_u32_unchecked(42),
    );
    assert_eq!(gate_val, qm31_from_u32s(s0.0, s1.0, s2.0, s3.0));
    assert_eq!(hash_two_val, qm31_from_u32s(s0.0, 0, 0, 0));
}
