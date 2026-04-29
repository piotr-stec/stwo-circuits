use crate::context::Context;
use crate::ivalue::qm31_from_u32s;
use crate::ops::{Guess, eq, guess};
use crate::poseidon2::poseidon2_hash_two;

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
