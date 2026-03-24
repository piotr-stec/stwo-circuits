use num_traits::Zero;
use stwo::core::fields::qm31::QM31;

use crate::{context::Context, ops::{cond_flip, eq, guess, mul, output, sub}};

pub fn build_merkle_membership_context(depth: usize) -> Context<QM31> {
    let mut context = Context::<QM31>::default();
    let one = context.one();
    let zero = context.zero();

    let leaf = guess(&mut context, QM31::zero());
    let mut curr = leaf;

    for _level in 0..depth {
        let bit = guess(&mut context, QM31::zero());
        let sibling = guess(&mut context, QM31::zero());

        let bit_minus_one = sub(&mut context, bit, one);
        let bit_is_binary = mul(&mut context, bit, bit_minus_one);
        eq(&mut context, bit_is_binary, zero);

        let (left, right) = cond_flip(&mut context, bit, curr, sibling);

        // Compress one Merkle level with Poseidon2 over the same context.
        curr = crate::poseidon2::poseidon2_hash_two(&mut context, left, right);
    }

    let root_value = context.get(curr);
    let root = guess(&mut context, root_value);
    eq(&mut context, curr, root);
    output(&mut context, root);

    context.finalize_guessed_vars();

    context
}

#[cfg(test)]
#[path = "merkle_membership_test.rs"]
mod test;