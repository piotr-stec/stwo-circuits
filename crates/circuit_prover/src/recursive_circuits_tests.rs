use crate::prover::{BaseColumnPool, CircuitProof, CircuitProofKeccak, SimdBackend, prove_circuit_assignment, prove_circuit_assignment_keccak, verify_stwo_proof, verify_stwo_proof_keccak};
use circuit_air::statement::all_circuit_components;
use circuit_common::preprocessed::PreprocessedCircuit;
use circuits::blake::{HashValue, blake, blake_qm31};
use circuits::context::{Context, Var};
use circuits::eval;
use circuits::ivalue::qm31_from_u32s;
use circuits::ops::guess;
use circuits::ops::{Guess, cond_flip, eq as eq_op, output};
use circuits_stark_verifier::proof::ProofConfig;
use circuits_stark_verifier::statement::Statement;
use circuits_stark_verifier::verify::verify;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::backend::Column;
use stwo::prover::poly::circle::PolyOps;

const COMPOSITION_POLYNOMIAL_LOG_DEGREE_BOUND: u32 = 1;

// Update these after first run (the test prints actual values).
const NULL_CIRCUIT_ROOT_U32: [u32; 8] =
    [785648638, 1731010165, 144143747, 1044492678, 1729483117, 1059943257, 1108214134, 803902716];
const DEPOSIT_CIRCUIT_ROOT_U32: [u32; 8] =
    [2036214275, 1713163695, 518757843, 1514686217, 199145711, 84908060, 1310120495, 1453963251];
// Recursive circuit roots for specific aggregation shapes.
const RECURSIVE_NULL_PLUS_ONE_DEPOSIT_ROOT_U32: [u32; 8] =
    [819300817, 382718911, 704395743, 121210230, 1152059688, 2016326908, 1846463127, 1040581191];

const RECURSIVE_NULL_PLUS_TWO_DEPOSITS_ROOT_U32: [u32; 8] =
    [1712347555, 1940789204, 473716174, 700344975, 1040847960, 217071097, 1677615127, 1983603390];

struct ProofBundle {
    preprocessed: PreprocessedCircuit,
    preprocessed_root: HashValue<QM31>,
    proof: CircuitProof,
}

struct ProofBundleKeccak {
    preprocessed: PreprocessedCircuit,
    preprocessed_root: HashValue<QM31>,
    proof: CircuitProofKeccak,
}

fn root_from_u32s(words: [u32; 8]) -> HashValue<QM31> {
    HashValue(
        qm31_from_u32s(words[0], words[1], words[2], words[3]),
        qm31_from_u32s(words[4], words[5], words[6], words[7]),
    )
}

fn compute_preprocessed_root(
    preprocessed: &PreprocessedCircuit,
    pcs_config: &stwo::core::pcs::PcsConfig,
) -> HashValue<QM31> {
    let trace_log_size = preprocessed.params.trace_log_size;
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            trace_log_size
                + std::cmp::max(
                    pcs_config.fri_config.log_blowup_factor,
                    COMPOSITION_POLYNOMIAL_LOG_DEGREE_BOUND,
                ),
        )
        .circle_domain()
        .half_coset,
    );
    let preprocessed_trace = preprocessed.preprocessed_trace.get_trace::<SimdBackend>();
    let preprocessed_trace_polys = SimdBackend::interpolate_columns(preprocessed_trace, &twiddles);

    let store_polynomials_coefficients = true;
    let preprocessed_tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        preprocessed_trace_polys,
        pcs_config.fri_config.log_blowup_factor,
        &twiddles,
        store_polynomials_coefficients,
        pcs_config.lifting_log_size,
        &BaseColumnPool::<SimdBackend>::new(),
    );

    let root = preprocessed_tree.commitment.layers[0].at(0);
    root.into()
}

fn blake_hash_4(context: &mut Context<QM31>, a: Var, b: Var, c: Var, d: Var) -> HashValue<Var> {
    blake(context, &[a, b, c, d], 64)
}

fn enforce_bit(context: &mut Context<QM31>, bit: Var) {
    let one = context.one();
    let expr = eval!(context, (bit) * ((bit) - (one)));
    eq_op(context, expr, context.zero());
}

// Circuit to prove: given a Merkle root and token, show knowledge of a path to a leaf with that
// root and token, and output the amount in that leaf. The allowlist circuit will only allow proofs
// with certain roots (e.g. from deposits or previous recursive proofs).
fn build_deposit_context(
    amount: QM31,
    token: QM31,
    secret: QM31,
    nullifier: QM31,
    path_bits: &[QM31],
    siblings: &[HashValue<QM31>],
    root: HashValue<QM31>,
) -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    // Private inputs (witness).
    let amount_v = guess(&mut context, amount);
    let token_v = guess(&mut context, token);
    let secret_v = guess(&mut context, secret);
    let nullifier_v = guess(&mut context, nullifier);

    let bit_vars = path_bits.iter().map(|b| guess(&mut context, *b)).collect::<Vec<_>>();
    for bit in &bit_vars {
        enforce_bit(&mut context, *bit);
    }

    let sibling_vars = siblings.iter().map(|s| s.guess(&mut context)).collect::<Vec<_>>();
    let root_v = root.guess(&mut context);

    // rebuild Leaf = H(secret, nullifier, amount, token).
    // Leaf = H(secret, nullifier, amount, token).
    let mut node = blake_hash_4(&mut context, secret_v, nullifier_v, amount_v, token_v);

    // Walk the Merkle path to rebuild root, using path bits to select the order of hashing with
    // siblings.
    for (bit_v, sibling_v) in bit_vars.into_iter().zip(sibling_vars.into_iter()) {
        let (left0, right0) = cond_flip(&mut context, bit_v, node.0, sibling_v.0);
        let (left1, right1) = cond_flip(&mut context, bit_v, node.1, sibling_v.1);
        node = blake_hash_4(&mut context, left0, left1, right0, right1);
    }

    // Enforce root match (public input).
    eq_op(&mut context, node.0, root_v.0);
    eq_op(&mut context, node.1, root_v.1);

    // Public outputs: amount, token, root.
    output(&mut context, amount_v);
    output(&mut context, token_v);
    output(&mut context, root_v.0);
    output(&mut context, root_v.1);

    context
}

fn build_recursive_context(
    preprocessed_proof_a: &PreprocessedCircuit,
    circuit_proof_proof_a: CircuitProof,
    preprocessed_proof_b: &PreprocessedCircuit,
    circuit_proof_proof_b: CircuitProof,
) -> Context<QM31> {
    let mut recursive_context = Context::<QM31>::default();
    let outputs_a =
        verify_proof_allowlist(&mut recursive_context, preprocessed_proof_a, circuit_proof_proof_a);
    let outputs_b =
        verify_proof_allowlist(&mut recursive_context, preprocessed_proof_b, circuit_proof_proof_b);

    let total = eval!(&mut recursive_context, (outputs_a[0]) + (outputs_b[0]));
    output(&mut recursive_context, total);

    recursive_context
}

fn build_null_context(token: QM31, root: HashValue<QM31>) -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    // Null proof outputs a zero total and anchors token/root.
    let total_v = guess(&mut context, qm31_from_u32s(0, 0, 0, 0));
    let token_v = guess(&mut context, token);
    let root_v = root.guess(&mut context);

    output(&mut context, total_v);
    output(&mut context, token_v);
    output(&mut context, root_v.0);
    output(&mut context, root_v.1);

    context
}

struct AllowlistCircuitStatement {
    inner: circuit_air::statement::CircuitStatement<QM31>,
    allowed_roots: Vec<HashValue<QM31>>,
    selector_values: Vec<QM31>,
}

impl Statement<QM31> for AllowlistCircuitStatement {
    fn claims_to_mix(&self, context: &mut Context<QM31>) -> Vec<Vec<Var>> {
        <circuit_air::statement::CircuitStatement<QM31> as Statement<QM31>>::claims_to_mix(
            &self.inner,
            context,
        )
    }

    fn get_components(
        &self,
    ) -> &[Box<dyn circuits_stark_verifier::constraint_eval::CircuitEval<QM31>>] {
        self.inner.get_components()
    }

    fn public_logup_sum(
        &self,
        context: &mut Context<QM31>,
        interaction_elements: [Var; 2],
        claim: &circuits_stark_verifier::proof::Claim<Var>,
    ) -> Var {
        <circuit_air::statement::CircuitStatement<QM31> as Statement<QM31>>::public_logup_sum(
            &self.inner,
            context,
            interaction_elements,
            claim,
        )
    }

    fn get_preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        self.inner.get_preprocessed_column_ids()
    }

    fn verify_preprocessed_root(
        &self,
        context: &mut Context<QM31>,
        preprocessed_root: HashValue<Var>,
    ) {
        // Bootstrap mode: if consts are zero, skip the check and only log roots.
        let all_zero = NULL_CIRCUIT_ROOT_U32 == [0; 8]
            && DEPOSIT_CIRCUIT_ROOT_U32 == [0; 8]
            && RECURSIVE_NULL_PLUS_ONE_DEPOSIT_ROOT_U32 == [0; 8]
            && RECURSIVE_NULL_PLUS_TWO_DEPOSITS_ROOT_U32 == [0; 8];
        if all_zero {
            return;
        }

        let selectors = self
            .selector_values
            .iter()
            .map(|v| guess(context, *v))
            .collect::<Vec<_>>();
        for bit in &selectors {
            enforce_bit(context, *bit);
        }

        // Enforce one-hot selection.
        let mut sum = context.zero();
        for bit in &selectors {
            sum = eval!(context, (sum) + (*bit));
        }
        eq_op(context, sum, context.one());

        let mut expected0 = context.zero();
        let mut expected1 = context.zero();
        for (sel, root) in selectors.iter().zip(self.allowed_roots.iter()) {
            let r0 = context.constant(root.0);
            let r1 = context.constant(root.1);
            expected0 = eval!(context, (expected0) + ((*sel) * (r0)));
            expected1 = eval!(context, (expected1) + ((*sel) * (r1)));
        }

        eq_op(context, preprocessed_root.0, expected0);
        eq_op(context, preprocessed_root.1, expected1);
    }
}

fn verify_proof_allowlist(
    context: &mut Context<QM31>,
    preprocessed: &PreprocessedCircuit,
    circuit_proof: CircuitProof,
) -> Vec<Var> {
    let preprocessed_column_ids = preprocessed.preprocessed_trace.ids();
    let proof_config = ProofConfig::from_components(
        &all_circuit_components::<QM31>(),
        preprocessed_column_ids.len(),
        &circuit_proof.pcs_config,
        circuit_air::statement::INTERACTION_POW_BITS,
    );
    let (proof, public_data) =
        crate::prover::preprare_circuit_proof_for_circuit_verifier(circuit_proof, &proof_config);
    let inner = circuit_air::statement::CircuitStatement::new(
        context,
        &preprocessed.params.output_addresses,
        &public_data.output_values,
        preprocessed.params.n_blake_gates,
        preprocessed_column_ids,
        root_from_u32s(DEPOSIT_CIRCUIT_ROOT_U32),
    );
    let proof_root = proof.preprocessed_root;
    let allowed_roots = vec![
        root_from_u32s(NULL_CIRCUIT_ROOT_U32),
        root_from_u32s(DEPOSIT_CIRCUIT_ROOT_U32),
        root_from_u32s(RECURSIVE_NULL_PLUS_ONE_DEPOSIT_ROOT_U32),
        root_from_u32s(RECURSIVE_NULL_PLUS_TWO_DEPOSITS_ROOT_U32),
    ];
    let mut selector_values = vec![qm31_from_u32s(0, 0, 0, 0); allowed_roots.len()];
    if let Some(idx) = allowed_roots.iter().position(|r| *r == proof_root) {
        selector_values[idx] = qm31_from_u32s(1, 0, 0, 0);
    } else {
        panic!("proof preprocessed root not in allowlist");
    };
    let statement = AllowlistCircuitStatement { inner, allowed_roots, selector_values };
    let proof_vars = proof.guess(context);
    verify(context, &proof_vars, &proof_config, &statement);
    statement.inner.output_values.clone()
}

fn make_bundle(mut context: Context<QM31>) -> ProofBundle {
    context.finalize_guessed_vars();
    context.validate_circuit();
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let proof = prove_circuit_assignment(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    let preprocessed_root = compute_preprocessed_root(&preprocessed, &proof.pcs_config);
    ProofBundle { preprocessed, preprocessed_root, proof }
}

fn make_bundle_keccak(mut context: Context<QM31>) -> ProofBundleKeccak {
    context.finalize_guessed_vars();
    context.validate_circuit();
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let proof = prove_circuit_assignment_keccak(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    let preprocessed_root = compute_preprocessed_root(&preprocessed, &proof.pcs_config);
    ProofBundleKeccak { preprocessed, preprocessed_root, proof }
}

#[test]
fn test_recursive_allowlist_flow() {
    // Build a small Merkle tree (depth 4) and 2 deposits.
    let token = qm31_from_u32s(99, 0, 0, 0);
    const DEPTH: usize = 4;
    const N_LEAVES: usize = 1 << DEPTH;

    let deposits = (0..N_LEAVES)
        .map(|i| {
            (
                qm31_from_u32s((i as u32 + 1) * 10, 0, 0, 0),
                qm31_from_u32s(100 + i as u32, 0, 0, 0),
                qm31_from_u32s(200 + i as u32, 0, 0, 0),
            )
        })
        .collect::<Vec<_>>();

    let leaves = deposits
        .iter()
        .map(|(amount, secret, nullifier)| blake_qm31(&[*secret, *nullifier, *amount, token], 64))
        .collect::<Vec<_>>();

    let mut levels: Vec<Vec<HashValue<QM31>>> = Vec::with_capacity(DEPTH + 1);
    levels.push(leaves.clone());
    for d in 0..DEPTH {
        let prev = &levels[d];
        let mut next = Vec::with_capacity(prev.len() / 2);
        for i in (0..prev.len()).step_by(2) {
            next.push(blake_qm31(&[prev[i].0, prev[i].1, prev[i + 1].0, prev[i + 1].1], 64));
        }
        levels.push(next);
    }
    let root = levels[DEPTH][0];

    let make_deposit = |idx: usize| {
        let (amount, secret, nullifier) = deposits[idx];
        let mut path_bits = Vec::with_capacity(DEPTH);
        let mut siblings = Vec::with_capacity(DEPTH);
        let mut i = idx;
        for d in 0..DEPTH {
            let bit = (i & 1) as u32;
            path_bits.push(qm31_from_u32s(bit, 0, 0, 0));
            let sib_idx = i ^ 1;
            siblings.push(levels[d][sib_idx]);
            i >>= 1;
        }
        build_deposit_context(amount, token, secret, nullifier, &path_bits, &siblings, root)
    };

    let deposit_a = make_bundle(make_deposit(0));
    let deposit_b = make_bundle(make_deposit(1));
    let null_bundle = make_bundle(build_null_context(token, root));

    // Log roots to update consts on first run.
    println!("Computed NULL root: {:?}", null_bundle.preprocessed_root);
    println!("Computed DEPOSIT root: {:?}", deposit_a.preprocessed_root);

    // Recursive step: allowlist NULL/DEPOSIT/RECURSIVE in the verifier circuit.
    let mut recursive_context = Context::<QM31>::default();
    let prev_outputs = verify_proof_allowlist(
        &mut recursive_context,
        &null_bundle.preprocessed,
        null_bundle.proof,
    );
    let curr_outputs =
        verify_proof_allowlist(&mut recursive_context, &deposit_a.preprocessed, deposit_a.proof);

    let total = eval!(&mut recursive_context, (prev_outputs[0]) + (curr_outputs[0]));
    output(&mut recursive_context, total);

    let recursive_bundle = make_bundle(recursive_context);
    println!("Computed RECURSIVE root: {:?}", recursive_bundle.preprocessed_root);

    // Second recursive step: recursive + deposit.
    let mut recursive_context_2 = Context::<QM31>::default();
    let prev_outputs_2 = verify_proof_allowlist(
        &mut recursive_context_2,
        &recursive_bundle.preprocessed,
        recursive_bundle.proof,
    );
    let curr_outputs_2 =
        verify_proof_allowlist(&mut recursive_context_2, &deposit_b.preprocessed, deposit_b.proof);

    let total_2 = eval!(&mut recursive_context_2, (prev_outputs_2[0]) + (curr_outputs_2[0]));
    output(&mut recursive_context_2, total_2);

    let _recursive_bundle_2 = make_bundle(recursive_context_2);

    // Enforce const roots once you fill them in.
    if NULL_CIRCUIT_ROOT_U32 != [0; 8] {
        assert_eq!(root_from_u32s(NULL_CIRCUIT_ROOT_U32), null_bundle.preprocessed_root);
        assert_eq!(root_from_u32s(DEPOSIT_CIRCUIT_ROOT_U32), deposit_a.preprocessed_root);
        assert_eq!(
            root_from_u32s(RECURSIVE_NULL_PLUS_ONE_DEPOSIT_ROOT_U32),
            recursive_bundle.preprocessed_root
        );
    }
}

#[test]
fn test_recursive_two_deposits() {
    // Mock token
    let token = qm31_from_u32s(99, 0, 0, 0);

    // First deposit data
    let amount_a = qm31_from_u32s(55, 0, 0, 0);
    let secret_a = qm31_from_u32s(200, 0, 0, 0);
    let nullifier_a = qm31_from_u32s(300, 0, 0, 0);

    // Second deposit data
    let amount_b = qm31_from_u32s(55, 0, 0, 0);
    let secret_b = qm31_from_u32s(200, 0, 0, 0);
    let nullifier_b = qm31_from_u32s(300, 0, 0, 0);

    // Third deposit data (used in an extra recursive step).
    let amount_c = qm31_from_u32s(25, 0, 0, 0);
    let secret_c = qm31_from_u32s(700, 0, 0, 0);
    let nullifier_c = qm31_from_u32s(900, 0, 0, 0);

    // Fourth deposit data (used in the final recursive step).
    let amount_d = qm31_from_u32s(15, 0, 0, 0);
    let secret_d = qm31_from_u32s(1100, 0, 0, 0);
    let nullifier_d = qm31_from_u32s(1300, 0, 0, 0);

    // Build a real Merkle tree with default (empty) leaves, then insert four deposits.
    const DEPTH: usize = 4;
    const N_LEAVES: usize = 1 << DEPTH;

    println!("N leaves: {}", N_LEAVES);
    // Default (empty) leaf used to initialize the entire tree.
    let empty_leaf = blake_qm31(
        &[
            qm31_from_u32s(0, 0, 0, 0),
            qm31_from_u32s(0, 0, 0, 0),
            qm31_from_u32s(0, 0, 0, 0),
            token,
        ],
        64,
    );

    // Level 0: all leaves (initially all empty).
    let mut leaves = vec![empty_leaf; N_LEAVES];
    let idx_a = 3usize;
    let idx_b = 10usize;
    let idx_c = 12usize;
    let idx_d = 14usize;
    // "Adding" deposits to the tree = replacing positions in the leaf array.
    leaves[idx_a] = blake_qm31(&[secret_a, nullifier_a, amount_a, token], 64);
    leaves[idx_b] = blake_qm31(&[secret_b, nullifier_b, amount_b, token], 64);
    leaves[idx_c] = blake_qm31(&[secret_c, nullifier_c, amount_c, token], 64);
    leaves[idx_d] = blake_qm31(&[secret_d, nullifier_d, amount_d, token], 64);

    // Rebuild the tree bottom-up:
    // levels[0] = leaves, levels[1] = parents, ..., levels[DEPTH] = root.
    let mut levels: Vec<Vec<HashValue<QM31>>> = Vec::with_capacity(DEPTH + 1);
    levels.push(leaves);
    for d in 0..DEPTH {
        let prev = &levels[d];
        let mut next = Vec::with_capacity(prev.len() / 2);
        // Each neighboring pair at level d is hashed into one node at level d+1.
        for i in (0..prev.len()).step_by(2) {
            next.push(blake_qm31(&[prev[i].0, prev[i].1, prev[i + 1].0, prev[i + 1].1], 64));
        }
        levels.push(next);
    }
    // After full rebuild, the root is the single element in the last level.
    let root = levels[DEPTH][0];

    // Reconstruct Merkle path for a leaf at index idx:
    // - path_bits: whether the node is left/right at each level,
    // - siblings: sibling hash at each level.
    let build_path = |idx: usize| {
        let mut path_bits = Vec::with_capacity(DEPTH);
        let mut siblings = Vec::with_capacity(DEPTH);
        let mut i = idx;
        for d in 0..DEPTH {
            path_bits.push(qm31_from_u32s((i & 1) as u32, 0, 0, 0));
            siblings.push(levels[d][i ^ 1]);
            // Move to parent at the next level.
            i >>= 1;
        }
        (path_bits, siblings)
    };

    let (path_bits_a, siblings_a) = build_path(idx_a);
    let (path_bits_b, siblings_b) = build_path(idx_b);
    let (path_bits_c, siblings_c) = build_path(idx_c);
    let (path_bits_d, siblings_d) = build_path(idx_d);

    // Prove both deposits
    let proof_deposit_a = make_bundle(build_deposit_context(
        amount_a,
        token,
        secret_a,
        nullifier_a,
        &path_bits_a,
        &siblings_a,
        root,
    ));
    println!(
        "proof_deposit_a outputs len: {} values: {:?}",
        proof_deposit_a.proof.claim.output_values.len(),
        proof_deposit_a.proof.claim.output_values
    );
    let proof_deposit_b = make_bundle(build_deposit_context(
        amount_b,
        token,
        secret_b,
        nullifier_b,
        &path_bits_b,
        &siblings_b,
        root,
    ));
    println!(
        "proof_deposit_b outputs len: {} values: {:?}",
        proof_deposit_b.proof.claim.output_values.len(),
        proof_deposit_b.proof.claim.output_values
    );
    let proof_deposit_c = make_bundle(build_deposit_context(
        amount_c,
        token,
        secret_c,
        nullifier_c,
        &path_bits_c,
        &siblings_c,
        root,
    ));
    println!(
        "proof_deposit_c outputs len: {} values: {:?}",
        proof_deposit_c.proof.claim.output_values.len(),
        proof_deposit_c.proof.claim.output_values
    );
    let proof_deposit_d = make_bundle(build_deposit_context(
        amount_d,
        token,
        secret_d,
        nullifier_d,
        &path_bits_d,
        &siblings_d,
        root,
    ));
    println!(
        "proof_deposit_d outputs len: {} values: {:?}",
        proof_deposit_d.proof.claim.output_values.len(),
        proof_deposit_d.proof.claim.output_values
    );

    // Create null circuit for init of recursive flow
    let proof_null = make_bundle(build_null_context(token, root));

    // Now we have 5 proofs - 1 init null proof and 4 deposit proofs.F

    // First recursive step: null + deposit_a -> recursive_a.
    let recursive_context_a = build_recursive_context(
        &proof_null.preprocessed,
        proof_null.proof,
        &proof_deposit_a.preprocessed,
        proof_deposit_a.proof,
    );

    let recursive_null_and_deposit_a = make_bundle(recursive_context_a);
    println!(
        "recursive_null_and_deposit_a preprocessed root: {:?}",
        recursive_null_and_deposit_a.preprocessed_root
    );
    println!(
        "recursive_null_and_deposit_a outputs len: {} values: {:?}",
        recursive_null_and_deposit_a.proof.claim.output_values.len(),
        recursive_null_and_deposit_a.proof.claim.output_values
    );

    // Second recursive step: recursive_a + deposit_b -> recursive_ab.
    let recursive_context_ab = build_recursive_context(
        &recursive_null_and_deposit_a.preprocessed,
        recursive_null_and_deposit_a.proof,
        &proof_deposit_b.preprocessed,
        proof_deposit_b.proof,
    );

    let recursive_ab_bundle = make_bundle(recursive_context_ab);
    println!(
        "recursive_ab preprocessed root: {:?}",
        recursive_ab_bundle.preprocessed_root
    );

    println!(
        "recursive_ab outputs len: {} values: {:?}",
        recursive_ab_bundle.proof.claim.output_values.len(),
        recursive_ab_bundle.proof.claim.output_values
    );

    // Third recursive step: recursive_ab + deposit_c -> recursive_abc.
    let recursive_context_abc = build_recursive_context(
        &recursive_ab_bundle.preprocessed,
        recursive_ab_bundle.proof,
        &proof_deposit_c.preprocessed,
        proof_deposit_c.proof,
    );

    let recursive_abc_bundle = make_bundle(recursive_context_abc);
    println!(
        "recursive_abc preprocessed root: {:?}",
        recursive_abc_bundle.preprocessed_root
    );
    println!(
        "recursive_abc outputs len: {} values: {:?}",
        recursive_abc_bundle.proof.claim.output_values.len(),
        recursive_abc_bundle.proof.claim.output_values
    );

    // Fourth recursive step: recursive_abc + deposit_d -> recursive_abcd.
    let recursive_context_abcd = build_recursive_context(
        &recursive_abc_bundle.preprocessed,
        recursive_abc_bundle.proof,
        &proof_deposit_d.preprocessed,
        proof_deposit_d.proof,
    );

    let recursive_abcd_bundle = make_bundle_keccak(recursive_context_abcd);
    println!(
        "recursive_abcd preprocessed root: {:?}",
        recursive_abcd_bundle.preprocessed_root
    );
    println!(
        "recursive_abcd outputs len: {} values: {:?}",
        recursive_abcd_bundle.proof.claim.output_values.len(),
        recursive_abcd_bundle.proof.claim.output_values
    );

    // From the second recursive step onward, the circuit shape stabilizes.
    assert_eq!(
        recursive_ab_bundle.preprocessed_root,
        recursive_abc_bundle.preprocessed_root
    );
    assert_eq!(
        recursive_ab_bundle.preprocessed_root,
        recursive_abcd_bundle.preprocessed_root
    );

    verify_stwo_proof_keccak(&recursive_abcd_bundle.preprocessed, recursive_abcd_bundle.proof);
}
