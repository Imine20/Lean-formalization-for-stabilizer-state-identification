# Independent review of Lüders verification

Date: 2026-10-11. Reviewed source commit: `5814058d2dff6e999236f2669e07a127c974a4cb`.
Comparison baseline: `ce043d6`. Pinned toolchain: `leanprover/lean4:v4.24.0`.
The review was performed in the separate cloud directory `/data/lean/tasks/verification-born`, on branch `codex/verification-review`. Neither the integration directory nor any committed Lean source was modified.

Conclusion: this snapshot proves the original Lüders outcome average, score one exactly for valid reports, and score at most (1/p) for incorrect reports. Commutativity, completeness of the projector family, and probability bounds are not added as premises of these final theorems. This is a complete proof chain for the verification experiment, not a completed proof of the entire no-copy-rate-discount main theorem.

## Original definitions and quantifiers

An exact Git comparison with the baseline confirms that the following public files are unchanged:
`Main.lean`, `Quantum/Finite.lean`, `Quantum/Pauli.lean`,
`Quantum/Stabilizer.lean`, `FixedConstraints/Task.lean`, and
`FixedConstraints/Rates.lean`.

`verificationPayoff_eq_born` and `verificationPayoff_eq_one_iff_valid` take only the original parameters
`{p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (x : StabilizerState p n) (r : Report W)`.
The incorrect-report bound adds only `¬ Valid W x r` with its original semantics. An auxiliary theorem displaying the intersection spectrum uses a representing label `ℓ` and `labelProjector p n ℓ = x.val`. The final incorrect-report bound obtains this label internally from the original `StabilizerState` definition; it does not require the caller to supply a label, spectrum formula, or inclusion relation.

Reports remain the dependent sum over all subspaces satisfying the original `ReportSubspace W` conditions, together with their full `Assignment`: isotropy, dimension (m), inclusion in Wᗮ, and zero intersection with (W). No canonical subfamily, reference coordinates, or generic-input restriction is selected. The original `Valid` checks the eigenvalue of each Pauli operator on the input state. Exceptional inputs may have several valid reports; the equivalence between score one and validity does not assume uniqueness of a valid report.

Every theorem uses an arbitrary-prime condition, with no odd-prime or positive-dimension requirement. Independent Lean specialization checks covered (p=2,n=m=0), (m=0), (m=n), and (k=0). These are boundary type checks of universal theorems, not finite tests used in place of general proofs. `Learner W k` always ranges over all normalized PSD POVMs on the complete `Fin k → Configuration p n` space. The test copy occurs only in `x.val` within an individual `verificationPayoff` and is not counted in (k).

## Conditional experiment and zero probability

Comparison with lines 438–518 of `paper/main-stabilizer2.tex` confirms that the definition still sums over each measurement outcome `ν : Assignment p n W.subspace`. For positive probability, the term is q_ν times the conditional Born score on the normalized state; for zero probability, it is zero. The conditional score is not directly replaced by the score on the unmeasured state.

`normalizedLudersState` uses the projector laws, input positivity, and trace one to prove that `q⁻¹ • (P * ρ * P)` is an original `DensityMatrix` when `q > 0`. `verificationConditionalScore_mem_Icc` proves membership of the conditional score in `[0,1]` only for positive-probability outcomes. In contrast, `verificationPayoff_eq_born` is an identity after averaging over measurement outcomes `ν`: it is neither an identity for each `ν` nor an average over the input-state prior.

The zero-probability branch first derives Born nonnegativity from positivity, then uses nonpositivity to obtain `q = 0`. The proved `projection_sandwich_eq_zero_of_born_zero` gives `P * ρ * P = 0`, from which the corresponding Born contribution is shown to vanish. Commutativity follows from the original report condition `K ≤ Wᗮ` and actual Pauli multiplication. Completeness comes from `sum_jointProjector` over all original assignments, which internally invokes proved assignment existence.

## Actual recompilation and axiom audit

In the independent directory, the following seven exact source modules were recompiled in dependency order with
`./scripts/lake.sh env lean -o .lake/build/lib/lean/StabilizerLearning/<module>.olean StabilizerLearning/<module>.lean`.
Every process exited with code 0, and all logs contained no warnings or errors:
`Quantum/BornProbability`, `Quantum/TensorProbability`,
`Quantum/ProjectorRelations`, `FixedConstraints/ReportSemantics`,
`Quantum/ProjectorOverlap`, `Quantum/Luders`, and
`FixedConstraints/LudersVerification`.
This was independent module recompilation using the pinned dependency cache; this review does not describe it as a clean whole-project rebuild.

`#print axioms` was actually executed for the following 12 core declarations. Every output was exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new mathematical axiom:

- Quantum: `luders_outcome_eq_born`, `normalizedLudersState`, `conditional_luders_born_mem_Icc`, `luders_average_eq_born`.
- FixedConstraints: `verificationPayoff_eq_born`, `verificationConditionalScore_mem_Icc`, `verificationPayoff_mem_Icc`, `verificationPayoff_eq_one_iff_valid`, `verificationPayoff_eq_one_of_valid`, `verificationPayoff_le_inv_prime_of_not_valid`, `verificationStatewise_eq_born`, `verificationPayoff_eq_intersection_spectrum`.

An independent Scratch audit program read actual constant proof values from the Lean environment, traversed `Expr.getUsedConstants`, and raised an error if any of the following fifteen paths was missing. The final audit file exited with code 0, and every check reported `DEPENDENCY_PATH_OK`:

- `verificationPayoff_eq_born → sum_jointProjector`.
- `verificationPayoff_eq_born → luders_average_eq_born → luders_outcome_eq_born → projection_sandwich_eq_zero_of_born_zero`.
- `verificationPayoff_eq_born → jointProjector_commute_reportProjector`.
- `verificationPayoff_eq_born → sum_jointProjector → nonempty_assignment_of_isIsotropic`.
- `verificationPayoff_le_inv_prime_of_not_valid → born_jointProjector_overlap_le_inv_prime_of_not_correct → born_jointProjector_overlap`.
- The preceding path continues through `trace_jointProjector_overlap → sum_assignment_phase_ratio → AddChar.sum_eq_ite`.
- `verificationPayoff_le_inv_prime_of_not_valid → valid_iff_label_restriction`.
- `verificationPayoff_eq_one_iff_valid → valid_iff_reportProjector_mul_eq_self`.
- `verificationPayoff_eq_one_iff_valid → born_projection_eq_one_iff`.
- `verificationPayoff_mem_Icc → born_projection_mem_Icc`.
- `verificationConditionalScore_mem_Icc → conditional_luders_born_mem_Icc → normalizedLudersState`.
- `verificationPayoff_eq_intersection_spectrum → born_jointProjector_overlap`.
- `verificationStatewise_eq_born → verificationPayoff_eq_born`.
- `normalizedLudersState → normalizedLudersState._proof_2 → trace_mul_eq_ofReal_born_of_posSemidef`.
- `DensityMatrix.tensorPower → DensityMatrix.tensorPower._proof_1 → tensorPower_posSemidef`.

The accompanying [luders-audit-links.json](luders-audit-links.json) gives the full declaration names for these 15 groups. Each `target` is the audited declaration and each `dependency` its actual transitive dependency. These checks were executed and passed and can be incorporated permanently into the whole-project audit.

The audit traversed only project constants occurring in actual values, together with the specified endpoints. It did not treat a name appearing in source text as a proof dependency. Original recompilation results and audit output are preserved in this execution copy at `Scratch/luders-review/build.json`, `audit.log`, and `Review.lean`; they are outside the formal import chain.

## Outstanding acceptance and assessment of remaining work

At exact commit `5814058`, the root import graph reaches `Main` but does not yet reach `Quantum/Luders` or `FixedConstraints/LudersVerification`. The main task still needs to wire these modules into the entry point, run `scripts/check.py`, perform the milestone clean rebuild, and run the updated complete axiom audit. This record does not retroactively attribute wiring from a later commit to this snapshot.

This round removes the proof gaps for the actual normalized experiment, zero probabilities, commutativity, the complete assignment family, and the exact score spectrum. The incorrect-score bound (1/p) alone does not vanish as (n) grows, so it does not establish the asymptotic verification converse or the main theorem. Complete bounds stratified by report scores, subsequent connections at the learner and optimum levels, and the final main proof still require acceptance at their respective actual commits. Module compilation times cannot estimate the effort for those unfinished mathematical chains. Corresponding tasks should be removed when their interfaces are proved; remaining effort should be reassessed once the key outstanding bridges have actual proofs.

## Additional review: statewise, aggregate, and optimal bounds for the original task

This section independently reviewed and incorporated `FixedConstraints/VerificationBounds.lean` from original commits `12ff028274fff563965fea94ae3e117c1f2e55ab`, `1dae7173e5fd23fd70e8e0e3f2e98034967fbb0e`, and `7dc2f59f6534b74ddb755a332cf91a0f2b67dd89`, without editing its Lean source. Independent compilation of the first two versions exited with code 0 and no warnings. The version including the final cleanup commit also exited with code 0, but line 298 produced a deprecation warning for `mul_le_mul_left`. The integration task reported adopting the recommended API and recompiling; the later version is governed by its frozen checks, not retroactively described as warning-free in this review.

Quantifier and aggregation checks passed:

- The original `optimal .worstCase` remains defined as `sSup_M (sInf_x ...)`. The worst-case branch of `verificationPerformance_le_affine_exact` first fixes the same `M`, obtains an actual minimum exact score from the nonempty finite state set, and applies the statewise affine bound at that input. It neither swaps `sSup_M` with `sInf_x` nor allows the measurement to depend on the unknown input.
- For each fixed `M`, `optimal_verification_le_affine_exact` first applies that performance bound, then bounds this measurement's exact performance by the exact `sSup`, and finally bounds the verification `sSup`. It does not assume that an optimal POVM attains the supremum.
- The uniform average still divides by `Fintype.card (StabilizerState p n)` and sums over distinct physical density matrices, rather than counting labels, vectors, or coordinate parameters. Positivity of the denominator follows from the internal proof `stabilizerState_nonempty`, using the graph Lagrangian of the zero matrix, its proved assignment existence, and the original label-to-state construction. Zero dimension is included in the general proof.
- `optimal_mem_Icc`, monotonicity of the optimum, and the optimal affine bound explicitly distinguish empty from nonempty `Learner W k`. The empty branch uses the original real-valued `sSup ∅ = 0`, reducing the affine bound to `0 ≤ 1/p`. No new `Nonempty (Learner W k)` premise is added. This agrees with the original definitions, but handling this branch is not represented as a proof that physical reports exist for every legal `W`.
- `optimal_exact_eq_one_iff_verification_eq_one` uses the proved unit-interval bounds, exact ≤ verification, and the optimal affine bound, followed by primality to obtain `0 < 1 - 1/p`. It assumes neither attainment, genericity, odd characteristic, positive dimension, nor additional nonemptiness. Its final parameters are exactly `{p n m} [Fact p.Prime] (a : Aggregation) (W : Constraint p n m) (k : ℕ)`.

The independent Scratch audit executed `#print axioms` for all 19 public theorems in the module. Every declaration had exactly `propext`, `Classical.choice`, and `Quot.sound`. The accompanying [verification-bounds-required.json](verification-bounds-required.json) supplies the 19 full declaration names and recommends their inclusion in the whole-project audit's `required` list. They cover the public interfaces from learner weights and the statewise range, through performance comparisons, to `optimal_verification_le_affine_exact` and `optimal_exact_eq_one_iff_verification_eq_one`.

The accompanying [verification-bounds-audit-links.json](verification-bounds-audit-links.json) supplies 19 groups of proof-value dependency checks that actually passed, including:

- Learner nonnegativity → actual `tensorPower_posSemidef`; weight sum → `trace_tensorPower`.
- Statewise affine bound → original incorrect-report bound and `sum_learner_born`.
- Performance range and worst ≤ average → proved nonemptiness of the actual state set.
- Performance affine bound → statewise affine bound; optimal affine bound → performance affine bound and performance range.
- Equivalence of optimal score one → optimal affine bound, exact ≤ verification, and the optimum's unit-interval bounds.
- Optimal affine bound → `Real.sSup_empty`, explicitly covering the empty-learner branch.

The final independent audit exited with code 0, and all 19 paths reported `DEPENDENCY_PATH_OK`. The `p=2,n=m=k=0` specialization of the optimal-score-one equivalence and a Scratch example asserting that the original optimum is zero when Learner is empty also passed. Output is stored in `Scratch/luders-review/aggregation-audit.log`, with program `BoundsReview.lean`. This section did not invoke the whole-project `Audit.lean`.

Thus, this section completes acceptance of the learner, average/worst-case aggregation, and elementary affine comparison of optima that remained pending in the preceding snapshot. It still does not prove a verification converse decaying with problem size: for fixed prime p, the single-layer incorrect score `1/p` does not tend to zero. Tail-probability bounds and the main theorem require their own actual proofs and the complete audit after freezing; completion cannot be inferred directly from this affine comparison.
