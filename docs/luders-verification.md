# Original Lüders verification: proof scope and acceptance

This stage preserves the definitions and quantifiers in the original paper, `Main.lean`, `Quantum/Finite.lean`, `Pauli.lean`, `Stabilizer.lean`, `FixedConstraints/Task.lean`, and `Rates.lean`. The main theorem is still **statement only** at this stage; the local conclusions below do not establish the whole no-copy-rate-discount theorem.

Lean 4.24.0 and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` are pinned. The final frozen commit and results of the two complete builds are recorded in the [stage acceptance comparison](validation/2026-10-11-luders-verification/comparison.json). See the [independent semantic review](luders-verification-review.md).

## Constructed proof chain

1. `Quantum/BornProbability.lean` derives actual Born nonnegativity from Gram factorization of PSD matrices, proves that projector scores lie in [0,1], and characterizes zero and unit scores by projector action. Zero score implies that the projected sandwich matrix vanishes; this is not an additional axiom.
2. `Quantum/TensorProbability.lean` proves multiplication, conjugate transpose, trace, and positivity laws for the original entrywise `tensorPower`, including k=0.
3. `Quantum/ProjectorRelations.lean` and `FixedConstraints/ReportSemantics.lean` derive commutation of the W and report projectors from actual Pauli multiplication and the original report conditions. They prove that the original `Valid` is equivalent to inclusion of the report subspace in the input Lagrangian and equality of the report assignment with the restricted input assignment.
4. `Quantum/ProjectorOverlap.lean` uses actual character orthogonality to prove the complete intersection spectrum. For input label (L,χ) and report (K,η), the score is p^(dim(K∩L)−dim K) when phases agree on K∩L, and zero otherwise. All primes use the original XZ section.
5. `Quantum/Luders.lean` constructs normalized Lüders density matrices for positive-probability outcomes. It proves conditional scores lie in [0,1], removes normalization in each weighted term, and establishes the averaging identity for the complete projector family.
6. `FixedConstraints/LudersVerification.lean` applies these results to the original definitions. The final `verificationPayoff_eq_born W x r` takes no externally supplied commutativity, projector completeness, label representation, equivalence, or probability-bound premises. Completeness invokes the proved `sum_jointProjector` and assignment existence for every isotropic subspace.
7. `VerificationBounds.lean` proves that actual learner-POVM weights are nonnegative and sum to one. It derives unit-interval bounds pointwise in the state, for both aggregations, and for the four original `optimal` values, together with exact≤verification, worst≤average, and the affine comparison below.
8. `VerificationTail.lean` defines a near event using actual report-intersection codimension, splits the original learner's report sum term by term, and obtains a graded tail bound.

The full original `Report W` set is not replaced by a canonical subfamily. Exceptional inputs may have several correct reports. No odd-prime, positive-dimension, positive-copy-count, or attained-optimal-POVM assumption is added.

## Final interfaces

- `verificationPayoff_eq_born W x r`: the original average over ν equals the Born score of the report projector.
- `verificationPayoff_eq_one_iff_valid W x r`: the score is one exactly when the original report is valid.
- `verificationPayoff_le_inv_prime_of_not_valid W x r h`: an incorrect report scores at most 1/p.
- `optimal_mem_Icc c a W k`: all four original optima, for two criteria and two aggregations, lie in [0,1].
- `optimal_exact_le_verification` and `optimal_verification_le_affine_exact`: for both average and worstCase, P_exact≤V≤1/p+(1−1/p)P_exact.
- `optimal_exact_eq_one_iff_verification_eq_one`: for either aggregation, the exact optimum equals one if and only if the verification optimum does; no optimal measurement need exist.
- `verificationStatewise_le_nearReportProbability_add_tail W k M x ℓ hℓ t`:
  V≤Pr[m−dim(K_report∩L_ℓ)<t]+1/(p^t).
  `nearReportProbability` is the sum of original Born weights over the actual report event, not a new assumption.
  `exists_label_verificationStatewise_le_tail W k M x` obtains a representation of the original input internally and provides this bound simultaneously for all t, without an externally supplied label-existence premise.

The average divides by the cardinality of the original set of distinct density-matrix states. The worstCase affine bound first attains the minimum exact score over the finite input set for a fixed M, and then compares verification at the minimizing input for that same M. The outer optimization remains the original `sup_M inf_x`; the quantifiers are not swapped. State nonemptiness is constructed from the zero graph and proved assignment existence. Learner nonemptiness is not assumed: the formal empty branch follows the original real-valued convention sSup∅=0. A separate geometric interface proving physical nonemptiness of legal fixed-W reports and learners remains the responsibility of the subsequent bridge.

## What this stage does not establish

The Lüders identity averages over outcomes ν; it does not equate the conditional scores for individual ν. The independent test copy always belongs to the verifier and is not included in the learner's k copies.

The 1/p residual does not vanish with n, so the affine bound alone cannot prove the verification converse. The near/far bound proves the actual event split but does not yet supply a bounded-list/counting estimate for the near probability. The current near event filters only by codimension and does not additionally impose intersection-phase compatibility; the paper's compatible-list cardinality cannot be applied directly to that larger event. The proved exact spectrum can first refine the event and remove all zero contributions from incompatible reports, after which the corresponding legal list reduction and count must be proved. Identification of the generic-input target with the paper's K_W(x), the graded-to-exact comparison, exceptional-mass control, and connection to the proved uniform J remain necessary. Similar names alone do not complete the interface between the paper's refined P_id/verification propositions and the original basis-free optimal values.

Symplectic/Clifford transport for arbitrary reference frames, fixed-W operational comparison, the full direct construction, the four original operational limits, and the final copy-rate main proof are not completed by this stage.

## Acceptance and remaining effort

The import chain is `StabilizerLearning → Main → Verified → VerificationTail`; Scratch is outside the formal chain. Acceptance must include a root build after clearing project .oleans and a reconstruction in a new directory that independently obtains pinned dependencies and the official cache. Both use the same version-checked Linux compiler and are not described as a new operating system or a cross-machine test. The recursive axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`, and checks reachability in actual proof terms. The main-proof release gate should continue to reject the unproved Main.

Only after these checks pass are this stage's Lüders averaging identity, validity criterion, actual score spectrum, elementary probability bounds, and near/far partition removed from the remaining obligations. Completed packages have zero remaining work; the open near-event counting, arbitrary-frame/fixed-W, and direct/Main chains lack a calibrated end-to-end example. Declaration counts, lines of code, compilation seconds, and GPU hours are therefore not converted into a total calendar estimate.

## Recorded repair of the audit entry point

At the first freeze, 3e60465, both complete root builds succeeded, but both original large single-command audits exited with code 139 and were not accepted. Increasing the process stack did not resolve the issue. An isolated diagnostic wrote directly to a file and confirmed entry into the command, but neither the required-table-ready marker nor any axiom traversal had been reached. No Lean-runtime root cause was inferred from this alone. Failed logs and reproduction metadata are retained under `validation/2026-10-11-luders-verification/failed-3e60465/`.

20e9cd5 only split the audit into required/Main checks, the all-declaration axiom pass, dependency blocks, and the final graph/statistics stage. Independent review confirmed that the ordered table of 237 required declarations and 206 dependency pairs is identical. The allowed axioms, public/private declaration scope, and complete axiom loop were not reduced. Exit code 0 for the full process remains mandatory: an isolated AUDIT_OK cannot hide an error in an earlier block. All mathematical Lean files are byte-identical to those in the first clean rebuild. The working-copy recheck reused these unchanged modules; the separate fresh directory obtained dependencies anew and rebuilt from scratch. Final results are governed by comparison.json; running a diagnostic candidate does not replace formal acceptance.
