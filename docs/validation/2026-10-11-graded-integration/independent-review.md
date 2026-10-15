# Independent frozen-source review

Reviewed peer commit: `583897b83f2714c9b1a4d27fb1cfd2fc988ee7e8`.
Mac integration commit: `9c6bacadd5fd4231f0e59955e17e565e17b7b56e`.
Three independent reviewers read the exact frozen sources without editing or
running compilation. No blocking semantic defect was identified. Compilation,
complete axiom audit and evidence comparison remain separate acceptance gates.
Source hashes are in `acceptance-plan.json`.

## Constructive Bayes reduction and the original experiment

Reviewer: `/root/clifford_implementation`.

- `FiniteCopy/BoundedList.lean:16–61` constructs nonnegative stochastic weights
  and a normalized positive POVM. Every original effect gives weight `1/L` to
  each candidate; unused weight goes to a fixed legal output. An empty list and
  a fallback already in the list are both covered. There is no division by an
  outcome probability.
- `FixedConstraints/GradedComparison.lean:60–89` constructs this decoder for
  each original `Learner W k`. It does not depend on the unknown input state.
  The prior remains the uniform prior on actual `GenericState W`, not a
  substituted uniform distribution on target labels. The target may be
  noninjective. General Bayes helpers are instantiated with proved card bounds.
- `CompatibleVerification.lean:34–45` proves the actual maximum list size is
  positive using a generic state's own target. Individual lists may be empty.
  Existence of the fallback report is already proved in `GenericNonempty`.
- `CompatibleVerification.lean:47–91` identifies the actual input/report
  intersection and full phase restrictions, then invokes the original Lüders
  spectrum. The zero-probability branch is handled by the existing positivity
  proof in `Quantum/Luders.lean:67–82`, not excluded by hypothesis.
- `CompatibleVerification.lean:101–145` bounds incompatible scores by zero and
  compatible distant scores by `p^(-(D+1))`, using total Born probability one.
  `GradedComparison.lean:112–143` takes the supremum over all original POVMs
  and restores the actual full-state prior via
  `delta + (1-delta) * (L * genericExactOptimal + tail)`.

## Actual compatible lists and assignment fibers

Reviewer: `/root/frame_geometry`.

- `Quantum/AssignmentExtension.lean:27–56` constructs the character extension
  using a linear retraction and transfers it to the full original phase torsor.
  The final extension theorem has no base-assignment or surjectivity premise.
- `AssignmentExtension.lean:89–130` proves the genuine restriction fiber count
  `p^(dim V-dim U)` and the actual intersection-compatible assignment count.
- `CompatibleList.lean:12–31` retains realizability by generic physical states,
  distance and full phase compatibility. The maximum ranges over all original
  legal centers without assuming equal list sizes or center realizability.
- `CompatibleListCounting.lean:204–266` chooses an actual common
  `(m-D)`-subspace and proves an injection retaining the original report and
  assignment. Enlarging legal subspaces to the full phase-space interval only
  overcounts; no cover is falsely asserted to be a bijection. The count uses
  the proved phase restriction fiber.
- `CompatibleListCounting.lean:315–325` proves
  `L_D <= 16 * p^(2*n*D+D)` for every `D <= m <= n`, uniformly in W and center.
  All primes including 2, zero dimensions, `D=0`, `D=m`, and `m=n` are covered.
  Natural-number subtractions are supported by actual dimension inequalities.

The original paper's Gaussian shell sum and specified kappa prefactor are NOT
proved by this ambient cover. `lem:generic-original-list-count` must retain
partial coverage; exact assignment-extension counting may be marked closed.

## Uniform asymptotics and original Main converse component

Reviewer: `/root/fixedw_geometry`.

- `GradedAsymptotics.lean` proves `Nat.sqrt N` diverges, its ratio to N tends to
  zero, and it is eventually at most `m N` when the limiting visible rate is
  positive. The common extra exponent is
  `2*N*Nat.sqrt N + m N + log(16)/log(p) = o(N^2)`.
- `VerificationConverse.lean` obtains `k N <= N` and `N > 0` eventually from
  the original rates. Alpha zero, beta one and prime two remain included.
  The finite envelope excludes N zero; the finite list/graded theorem does not.
- The original average is over all distinct stabilizer states, the learner is
  unrestricted, and worst-case decay uses the established worst-case/average
  inequality without exchanging supremum and infimum.
- Verification retains both the square-root tail and full-prior exceptional
  term. It is NOT claimed to decay with only a quadratic exponential term.
- `fixedConstraint_uniform_converse` has `exists e C` before the eventual N
  and every W. It uses the original exact remainder and C=1 and returns all
  four original `UniformLimit ... 0` conclusions. Its conclusion matches the
  entire converse clause of unchanged `NoCopyRateDiscountForPrime`.

Still separate: refined-verification-specific rank-list interfaces; literal
Gaussian shells; full covariance between arbitrary equal-dimensional W;
unrestricted direct measurement, uniform limits to one, copy-rate identities,
and the final Main proof. Root reachability is not a proof of Main.
