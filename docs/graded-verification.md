# Compatible-list converse for the original verification task

This stage leaves the original `Main.lean`, `Quantum/Finite.lean`, `Pauli.lean`, `Stabilizer.lean`, `FixedConstraints/Task.lean`, `Rates.lean`, paper, and version locks unchanged. The mathematical chain below has compiled; formal acceptance is determined by this stage's comparison records under `validation/`.

## Original sets and experiment

`genericStateReport W x hx` is the unique correct report for an original generic physical input. The actual list `genericCompatibleList W D r` requires all three of the following: a target realizable by a generic input, subspace distance at most D, and agreement of the two original finite phase assignments on their common physical Pauli subspace. List size is maximized over all legal centre reports, without assuming transitivity of centres or a uniform prior on targets.

`CompatibleVerification` derives the common-intersection identity from the requirement that legal report subspaces lie in the symplectic orthogonal of W, then applies the proved actual Lüders / Pauli phase spectrum. Outside the list, incompatible scores vanish; compatible reports at distance greater than D have score at most `p^(-(D+1))`. This is the score of the original experiment, with no replacement of the verification definition.

## Actual counting

`AssignmentExtension` extends ordinary characters using a linear retraction associated with a subspace inclusion, then extends original assignments through the complete finite-phase/character equivalence. This proves surjectivity of restriction. Actual restriction fibres have size exactly `p^(dim V-dim U)`; the count is neither an assumption nor extra data.

For a legal target at distance at most D, choose an `m-D` dimensional subspace I in the common intersection. The encoding retains the actual report's K and assignment, so the original report can be recovered and injectivity proved. Multiplying the counting bounds for two actual interval Grassmannians by the restriction-fibre count yields

`L_D ≤ 16*p^(2*n*D+D) ≤ 16*p^(2*n*D+m)`, assuming `D≤m`.

This cover may count objects more than once; it is not incorrectly presented as a bijection. The bound applies to all primes and to D=0, m=0, and n=0. Exact assignment fibres are proved, but this argument does not prove the finer Gaussian shell sum, exact shell counts, or specified kappa constants in the paper's `lem:generic-original-list-count`. Those items remain partially covered.

## Legal list decoding and original probability bounds

`BoundedList` constructs an actual POVM: each candidate in a list receives a 1/L share of the original effect, and the remaining nonnegative weight for each original report is assigned to a fixed legal output. Positivity and the sum-to-identity property are proved. This gives a list-event bound pointwise in the state and for every nonnegative input prior; report and target alphabets may differ, and the target map need not be injective.

Under the uniform prior on the original generic physical inputs, the constructed decoder still belongs to the full original `Learner W k` type. Consequently,

`genericVerificationOptimal ≤ L_D*genericExactOptimal + p^(-(D+1))`.

The actual exceptional mass and decomposition of the original full input prior then give

`optimal verification average ≤ δ + (1-δ)*(L_D*genericExactOptimal + tail)`.

These final finite statements take only the original W, k, and D as parameters. List counts, event probabilities, physical bridges, and prior decompositions are not assumed.

## The same J and uniform limits

`VerificationConverse` actually invokes the comparison between original generic exact success and the physical refined optimum, together with the finite moment / completion / row-space / prescribed-rank converse.

Set `D_N=Nat.sqrt N`. The formal proof shows that D_N tends to infinity, D_N/N tends to zero, and D_N≤m_N eventually whenever m_N/N tends to a positive b. It uses the explicit remainder

`gradedConverseRemainder = converseRemainder + 2*N*D_N + m_N + log(16)/log(p)`,

proves that this remainder divided by N² tends to zero, and identifies the list cost times the original finite envelope with `p^(-J*N²+gradedConverseRemainder)`. The remainder is chosen before W.

Generic verification is bounded by this quadratic-exponent term plus `p^(-(D_N+1))`. The average under the original full prior additionally includes the proved exceptional term `p^(-m_N)`. All three terms tend to zero, and the original worst-case optimum is bounded by the original average optimum. Every threshold works uniformly for all legal W of the given dimension.

Finally, `fixedConstraint_uniform_converse` returns the entire converse component of the original Main: the same exact exponent bounds, the same remainder, and all four original `UniformLimit ... 0` conclusions. Neither the order `sup_M inf_x` nor the definition of the test copy is changed.

## Still open at this stage

The complete `FixedWNoCopyRateDiscount` remains statement only. The direct construction using unrestricted collective measurements, the four limits to one, the exact copy-rate identities, and final strict main-theorem release still need proofs. Successful root builds of the auxiliary results at this stage do not constitute a proof of the complete Main.
