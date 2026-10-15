# Semantic review: fixed-constraint covariance and exact shell products

Date: 2026-10-11. Reviewer: frame_geometry subagent, in a separate context from the covariance and shell-product authors.

## Source binding and scope

The reviewed integrated snapshot was **1a122b6171bbd00fbf78e8b22b4fce7d4e454948**. The Mac checkout was read only. Its in-progress Main, Verified, Direct and ExactRate edits were outside this review.

| Item | Immutable source |
| --- | --- |
| Constraint covariance construction | 4bb4bd0b7d0c8b4797de7f06ec9f54e5a7ced295 |
| Complete covariance file, including all performance ranges and four optima | 6b1145599ee86acb15e19eab02b0fdbc80334261 |
| Literal shell products | b2806935a71994eb752018e7ef6457f674c647db |
| Grassmann product dependency | 083c3e6dd5f0e1463a5c72502626e85aab465e31 |

The integrated ConstraintCovariance.lean blob is 9a83fec3117f6b99e725e728d13c65182c7837c9, identical to 6b11455. The integrated OverlapShellProduct.lean blob is cea60fd1b0f9a247bdf583227963a268a28c54de, identical to b280693. The paper blob at the inspected snapshot is aa3cd71c14cff788d7ec793082e816c0a9f4864f.

This is a source-level semantic review, not a new compile, clean rebuild, or recursive axiom audit. Those checks remain the integrator's responsibility. The reviewer authored GrassmannExact and LagrangianShellExact; the review is independent of the covariance/product wrapper implementations, but must not be described as an independent second audit of those two underlying authored modules.

## Result

No blocking semantic issue was found in the requested covariance or exact product statements. The domains are the actual original physical objects. The only qualification is representational: the shell theorem evaluates the Gaussian coefficient with lower index n-r, whereas the displayed paper shell/energy formulas use lower index r. Both count the correct intersection choices, but the separate Gaussian symmetry rewrite is not formalized in these reviewed modules.

## Fixed-constraint covariance

The correspondence to paper/main-stabilizer2.tex:1314–1378, proposition prop:fixed-W-dimension-only-covariance, is complete at the stated finite-size level.

- ConstraintCovariance.lean:16–47 constructs an actual symplectic map for any two Constraint p n m values. It chooses actual Lagrangian completions, adapts their ordered bases to the original constraints, and maps the matching tails. Neither symplectic transitivity nor a Clifford implementation is a premise of the final result. The public Constraint definition in Task.lean:12–16 retains isotropy, dimension n-m, and m ≤ n.
- ConstraintCovariance.lean:70–118 transports all four public ReportSubspace conditions: isotropy, dimension m, inclusion in W-perp, and zero intersection with W. The inverse uses the inverse ambient linear equivalence, so this is a bijection on the entire legal subspace alphabet.
- ConstraintCovariance.lean:122–140 transports every assignment on each report subspace, then uses a sigma equivalence for all original reports. It is not a selected basis, canonical chart, or one-report-per-state restriction. The actual phase rule is inverse tau times the old eigenphase: CliffordTransport.lean:60–75. Its compatibility is proved on every point of the subspace using the XZ cocycle, and projector covariance is an identity of the original finite sums at CliffordTransport.lean:78–98.
- The section convention is the project's literal physical XZ section. In characteristic two the implementation does not discard phases or assume that its correction is always a sign. The unit-norm complex correction and proved cocycle produce an equivalence of the original finite Assignment encoding. Thus the operational statement is valid for p=2 without importing the paper's optional Hermitian-representative phase convention as an assumption.
- ConstraintCovariance.lean:168–183 uses a bijection on StabilizerState p n itself. Stabilizer.lean:24–29 defines this as distinct pure stabilizer density matrices. CliffordStates.lean:123–138 proves that the underlying density is conjugated by the implementing unitary. No prior over redundant labels replaces the full physical prior.
- ConstraintCovariance.lean:143–157 preserves the literal outcome-averaged verification payoff through the already proved LudersVerification.lean:17–26 reduction. This reduction includes zero-probability outcomes and the independent test copy. Validity follows from the already proved score-one iff original validity result; exceptional inputs with several valid reports are retained.
- ConstraintCovariance.lean:203–215 defines Learner W k ≃ Learner W' k using tensor-unitary conjugation and report relabeling. Task.lean:45–46 still uses the full matrix space Fin k → Configuration p n. The public POVM structure only requires PSD effects and their sum equal to identity. UnitaryExperiment.lean:11–14 gives a genuine POVM equivalence, not merely a map of Clifford or restricted measurements.
- ConstraintCovariance.lean:218–237 reindexes the full report sum and proves exact and verification score preservation on every original input. The same Clifford implementation is consistently used for states, report phases, projectors, and learner effects.

The optimization order is correct. ConstraintStatewise_range at lines 248–256 first proves equality of every fixed learner's full score range. ConstraintPerformance at lines 259–272 applies sInf to that range for worst case, and reindexes the uniform full-state sum for average; its denominator is the cardinality of the same original state type. ConstraintPerformance_range at lines 276–282 then uses surjectivity of the full learner equivalence. Finally optimal_constraint_independent at lines 286–289 applies sSup to equal attainable-performance ranges. No interchange of infimum and supremum, assumed optimizer, boundedness premise, or attainment hypothesis occurs. Four_optimal_constraint_independent at lines 292–300 states all four requested equalities.

All p are governed only by Fact p.Prime, and n,m,k are natural numbers with the constraint's intrinsic m ≤ n. The construction and theorem statements include p=2, n=m=0, m=0, m=n, and k=0. In particular covariance does not acquire the positive-copy hypothesis needed by the separate overlap-energy expansion.

## Actual shell count and literal products

OverlapShellProduct.lean:17–45 constructs the actual interval-subspace equivalence. A subspace K ≤ L is first treated as a submodule of L and mapped back by the subtype inclusion; both inverse identities are proved. A basis of the actual n-dimensional L then gives a linear equivalence with the coordinate space. The result is an equivalence with RankSubspaces, not a cardinality postulate.

GrassmannExact.lean:16–53 supplies the independent-family bundle bijection: an independent family determines its actual span, and its coordinates in a chosen basis of that span give the inverse. Lines 58–82 derive the natural-number identity from mathlib's independent-family and GL cardinalities. Lines 86–111 justify subtraction casting and division by the positive GL cardinality. Lines 115–142 factor powers to obtain the actual finite product
prod_{i < t} (p^(n-i)-1)/(p^(t-i)-1).
The Gaussian quantity is not defined to be Nat.card. This matches the product definition in paper/main-stabilizer2.tex:9555–9560 with t equal to the counted subspace dimension.

The shell coefficient in OverlapShellProduct.lean:57–63 is
prod_{i < n-r} (p^(n-i)-1)/(p^(n-r-i)-1) * p^(r(r+1)/2).
This index is correct: lagrangianDistance is n minus the dimension of the actual intersection, and the choices of K have dimension n-r. OverlapShellExactCounting.lean:17–39 gives a genuine disjoint-fiber equivalence; lines 54–65 evaluate each actual fiber using the symmetric-matrix equivalence. The product theorem does not assume the shell count.

Boundary checks follow directly from the quantified statement and product:
- r=0: the unique n-dimensional intersection is L, the Gaussian factor is 1, and the fiber factor is 1.
- r=n: the intersection is zero, the Gaussian product is empty and equals 1, and the count is p^(n(n+1)/2).
- n=0: necessarily r=0 and the shell count is 1.
- For nonempty products, i < n-r implies the denominator exponent n-r-i is positive. Prime p is at least 2. Empty products require no exceptional division.
- No odd-characteristic hypothesis is introduced by the graph symmetry argument, the Grassmann count, or these wrappers.

OverlapShellProduct.lean:67–78 evaluates the actual distinct-state tensor row energy. Its sum over r in range n uses distance d=r+1, so it covers precisely d=1,...,n; the diagonal state is excluded. The factor p^(d(d+1)/2) counts geometric fibers, and p^(-d(k-1)) already includes the exact p^d compatible assignment count. OverlapEnergy.lean:55–57 defines the physical off-diagonal row energy, lines 129–156 count actual compatible phases, and lines 159–176 reindex all original states using the proved state-label equivalence. This is not a sum over an assumed spectrum or a smaller ensemble.

The explicit hypothesis 0 < k is necessary for this energy identity: orthogonal states contribute 0^k only for positive k. The theorem should not be advertised as a k=0 energy formula. It includes n=0 for all positive k, when the energy sum is empty. Every actual state is covered via the surjective label-state equivalence, although the displayed product-sum theorem chooses to take its center as a label.

## Paper-map recommendations and limits

1. prop:fixed-W-dimension-only-covariance may be upgraded to complete, linked to four_optimal_constraint_independent (or the criterion/aggregation-general optimal_constraint_independent), subject to the integrator's normal build/audit gates.
2. The exact actual shell count, symmetric fiber factor, and finite Gaussian evaluation are closed. For lem:lagrangian-intersection-shells and eq:unrestricted-stabilizer-energy, describe the literal coefficient as the n-r-dimensional-intersection product [n,n-r]_p. Paper lines 5533 and 5576 instead print [n,r]_p. A separately named/formalized Gaussian symmetry equality between these two product presentations is not supplied by the reviewed package. This is not a flaw in the shell theorem and does not affect the direct bound.
3. The product module alone does not prove a PGM performance guarantee, a rate identity, or the complete Main theorem. Those are separate integration results and were not reviewed here. Likewise, the covariance half of a combined covariance-and-rates paper-map node does not by itself settle its rate-infimum component.
4. This review does not claim a fresh build or whole-project axiom closure. It records source-level quantifier, domain, phase, optimization-order, index, and boundary checks against the immutable sources above.
