# Direct-identification paper coverage: read-only semantic review

Reviewed mathematical source: **6d17da20d7a7625333ecf87d23824f031a01a6ae**.

Paper: paper/main-stabilizer2.tex, SHA-256 **c172bf686f08d7c0b643fa45b29323ba07416c494db6531edd5990fced34bd61**. The read-only Mac paper copy matches the frozen Git blob.

Date: 2026-10-11. Method: read immutable source, declarations, hypotheses and paper statements. This review did not compile Lean or modify mathematical source. The parallel strict clean-build audit is separate evidence. Scope is the five requested paper labels; proof of Main does not certify all other statements in the paper.

## Classification for theorem-map

| Paper label; paper lines | Classification at this freeze |
| --- | --- |
| thm:complete-identification-achievability; 393–410 | **Partial as a whole.** The actual statewise decoder bound and original fixed-W four-limit conclusion are closed. Finite unrestricted worst-case/average equality, a named common optimum, and the explicit W=0/full-identification equivalence remain unpackaged/unproved endpoints. |
| lem:unrestricted-stabilizer-overlaps; 5452–5466 | **Core mathematical statement closed in equivalent physical projector/assignment form.** Both the overlap dichotomy and exact compatible-phase fiber count hold for every prime. |
| lem:lagrangian-intersection-shells; 5527–5536 | **Actual exact count and literal finite product closed; paper Gaussian-symmetry wrapper remains.** The product is indexed by Fin(n-r), not the paper Gaussian coefficient indexed by r. |
| thm:unrestricted-stabilizer-direct; 5595–5611 | **Partial as a whole.** Actual normalized PGM, actual energy, pointwise error control, triangular tail with constant 4, and original-overhead limit are closed. Minimum-error optimality and the specific inverse-kappa constant are not. |
| cor:statewise-fixed-W-achievability; 5652–5669 | **Fixed-W conclusion closed; whole corollary partial.** All-input deterministic postprocessing and four original uniform limits are proved. Covariance/equal conditional PGM success and the inverse-kappa finite bound are not established by this chain. |

“Closed in equivalent form” identifies proved mathematical content, not a theorem carrying the same LaTeX label. Missing optimization or notation wrappers should not be silently presented as existing declarations.

## Complete identification

Quantum.stabilizerPGM p n k is an actual POVM on (Fin k → Configuration p n) with outcome alphabet StabilizerState p n (FiniteCopy/StabilizerPGM.lean:31). These are original distinct density matrices, not phase-labelled duplicates.

StabilizerLearning.stabilizerPGM_success_ge_bound (Bounds/Direct.lean:21) gives, for every prime p, natural n,k with n+1 ≤ k, and every actual x:

    1 - stabilizerDirectError p n k
      ≤ born ((stabilizerPGM p n k).effect x) (tensorPower x.val k)

The error is 4 * dampedTail (p:ℝ)⁻¹ n (k-n-1), independent of x and W. Quantum.dampedOverlapBound_tendsto_zero (Quantum/OverlapShellExactCounting.lean:144) assumes exactly the original real limit Tendsto (fun n => (k n:ℝ)-(n:ℝ)) atTop atTop. No success bound, covariance, optimality, or equal-success premise occurs in the final decoder theorem.

This closes the unrestricted statewise direct mechanism. The named original-task endpoint is StabilizerLearning.fixedConstraint_four_uniform_limits_one (Bounds/Direct.lean:39). Taking the output-dimension sequence m(n)=n covers the fixed-W endpoint mentioned in the paper.

FixedConstraints.fullIdentificationPerformance and fullIdentificationOptimal are defined at FixedConstraints/FullStatePostprocessing.lean:176,184 using sInf/uniform mean and sSup over all complete-state POVMs. The theorems at lines 228 and 238 only prove fullIdentificationOptimal_le_optimal_exact and fullIdentificationOptimal_le_optimal_verification. There is no reverse W=0 equivalence theorem, no finite equality between the unrestricted worst-case and average optima, and no standalone Tendsto endpoint for the two named fullIdentificationOptimal values. The pointwise bound supplies the mathematical lower-bound ingredient for such limit wrappers, but does not prove their finite equality or maximum attainment.

Therefore do not mark the entire paper theorem closed: its displayed equality for every n,k is an additional assertion beyond the proved direct mechanism.

## Unrestricted overlaps and compatible states

Quantum.born_labelProjector_eq (Quantum/OverlapEnergy.lean:104) is exactly the dichotomy: actual Born overlap is inverse p-to-the-intersection-codimension if restricted assignments agree, and zero otherwise.

The exact counting and physical bridges are:

- Quantum.born_jointProjector_overlap (Quantum/ProjectorOverlap.lean:115): the public actual XZ-section projector calculation.
- Quantum.card_compatibleAssignments (Quantum/AssignmentExtension.lean:124): p^(dim U - dim(U∩V)) compatible assignments, with only isotropy of U and a real center assignment as hypotheses.
- Quantum.restrictAssignment_surjective and card_assignmentRestrictionFiber (same file:48,89): actual assignment extension and exact fibers; extension is proved, not assumed.
- Quantum.stabilizerLabelStateEquiv (Quantum/StabilizerEquivalence.lean:34): actual labels are in bijection with original distinct projective physical states.
- Quantum.StabilizerState.stateVector_density, tensor_stateVector_density, tensor_born_eq_normSq (Quantum/PureStateVectors.lean:101,106,117), and born_pureVectorDensity at line 58: translation to the paper's normalized-vector squared-overlap notation.

For Lagrangian U the fiber exponent is r, proving the second clause of the paper lemma. The fixed prime can be 2. Assignments retain ZMod(2*p), hence ZMod 4 in characteristic two. Ordinary characters describe assignment ratios, not an incorrect replacement of the full physical section assignment.

Compatibility is equality of physical eigenvalues: assignmentComplexEquiv (Quantum/PhaseEncoding.lean:134) and eigenPhase_injective identify the finite encoding with its complex phases. The source uses the public XZ section. A separate theorem quantifying over arbitrary Pauli-section rephasings is not packaged; do not advertise the paper's explanatory representative-invariance discussion as an additional general-section transport API.

## Exact shells and literal Gaussian products

The count has no assumed fiber estimate:

- Quantum.lagrangianIntersectionFiberEquivSymmetricMatrices and card_lagrangianIntersectionFiber_eq (Quantum/LagrangianShellExact.lean): a genuine bijection and cardinality p^(r*(r+1)/2) for each K ≤ L with dim K=n-r.
- Quantum.lagrangianShellEquivIntersectionFibers (Quantum/OverlapShellExactCounting.lean:17): the actual shell is the dependent sum over actual K.
- Quantum.lagrangianShellCount_eq (same file:54): actual interval-subspace cardinality times the exact symmetric-matrix factor.
- Quantum.lagrangianSubspacesEquivRankSubspaces (Quantum/OverlapShellProduct.lean:17): genuine coordinate bijection.
- Quantum.lagrangianShellCount_eq_gaussian_product (same file:57): literal finite product

    (∏ i : Fin (n-r),
       ((p:ℝ)^(n-i.val)-1) / ((p:ℝ)^(n-r-i.val)-1))
      * (p:ℝ)^(r*(r+1)/2).

StabilizerLearning.card_rankSubspaces_prime_eq_gaussian_product (Foundations/GrassmannExact.lean:138) proves the Grassmann product itself. This is not a Nat.card definition renamed as a product.

The shell theorems assume r ≤ n, exactly the range of actual intersection codimensions. They include r=0, r=n, n=0 and p=2; the triangular division is natural-number arithmetic, not division by 2 in the prime field.

The paper prints [n choose r]_p. The proved product is [n choose n-r]_p because it counts K. No Gaussian-symmetry Lean endpoint rewrites this to the Fin r expression. The remaining difference is an explicit identity/notation wrapper, not a missing actual shell count. State this distinction instead of claiming an exact syntactic match to the paper display.

## PGM, finite constants, and copy boundaries

The construction handles singular support:

- FiniteCopy/SupportedSynthesis.lean:18,26 defines the spectral inverse root, zero on the kernel, and supported synthesis.
- supportProjection_idempotent and supportProjection_mul_synthesis (same file:158,169) prove projection idempotence and signal support.
- PGM.completedColumnPOVM (FiniteCopy/ColumnMeasurement.lean:54) assigns the positive support complement to one legal outcome and proves normalization.
- born_completedColumnPOVM (same file:65) proves that completion contributes zero on every signal, including the chosen outcome.
- Quantum.stabilizerSynthesis_column and stabilizerSynthesis_gram_diagonal (FiniteCopy/StabilizerPGM.lean:20,25) identify the columns with original tensor densities and prove Gram diagonal one.
- Quantum.stabilizerPGM_born_gram and stabilizerPGM_success_ge_overlap (same file:36,44) prove the actual square-root-Gram probability and statewise energy bound.

PSD and unit diagonal in the generic Gram inequality are discharged here. Neither invertibility nor a low-energy assumption is required; FiniteCopy/GramEnergy.lean:64 handles both energy ≤ 1 and energy > 1. Unweighted synthesis is appropriate for a uniform-prior PGM because the common scalar weight cancels during normalization.

The actual energy is a sum over all distinct physical states except the center (Quantum/OverlapEnergy.lean:55). Its exact finite-product evaluation is Quantum.stabilizerOverlapEnergy_eq_gaussian_product_sum (Quantum/OverlapShellProduct.lean:67).

**Zero-copy distinction:** PGM construction, its actual Born/Gram identity, and its actual-row-energy bound allow every natural k, including zero. The compatible-phase shell-energy formula requires 0 < k. At k=0, originally orthogonal inputs also produce the same scalar zero-copy density; discarding them via their zero single-copy overlap would be invalid. Do not extend this shell formula to zero copies.

Quantum.stabilizerOverlapEnergy_le_dampedTail (Quantum/OverlapShellExactCounting.lean:115) gives the triangular tail for n+1 ≤ k. StabilizerLearning.dampedTail_le (Bounds/Asymptotic.lean:21) supplies geometric domination when k ≥ n+2. Their direct composition gives the paper-shaped ratio bound with **constant 4**. Empty sums/products preserve n=0; the finite tail theorem still assumes n+1 ≤ k, so it does not separately package the (n,k)=(0,0) corner.

**Constant distinction:** the paper defines kappa_p^GL as an infinite product at lines 2946–2947 and uses its inverse at 5601–5602. The Lean chain instead proves the finite-product lower bound 1/4 (Foundations/UniformGL.lean:34), then card_GL_lower at line 85. The specific infinite-product constant and its use in the displayed direct endpoint are not proved here. A weaker upper bound with constant 4 does not imply the potentially smaller inverse-kappa bound. A scalar tail lemma accepting an arbitrary constant is not a proof of the requested counting constant.

**Optimality/equal-success distinction:** no theorem establishes minimum-error optimality of this stabilizer PGM, constancy of the square-root Gram diagonal across states, or equality of conditional successes. The pointwise lower bound does not imply any of these. Also, assigning the support complement to a single chosen outcome need not preserve full-Hilbert-space covariance; its contribution on every signal is proved zero. The direct argument obtains a common statewise lower bound without requiring these extra assertions.

## Fixed-W postprocessing and the exact scope of Main

FixedConstraints.FullStatePostprocessing implements every input, including exceptional inputs:

- finrank_fullTargetSlice (line 17): dim(L∩W-perp) = m + dim(L∩W).
- exists_fullReportSubspace, fullReportSubspace, fullReportSubspace_sup (lines 48,91,98): a legal complement of dimension m, disjoint from W, spanning the required slice with L∩W.
- fullLabelReport, fullStateReport (lines 104,108): restriction of the genuine original phase assignment.
- valid_fullStateReport, verificationPayoff_fullStateReport (lines 111,119): exact validity and score one.
- fixedWPostprocess (line 130): an actual POVM pushforward on the original copy space.
- fullIdentification_born_le_exactStatewise and fullIdentification_born_le_verificationStatewise (lines 134,168): statewise success survives postprocessing.

StabilizerLearning.fixedConstraint_direct_finite (Bounds/Direct.lean:28) gives the original four finite lower bounds. fixedConstraint_four_uniform_limits_one (same file:39) gives all four original UniformLimit conclusions with only prime p and the original real overhead assumption. No positive output-rate beta, generic-input premise, success estimate, counting estimate, or externally supplied complement is required.

The task retains the uniform prior on all distinct physical states and an sSup over every normalized PSD collective learner POVM (FixedConstraints/Task.lean:85,92). Constraint itself carries m ≤ n, isotropy and dim W=n-m. UniformLimit has the exact quantifier order “for every epsilon > 0, there exists N, for every n ≥ N, for every actual W” (FixedConstraints/Rates.lean:25). The learner does not gain the verifier outcome.

The report complement is a fixed Classical.choose function, hence deterministic mathematically. It is not an executable Gaussian-elimination algorithm. This refinement is unnecessary for the proved correctness and achievability conclusion.

Accordingly, the final fixed-W convergence claim of the corollary is closed, by a genuine pointwise construction. Its preliminary equal-success/covariant-PGM assertion and the inherited inverse-kappa bound remain separate.

StabilizerLearning.fixedW_noCopyRateDiscount (Main.lean:17) closes the unchanged FixedConstraints.NoCopyRateDiscountForPrime target: its specified converse, four direct limits and two exact rates. It does not additionally prove PGM optimality, finite unrestricted worst-case/average equality, inverse-kappa constants, Gaussian symmetry, or all other statements of the paper. Preserve those boundaries in the theorem map.
