# Transport for arbitrary reference frames: independent semantic review

## Review target and scope of conclusions

The reviewed source commit is **`40239e92d885d4d8e1f70e24980be8cbb58ba0e2`** (`40239e9` for short), from private branch `codex/frame-fixedw-comparison`. Every source-code and paper assessment in this document refers to this immutable snapshot; later changes in other working directories are not included in the conclusions.

Primary modules reviewed:

- `StabilizerLearning/Quantum/ReferenceChart.lean`
- `StabilizerLearning/Quantum/ReferenceVerification.lean`
- `StabilizerLearning/Bounds/ReferenceConverse.lean`

Their state, direction, assignment, report, and measurement interfaces were also traced through `Quantum/ReferenceFrameDirections.lean`, `Quantum/CliffordStates.lean`, `Quantum/CliffordTransport.lean`, `Quantum/UnitaryTransport.lean`, `FiniteCopy/UnitaryExperiment.lean`, and `FixedConstraints/ReferenceReports.lean`, and the public target in `StabilizerLearning/Main.lean` was checked. This is an independent semantic review of the three transport modules written by the main task; the reviewer participated in constructing the underlying Clifford implementation and state bijection, so this document is not described as a fully independent review of the entire dependency chain.

**Conclusion: in the reviewed snapshot, no substantive substitution of a smaller state family, phase target, or measurement class for the original fixed-reference-frame problem was found in these three modules.** Actual density matrices, report projectors, and all collective POVMs admit bidirectional transport between any ordered Lagrangian reference frame and the standard transverse chart, with exactly equal uniform-average exact success. Verification scores agree state by state, and the sets of attainable average and worst-case scores agree. `ReferenceConverse` carries the established standard-chart exact-identification bound to any public frame without an additional physical-equivalence assumption.

This conclusion does not claim closure of the verification asymptotic bound for the original fixed-W full-report problem or a proof of `Main`. This document reports no new compilation, `scripts/check.py`, clean root rebuild, or successful release gate; it is a semantic and assumption review of fixed source code, not a replacement for that verification evidence. This delivery adds only this document and does not modify mathematical sources.

## Correspondence to the source paper

The source paper is `paper/main-stabilizer2.tex` at the same commit, with content SHA-256:

`c172bf686f08d7c0b643fa45b29323ba07416c494db6531edd5990fced34bd61`

The following labels are more suitable than line numbers for locating material in later versions; line numbers apply only to this snapshot.

| Source location | Original obligation | Correspondence and boundary in the reviewed source |
| --- | --- | --- |
| `eq:announced-reference-frame`, `eq:frame-state-family`, approximately lines 536–547 | An arbitrary ordered Lagrangian frame R; those original distinct stabilizer states whose L(x) is transverse to the frame subspace | `ReferenceLabel` and `ReferenceState` restrict the original complete types using `Disjoint`, rather than defining them in advance as a particular coordinate image. |
| `eq:reference-dual-family`, `eq:frame-assisted-exact-target`, approximately lines 548–566 | The first m reference-dual directions uniquely determined by pairing, together with the entire restricted assignment | `referenceTargetDirections`, `referenceLabelTarget`, `referencePhysicalTarget`, and `referenceLabelTarget_transport`. |
| `prop:frame-conditioned-coordinate-reduction`, approximately lines 639–658 | Physical coordinate equivalence of states, targets, measurements, and tests; equality of average exact and verification optima, and identification of the worst-case problems | `referenceIdentificationOptimal_eq_physical`; `referenceExactStatewise_transport`; verification transport for per-state, average, and worst-case scores and the score sets of all measurements. Exact worst-case per-state transport is present, but no separately named exact worst-case optimum equality is stated here. |
| Original model distinctions, approximately lines 668–692 | The original fixed-W, generic unique-target, refined-chart, and unrestricted problems differ | The source does not claim that `ReferenceReport` and the complete original `Report W` form the same alphabet. Nor is the m=n chart full-label task renamed as the unrestricted W=0 task. |
| `thm:refined-exact-converse`, approximately lines 705–720 | All frames share the J-exponent bound on exact success and the zero-limit conclusion | `reference_probability_le_converseEnvelope` and `reference_common_converse_source`; the latter uses the same remainder as the standard physical converse. |
| `thm:refined-verification-threshold`, approximately lines 723–734 | The optimal verification score tends to zero | The three reviewed modules provide only verification coordinate transport; the exact converse alone does not give this conclusion. |
| `thm:fixed-W-no-discount`, approximately lines 1398–1452 | Exact and verification upper/lower bounds and the no-discount rate conclusion for the original fixed-W full-prior, full-report problem | Not directly stated by `ReferenceConverse`; the original fixed-W operational comparisons, exceptional-mass control, verification near-event argument, and direct direction are still needed. |

## Itemized semantic checks

### States and physical implementation

`ReferenceState R` is a subtype of the original `StabilizerState p n`, requiring the actual Lagrangian recovered by `stabilizerLabelStateEquiv.symm` to be transverse to R. The original state type distinguishes states by density matrices, and the proved label-to-state bijection prevents multiple labels from being counted repeatedly as distinct physical inputs.

`referenceLabelEquiv` restricts the complete `symplecticStabilizerLabelEquiv`, using `frameMapLagrangian_transverse_iff` to turn transversality into the standard transverse condition. `referenceStateEquiv` then combines this with both label–state bijections, so it covers the entire state families on both source and target sides and has an inverse.

Physical density transport uses `referenceStateEquiv_density`, with U supplied by `frameClifford R`. This U is obtained by applying the proved implementation-existence theorem to the original symplectic linear automorphism and pairing-preservation property; existence of a Clifford implementation is not assumed by this section's theorems. Reports, states, and the learner's tensor power all use the same chosen implementation.

### Targets, phases, and report alphabets

`ReferenceDirections R` retains all valid ordered m-tuples of directions: pairing with the full frame gives the corresponding Kronecker delta, and internal symplectic pairings vanish. `referenceDirectionsEquivCanonical` has an explicit two-way correspondence covering the entire refined alphabet.

The actual target consists of reference-dual directions inside the input Lagrangian, with the assignment obtained directly by restricting the original label using `restrictAssignment`. The target does not merely retain a subspace, generator signs, or linearized odd-prime phases. Both `ReferenceReport` and `CanonicalReport` carry the complete finite `Assignment` on their actual subspaces.

The Pauli covariance convention is

`U P(z) U† = τ(z) P(g z)`.

Accordingly, the target-side eigenphase must equal the source eigenphase multiplied by `τ(z)⁻¹`. The source's `assignmentPhaseEquiv` and `referenceLabelTarget_transport` use this direction; the latter proves actual report equality by injectivity of directions and of the full encoded eigenphases. Unit-norm and section-cocycle identities come from the same unconditional implementation and are not extra unproved physical assumptions.

The paper allows the original fixed-W learner a larger basis-free report alphabet. `referenceReportForget` maps refined reports into original reports while preserving assignments and projectors; it proves only the needed embedding/injectivity, without replacing the entire original report set by a nonexistent surjection. This supports operational comparisons in the appropriate direction, but does not alone imply the original full-report verification converse.

### Uniform priors

`referenceIdentificationSuccess` is `uniformTargetSuccess` over `ReferenceState R`, with inputs given by k-fold tensor powers of their actual densities. `referenceStateEquiv` is a bijection of finite types and therefore preserves cardinalities and pointwise uniform mass. Average transport uses invariance of finite means under a bijection and needs no extra assumption equating uniform random labels with uniform random states.

The prior retained here is the paper's uniform prior on the frame-transverse state family. It is not the original fixed-W full-state prior, which also contains exceptional states and requires a separate generic/full decomposition and exceptional-mass bound. This section's average equality cannot be used directly as an equality for that larger prior.

### All collective POVMs and optimization quantifiers

Both the domain and codomain of `referenceMeasurementEquiv` are complete finite-output `POVM` types, acting on `Fin k → Configuration`. The equivalence combines unitary conjugation by the actual `tensorUnitary U k` with relabeling by the report bijection and has an inverse. The learner is not restricted to Clifford circuits, stabilizer measurements, projective measurements, per-copy measurements, or covariant measurements.

Exact identification proves equality of the entire sets of attainable average success probabilities, then takes `sSup`, so no chosen measurement is assumed to attain the optimum. `referenceExactStatewise_transport` further preserves the actual target Born probability for every input, sufficient to support coordinate identification of the corresponding worst-case problem; the three current files do not separately name the final equality of exact worst-case optima.

The verification per-state equality first compares all state scores for the same measurement. `range_referenceVerificationStatewise` preserves the inner state range, `referenceVerification_worst_transport` preserves its `sInf`, and `range_referenceVerification_worst` then compares the sets of worst-case scores of all POVMs. The worst-case quantifier order thus remains: choose one measurement, take its worst input, then optimize over measurements, namely `sup_M inf_x`, without swapping to `inf_x sup_M`.

### The actual verification test

`referenceReportProjector` is the actual joint projector for the report's complete assignment. `referenceReportProjector_transport` proves its actual unitary conjugacy to the canonical projector.

`referenceVerificationStatewise` sums, over reports, the learner's output probability multiplied by the report projector's Born acceptance probability on one original input copy. The learner uses the k-copy tensor power; the test uses the density matrix of an independent copy, which is not counted in k.

For a frame adapted to fixed constraint W, `verificationPayoff_referenceReport` identifies the original `verificationPayoff` of the forgotten report with the same Born score. This equality follows from the existing outcome-averaged Lüders payoff theorem; equivalence is not introduced as a new assumption. Its finite-parameter hypotheses include W being a valid `Constraint`, M being a `Lagrangian`, and `W.subspace ≤ M.val`.

## Assumption and boundary checklist

| Interface | Explicit or type-carried assumptions | Limits on interpretation |
| --- | --- | --- |
| Frame, state, report, measurement, and verification transport | Natural p,n,m,b,k; `[Fact p.Prime]`; R is an `OrderedLagrangianFrame p (m+b)` (general state transport uses n); reports and assignments satisfy their types' validity conditions | n=m+b already encodes m≤n; no k≤n, n>0, odd-p, or extra Clifford-implementation assumption. |
| `verificationPayoff_referenceReport` | The prime and finite-dimensional conditions above; `W : Constraint p (m+b) m`; `M : Lagrangian p (m+b)`; `hWM : W.subspace ≤ M.val`; any actual input state and corresponding refined report | Identifies only that refined report's original score; does not show that refined reports cover all original reports. |
| `reference_probability_le_converseEnvelope` | `k ≤ m+b` and `0 < m+b`, in addition to the conditions above | The finite-envelope theorem excludes n=0; its signature cannot support a claim of a numerical bound for every n,k. |
| `reference_common_converse_source` | Fixed prime p; natural-valued sequences m,k; reals a,b with `0≤a<1`, `0<b≤1`; `k(N)-aN=o(N)`, `m(N)-bN=o(N)`; eventual `m(N)≤N`; any ordered frame in dimension `m(N)+(N-m(N))` for each N | Concludes positive J for exact identification, a common o(N²) remainder, an eventual exponential bound, a normalized-logb limsup bound, and convergence to zero. There is no W or verification-score parameter. |

Odd and even primes: the type assumptions require only primality, so p=2 is included. Full finite phase encoding, the actual XZ section cocycle, and its correction participate in the transport. This review found no division by 2 or compression of binary phases to only ±1 that loses assignments. This conclusion relies on the proved all-prime Clifford and PhaseEncoding interfaces; it does not mean that this document reaudits every underlying proof.

Zero dimensions and zero copies: transport theorems have no positive-dimension or positive-copy assumptions. For n=0, m=b=0, and the original definitions still handle empty direction families, zero-subspace assignments, and one-dimensional matrices. k=0 uses the actual zeroth tensor power and the same POVM bijection. Neither m=0 nor b=0 is additionally excluded. The finite converse's positive-dimension assumption must be retained; the asymptotic theorem makes only eventual statements and does not silently apply the positive-dimensional envelope at the finite N=0 boundary.

## Obligations not yet closed

### Verification near events and asymptotic decay

Convergence of exact-target identification to zero does not by itself imply decay of the verification score. Even if incorrect reports are known to have acceptance probability at most 1/p, this only gives an upper bound that does not vanish with n. The paper's actual bounded-list/graded-to-exact argument is therefore needed; neither error probability nor that fixed score gap can replace it.

The paper's `lem:generic-original-score-spectrum` (approximately line 6425), `lem:generic-bayes-bounded-list-conversion` (approximately line 6505), and `thm:generic-original-bounded-rank-graded-to-exact` (approximately line 6634) require the following steps for the actual original reports and inputs:

1. Define compatibility and distance, and prove that each valid basis-free report's actual Born score is 0 when incompatible and a negative integer power of p when compatible; correctness must retain the original report meaning.
2. Prove the required finite-list upper bound for the actual near event at distance at most D, and bound that event's probability by the list factor times the generic exact Bayes optimum. The report alphabet may be larger than the target alphabet; their equality must not be assumed.
3. Prove that the far-event contribution is at most `p^(-(D+1))`, then choose D tending to infinity slowly enough that list growth does not exhaust the existing Jn² exponent, yielding decay of generic verification.
4. Add back the actual exceptional mass for the original full prior, using comparison directions appropriate to average and worst-case scores.

The three reviewed modules provide the physical transport needed for these steps but do not state or prove the complete near-event chain. The refined case's `cor:graded-score-to-zero` (approximately line 6320) and the original basis-free graded-to-exact theorem must not be conflated into an automatically instantiated conclusion. This document reports only that explicit scope limit; it does not infer that other modules outside this review have made no subsequent progress.

### Original Main and overall release

At the reviewed commit, `StabilizerLearning/Main.lean` defines the proposition `FixedWNoCopyRateDiscount`, quantifying over all primes and invoking `FixedConstraints.NoCopyRateDiscountForPrime`; its comments explicitly require the release gate to find theorem `fixedW_noCopyRateDiscount` with the exact type. The file does not yet provide that proof.

Thus this review supports the claim that source interfaces exist for exact physical equivalence for any public reference frame and its exact converse. It does not support the claim that the original Main, original fixed-W verification, direct direction, and no-discount rate conclusions for all four optima are closed. Final acceptance must still connect the original statements item by item, establish reachability from the formal root imports, run the prescribed checks and clean rebuilds, and retain their respective evidence; this review does not replace that acceptance.
