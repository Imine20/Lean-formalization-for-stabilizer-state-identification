# Original fixed-W exact converse: independent quantifier review

## Fixed review source and scope

The primary reviewed commit is **`89e9fc4766aaf41613521ab36dbef75fde20a30e`**, on private branch `codex/fixedw-geometry`. Directly reviewed:

- `StabilizerLearning/Bounds/FixedConstraintConverse.lean`, SHA-256 `e93a6c089e80838e0be484edc81b6f357a39ac3371da6a5e62747f5e4bd201e1`.
- `StabilizerLearning/FixedConstraints/Rates.lean` at the same commit, SHA-256 `38dfbbe055c71bd7384abd6de79d85e11e7f84adb93a1b6fd3b9648df40bd357`.
- `FixedConstraints/OperationalComparison.lean`, `Bounds/PhysicalConverse.lean`, `Bounds/SourceScaling.lean`, `Bounds/ConverseExponent.lean`, and `Bounds/ConverseAsymptotics.lean` at the same commit.

The exceptional-probability interface was also checked in `FixedConstraints/ExceptionalProbability.lean` at frozen commit **`2abbe93813808605a46eb1b03030db68bf67cda3`**. That file is not in the Git tree of `89e9fc4`; it is an independently frozen dependency used by that development build and must be included with its dependency chain during integration. Accordingly, this review does not describe `89e9fc4` alone as an import-closed or cleanly rebuilt snapshot.

The source paper is `paper/main-stabilizer2.tex` at the same `89e9fc4` commit, with content SHA-256 `c172bf686f08d7c0b643fa45b29323ba07416c494db6531edd5990fced34bd61`. This review focuses on the exact converse and uniform-zero-limit portion of `thm:fixed-W-no-discount` (approximately lines 1398–1452) and traces its exact-identification exponent to `thm:refined-exact-converse` (approximately lines 705–720).

**Conclusion: no substantive weakening of the original `Rates` exact-converse quantifiers was found in the new interface.** `fixedConstraint_exact_uniform_converse` supplies one explicit remainder and C=1; the remainder, constant, and eventual threshold are independent of W. It also directly supplies the two exact `UniformLimit` conclusions in their original definitions. The average bound separately retains the `p^(-m_N)` exceptional term and is not rewritten as a quadratic-J-exponent bound on average success. The conclusions include α=0, β=1, and α+β=1.

This is a read-only semantic review of source code. It did not recompile mathematical modules, rerun the axiom audit, or perform a clean root build. The reviewer participated in constructing the exceptional-probability dependency but did not implement the new converse file under review. This document does not claim an independent revalidation of the entire underlying counting and physical-transport chain. This delivery adds only the review document and changes no mathematical files.

## Itemized correspondence to the original Rates

After fixing p, β, α, m, k and their dimension/rate assumptions, the original `NoCopyRateDiscountForPrime` requires:

`∃ e C, NegligibleQuadratic e ∧ 0 ≤ C ∧ ∀ᶠ n, ∀ W, [worst-case bound ∧ average bound]`.

The new `fixedConstraint_exact_uniform_converse` directly returns this shape, with the exponent explicitly using **`FixedConstraints.converseExponent`**, and also returns:

`UniformLimit p .exact .worstCase m k 0 ∧ UniformLimit p .exact .average m k 0`.

It still refers to the original `optimal`: the domain is all collective learner POVMs on the original `Report W` alphabet. Worst case takes the infimum over all original distinct states for each measurement, then the supremum over measurements; average takes the uniform average over all original distinct states, then the supremum over measurements. The final theorem does not replace the original target with a chart target or a generic-only average.

| Original requirement | Check result |
| --- | --- |
| The same e for worst case and average | The proof chooses exactly `e N = converseRemainder p a b N (m N) (k N)`; both bounds use that same e. |
| e and C precede all W | The existential quantifiers are outside `∀ᶠ N, ∀ W : Constraint p N (m N)`; the remainder is not chosen separately for each W sequence. |
| e satisfies the original `NegligibleQuadratic` definition | `tendsto_converseRemainder_div_sq` directly proves `e N / N² → 0`, rather than merely a little-o property along a particular W subsequence. |
| The average exceptional term is `C*p^(-m_N)` | C is explicitly 1, with nonnegativity supplied by `zero_le_one`; the exceptional term is separate from the J envelope. |
| The limit is uniform over all W | The original `UniformLimit` definition is used to construct one ε threshold before introducing arbitrary n and W. |
| Both original exact copy rates equal 1 | This module neither states nor proves those equalities; the exact converse and two zero limits only provide inputs for the corresponding lower-bound direction. |
| The original `FourUniformLimits ... 0` | This module supplies only the two exact components, not the two verification components. |

These uniformity claims fix p, α, β, and the sequences m,k; the remainder and ε threshold may depend on those parameters. The original `Rates` does not demand a common threshold across all primes or all rate sequences either, and the new interface does not make such a stronger claim.

## Common remainder and consistency of the two J definitions

The beginning of the new module uses `StabilizerLearning.converseExponent`, while the original `Rates` uses `StabilizerLearning.FixedConstraints.converseExponent`. Both definitions in the reviewed snapshot are:

- `β*(1-α-β/2)` if `α ≤ 1-β`;
- `(1-α)^2/2` otherwise.

The final interface explicitly names the original `FixedConstraints.converseExponent`; the proof ends with

`simpa only [one_mul, FixedConstraints.converseExponent, converseExponent]`

to unfold both definitions into the same expression. The two similarly named constants are not merely asserted to be the same, and their equality is not an extra assumption.

The common remainder comes from the actual finite-envelope identity `converseEnvelope_eq_rpow_remainder`. It is defined as the logarithm of the finite prefactor divided by `log p`, plus

`N² * (J(α,β) - J(k_N/N,m_N/N))`.

`converseLogOverhead` includes every prefactor term, including the finite exponent's `+k`. `tendsto_converseRemainder_div_sq` uses the two actual ratio limits and continuity of J to prove decay of the normalized remainder. Thus no linear prefactor is dropped, finite parameters are not prematurely replaced by their limits, and different error rates are not silently chosen for different W. The original target does not require e to be pointwise nonnegative, and the new proof needs no such extra condition.

## UniformLimit is not a substitute for a sequencewise limit

The file first gives sequencewise limits for a specified W sequence, then separately proves a stronger uniform interface. The final interface depends on the latter; it does not rewrite “each W sequence separately tends to zero” as uniform convergence without proof.

`fixedConstraint_exact_uniform_envelopes_source` first derives eventual `k_N≤N` from α<1 and the actual rate of k, combining this with eventual N>0. The threshold at this point depends only on scalar sequences indexed by N, before W is introduced. Each W carries `m_N≤N`, so `m_N+(N-m_N)=N`; the same `converseEnvelope p N (m N) (k N)` therefore controls all W.

`fixedConstraint_exact_uniformLimits_source` uses this vanishing envelope for worst case; for average it uses

`((p:ℝ)^(m N))⁻¹ + converseEnvelope p N (m N) (k N)`.

β>0 and `HasRate m β` imply m_N→∞ without requiring monotonicity of m. Primality of p gives p>1, so the inverse-power term vanishes. For every ε>0, the proof first obtains one N from envelope convergence and the uniform finite bound, and only then accepts arbitrary n≥N and W; its quantifiers are exactly the original `∀ ε>0, ∃ N, ∀ n≥N, ∀ W`. Strict `<ε` follows from the envelope eventually being strictly below ε; proved nonnegativity of the original optimum removes the absolute value.

## Average exceptional term and the original full prior

The actual finite bound in `OperationalComparison` is:

`optimal .exact .average W k ≤ δ(W) + (1-δ(W))*physicalIdentificationOptimal ...`.

The new converse first relaxes this to `δ(W)+physical optimum` using nonnegativity of the physical optimum and δ≥0, then applies the proved exceptional-probability bound `δ(W)≤p^(-m)` for the original full uniform prior. `exceptionalProbability` is not an extra input error rate; it is the mass of the actual nongeneric event under the original distinct-state uniform prior.

The resulting average upper bound is therefore

`p^(-m_N) + p^(-J(α,β)*N² + e_N)`,

not `p^(-J(α,β)*N²+o(N²))`. β>0 makes the first term vanish and hence makes the average score tend to zero, but this upper bound generally yields only a linear exponential decay scale for the average. Both the source comments and final statement retain this distinction.

For worst case, the comparison directly gives `optimal .exact .worstCase W k ≤ physicalIdentificationOptimal ...`, with no exceptional term. This direction comes from the proved comparison of the original worst case to generic Bayes and then to the actual chart; the new file does not assume the key operational comparison.

## Assumptions, endpoints, and zero dimension

The final `fixedConstraint_exact_uniform_converse` takes a fixed natural p, `[Fact p.Prime]`, natural-valued sequences m,k, reals a,b, and assumptions `a<1`, `0<b`, and the original `HasRate m b` and `HasRate k a`. It does not additionally require `0≤a`, `b≤1`, or `AllowedDimensions m`, so it directly covers the original target's domain with those conditions.

Omission of a separate `AllowedDimensions` hypothesis does not replace the original dimensions with truncated dimensions: for each actual W, `W.dimension_allowed` already proves m_N≤N. If a dimension is invalid, there is no W at that dimension, and the uniform quantifier is vacuous there. The original target's additional all-N dimension-validity assumption may remain unchanged; when calling the final theorem it is simply a stronger assumption that need not be used. The two earlier converse theorems for specified W sequences obtain validity directly from each `(W N).dimension_allowed`.

Endpoint checks:

- **α=0:** The assumption is `k_N/N→0`, not that k_N is identically zero; the eventual k_N≤N argument still applies. The existing `converseExponent_zero` gives `J(0,β)=β*(1-β/2)`.
- **β=1:** Only `m_N/N→1` is required, without strengthening it to eventual m_N=N. Valid W may leave o(N) dimensions; the same remainder applies. The existing `converseExponent_one` gives `J(α,1)=(1-α)^2/2`.
- **α=0 and β=1 simultaneously:** J=1/2; the piecewise boundary values agree, and positivity of β still makes the exceptional upper bound vanish.
- **α+β=1:** `continuous_converseExponent` and `converseExponent_boundary` ensure no discontinuity or one-sided restriction at the branch boundary.
- **p=2:** Every new interface requires only primality, with no odd-prime condition; the analysis actually uses p>1. The physical and exceptional-probability parts reuse proved all-prime interfaces.
- **N=0:** The finite-envelope theorem explicitly requires N>0; the uniform proof handles this when choosing the eventual threshold. Ratios, remainders, and little-o equivalences use only the eventual positive-dimensional range atTop and do not require changing the sequence's value at N=0. This review does not incorrectly extend the positive-dimensional finite bound to zero dimension.

## Targets not closed by this module

`NoCopyRateDiscountForPrime` also requires two verification zero limits, four uniform limits to one when k_N-N→∞, and both exactCopyRate values equal to 1; none is a conclusion of the new file's final interface. In particular, the full-report verification near-event/finite-list/far-tail argument still needs its own actual theorems and cannot be replaced by the exact-average convergence to zero established here.

The original definition of `AchievableExactRate` includes the existence of a W sequence and a liminf success threshold. The uniform exact converse proved here gives the correct input for excluding achievability at α<1, but this file does not complete the deduction from liminf to a lower bound on the achievable-rate set, direct achievability, or the full conclusion sInf=1.

Thus this review supports the claim that directly usable interfaces exist for the original `Rates`' two uniform exact-converse bounds and two exact zero limits. It does not support the claim that all of `NoCopyRateDiscountForPrime` or the original Main is proved. Root-module reachability, complete dependency closure after integration, and the prescribed build/release checks remain covered by the main task's separate records.


## Subsequent root-freeze check: range of the exact worst-case score

A bounded follow-up review examined root mathematical freeze **`85db6d8ab186d501a41f461d2764d012635c73f8`**. Its `FixedConstraintConverse.lean` and `Rates.lean` are byte-for-byte identical to the reviewed `89e9fc4` content above; `ExceptionalProbability.lean` is identical to the `2abbe93` freeze above, and the required exceptional-probability module is present in this root commit. No additional clean-build or whole-tree dependency-validation claim follows from that comparison.

This follow-up also directly checked two interfaces added in `Quantum/ReferenceVerification.lean` at that root commit:

- `range_referenceExactStatewise`: fix one original refined learner M, use surjectivity of the actual `referenceStateEquiv` to rewrite the full range of canonical-input scores, then use the original per-state Born equality to prove equality with the reference-input range. Different measurements are not chosen for different states.
- `range_referenceExact_worst`: first take `sInf` over the input-score range for each measurement, then use surjectivity of the full `referenceMeasurementEquiv` to prove equality of the ranges of these worst-case scores attainable by all collective POVMs. Applying `sSup` to both sides gives equality of the corresponding optimization problems, still with quantifiers `sup_M inf_x`.

This new interface therefore explicitly lifts the existing exact per-state transport to transport of the complete exact worst-case score set. It neither exchanges inf and sup nor restricts the learner class, and it does not claim a bijection on the original fixed-W full-report alphabet. Its assumptions remain arbitrary primes, valid ordered frames, and natural m,b,k, with no extra positive-dimension, positive-copy, or odd-prime requirement.

The earlier `semantic-review-transport.md` retains its historical assessment of `40239e92d885d4d8e1f70e24980be8cbb58ba0e2`; this section records only the new interfaces checked at the new exact SHA and does not retroactively rewrite the earlier review.
