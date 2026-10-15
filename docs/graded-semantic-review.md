# Graded verification semantic review

Date: 2026-10-11. Reviewer: graded-bayes, working in its own cloud directory.
Review scope is read-only inspection of the current integration candidate.
This is a semantic review, not a substitute for whole-root compilation,
fresh reproduction, or the complete declaration/proof-dependency audit.

## Candidate and verification status

Final mathematical freeze reviewed: `583897b83f2714c9b1a4d27fb1cfd2fc988ee7e8`
on private `codex/graded-integration`, relative to accepted mathematical base
`ff7e57b13fb0bae723c48f969daf72fef590f972`. The reviewer independently confirmed
the integration directory was clean at this exact commit and re-read the changed
counting and final converse wrapper. All five files below were read from the
frozen integration directory.

| Source | SHA-256 |
| --- | --- |
| Bounds/GradedAsymptotics.lean | a8c1f73184005b3830c2dab4122c86103e898645a83407f7e5f1fe9ad2c50c98 |
| Bounds/VerificationConverse.lean | e76d59c71ccb4602447f366f4a86c869f2e8de7cad2cc04fe7ad082185c5b25e |
| FixedConstraints/CompatibleListCounting.lean | 23c43e12a4ab47df9f59fe924a6b7df156be7971f01de0bf0632697b459e3cf8 |
| FixedConstraints/CompatibleVerification.lean | 55935d04141b5f8fc6e0679be20629bfae331689d6d4dc93d54a3bdb853fb109 |
| FixedConstraints/GradedComparison.lean | 975967d53446782cf46ec064d085ae4191f8146b5fe40530ff63744ed298aec5 |

The asymptotic scalar proof, compatible spectrum, and graded comparison are
byte-identical to the first review. The changed count now genuinely uses exact
phase-restriction fibers. The final wrapper now returns both the original common
exact bounds and all four original uniform limits at zero.

The reviewer also independently compared base and freeze Git blobs for Main,
FixedConstraints/Rates, FixedConstraints/Task, Quantum/Finite, Quantum/Stabilizer,
Quantum/Pauli, the paper source, lean-toolchain, lakefile.toml and
lake-manifest.json. All ten are byte-identical.

No semantic blocker was found in the frozen candidate. The coordinator reports
a successful whole-root build and a successful precheck of 28 selected new
proof links; this reviewer did not independently rerun those checks. The two
clean/fresh acceptance runs and the complete declaration/proof-dependency audit
remain **pending**, not accepted by this review.

## Original meaning and actual events

The neighborhood is the original report alphabet filtered by three conditions:
actual generic-target realizability, distance at most D, and equality of the
original finite phase assignments restricted to the intersection. In particular,
the near event is not the earlier distance-only event.

`genericLabelReport_inf` uses the legal report condition K ≤ W-perp to identify
the report's intersection with the actual input Lagrangian and with the generic
target. `reportsCompatible_genericLabel_iff` reverses the restriction equality
where necessary, so the order of center and target does not alter compatibility.
The resulting spectrum is the established original Lüders payoff.

Outside the actual list, the input target is already proved realizable. Thus
either the phase restrictions disagree and the actual payoff is zero, or the
distance exceeds D and the existing spectrum gives the tail p^(-(D+1)).
No compatibility or event-probability premise is added.

## Prior and measurements

The mean remains over `GenericState W`, which consists of the actual distinct
generic physical input states. It is never replaced with a uniform distribution
on distinct targets. The target map may have unequal fiber sizes.

The randomized list decoder outputs into the original complete `Report W`
alphabet. It is an actual positive, normalized POVM with leftover weight sent
to a legal fixed report. Its effects are not assumed positive or normalized.
The exact score identity uses the already proved uniqueness of the generic
correct report, then bounds this concrete decoder by the supremum over all
original `Learner W k` measurements.

The full-prior step uses the proved decomposition of the original distinct-state
uniform prior and the actual `exceptionalProbability W`. The passage to an
additive bound uses positivity, not an assumed exceptional error.
The final worst-case result follows from the established original
`optimal_worstCase_le_average`; it does not exchange supremum and infimum.

## Counting and common exponent

The frozen counting proof constructs an injective encoding of actual close,
phase-compatible reports into `PhaseReportCover`. A cover element consists of a
common (m-D)-subspace I, a legal report subspace K containing I, and an assignment
whose restriction to I equals the center's actual phase assignment.
`ReportsCompatible.restrict_common` proves that the actual compatible event
really maps into this restriction fiber.

The cover's phase factor is the proved exact restriction-fiber cardinality
p^(m-dim I)=p^D, using the genuine assignment-extension theorem. The two interval
Grassmannian bounds and this exact fiber give 16 p^(2 n D + D). The public coarse
interface derives 16 p^(2 n D + m) from this stronger bound using D ≤ m.
Consequently the main verification chain actually depends on the phase-fiber
proof, even though it retains the earlier, more generous asymptotic envelope.

The older all-assignment cover remains available as a separate lemma. It is not
the proof used by `genericCompatibleListSize_le_coarse` at this freeze. The
ambient dimension is still overcounted by the full 2n-dimensional phase space.

This is sufficient for the requested verification-decay conclusion: with
D = floor(sqrt n), the additional base-p logarithmic cost
2 n floor(sqrt n) + m + log_p 16 is o(n²). The proved physical finite envelope
therefore retains the same common quadratic exponent J.
It does **not** prove the sharper Gaussian shell expression in the paper's
list-count lemma; that sharper lemma must remain separately open in the map.

The remainder and the eventual threshold are functions only of p, the limiting
rates, and the sequences m and k. They are chosen before the quantifier over W.
The count is derived at the actual W, and the same W-independent envelope
bounds every such instance. The final epsilon modulus therefore has the
original uniformity in W.

## Feasible domain and boundaries

- All primes are handled by the same declarations with only `Fact p.Prime`;
  no odd-prime assumption is introduced, including in phase compatibility.
- The limiting hypothesis beta > 0 is the original converse domain. Beta = 1
  is included. The transition alpha = 1-beta uses the already established
  piecewise common J and its uniform remainder.
- Alpha = 0 and zero copies are not excluded by the finite graded theorem.
  Alpha = 1 is excluded by the original converse premise alpha < 1; no claim
  is made there.
- The finite graded comparison holds for every natural D. The coarse count
  requires D ≤ m, and the asymptotic proof actually derives that condition
  eventually from beta > 0.
- The finite envelope requires n > 0 and k ≤ n. Both are obtained eventually
  from the original scaling assumptions. Ignoring this finite prefix is valid
  for the original UniformLimit statement.
- `fixedConstraint_uniform_converse` now returns the complete converse clause:
  the unchanged original exact common-exponent bounds with one remainder and
  constant chosen before every W, together with `FourUniformLimits p m k 0`.
  It combines the already proved exact clause with the new verification limits.
  Its weaker hypotheses do not remove any original case: the original
  nonnegative alpha, beta ≤ 1, and AllowedDimensions hypotheses can simply be
  retained when applying it.
- Direct achievability at 1, exact-rate identities, and the full Main theorem
  remain separate obligations. No final Main proof is claimed.

## Suggested proof dependencies for the audit

These are concrete local declarations referenced by the proof chain.
The audit must confirm them in the frozen proof terms, rather than treating
this list as evidence that checking has already occurred.

| Consumer | Required dependency |
| --- | --- |
| Quantum.POVM.boundedListDecoder | Quantum.POVM.stochasticPostprocess |
| Quantum.POVM.boundedList_event_le_decoder | Quantum.POVM.born_stochasticPostprocess |
| Quantum.POVM.boundedList_uniform_le_decoder | Quantum.POVM.boundedList_event_le_decoder |
| FixedConstraints.verificationPayoff_eq_generic_spectrum | FixedConstraints.verificationPayoff_eq_intersection_spectrum |
| FixedConstraints.verificationPayoff_eq_generic_spectrum | FixedConstraints.reportsCompatible_genericLabel_iff |
| FixedConstraints.verificationPayoff_le_tail_of_not_mem | FixedConstraints.verificationPayoff_eq_generic_spectrum |
| FixedConstraints.verificationPayoff_le_tail_of_not_mem | FixedConstraints.verificationPayoff_le_inv_prime_pow_of_codim |
| FixedConstraints.verificationStatewise_le_compatibleNearProbability_add_tail | FixedConstraints.verificationPayoff_le_tail_of_not_mem |
| FixedConstraints.compatibleNearProbability_mean_le_list_mul_exact | Quantum.POVM.boundedList_uniform_le_decoder |
| FixedConstraints.compatibleNearProbability_mean_le_list_mul_exact | FixedConstraints.genericExactPerformance_le_optimal |
| FixedConstraints.genericVerificationPerformance_le_graded_exact | FixedConstraints.compatibleNearProbability_mean_le_list_mul_exact |
| FixedConstraints.optimal_verification_average_le_graded_exact | FixedConstraints.verificationPerformance_average_le_exceptional_add_generic |
| FixedConstraints.verificationPerformance_average_le_exceptional_add_generic | FixedConstraints.full_mean_le_exceptional_add_generic |
| FixedConstraints.phaseReportCoverEncode | FixedConstraints.ReportsCompatible.restrict_common |
| FixedConstraints.card_phaseReportCover_le | Quantum.natCard_assignmentRestrictionFiber |
| FixedConstraints.card_genericCompatibleList_le_phase | FixedConstraints.phaseReportCoverEncode_injective |
| FixedConstraints.card_genericCompatibleList_le_phase | FixedConstraints.card_phaseReportCover_le |
| FixedConstraints.genericCompatibleListSize_le_phase | FixedConstraints.card_genericCompatibleList_le_phase |
| FixedConstraints.genericCompatibleListSize_le_coarse | FixedConstraints.genericCompatibleListSize_le_phase |
| genericExactOptimal_le_converseEnvelope | FixedConstraints.genericExactOptimal_le_physicalIdentification_general |
| genericExactOptimal_le_converseEnvelope | physical_probability_le_converseEnvelope |
| genericCompatibleList_mul_exact_le_envelope | FixedConstraints.genericCompatibleListSize_le_coarse |
| fixedConstraint_verification_le_countingEnvelope | FixedConstraints.optimal_verification_average_le_graded_exact_additive |
| fixedConstraint_verification_le_countingEnvelope | FixedConstraints.exceptionalProbability_le_inv_pow |
| tendsto_gradedConverseRemainder_div_sq | tendsto_converseRemainder_div_sq |
| tendsto_gradedConverseRemainder_div_sq | tendsto_natSqrt_ratio_zero |
| fixedConstraint_verification_uniform_bounds_source | fixedConstraint_verification_le_countingEnvelope |
| fixedConstraint_verification_uniform_bounds_source | eventually_natSqrt_le_visible |
| fixedConstraint_verification_uniformLimits_source | tendsto_gradedConverseEnvelope_zero |
| fixedConstraint_verification_uniformLimits_source | tendsto_gradedTail_zero |
| fixedConstraint_verification_uniformLimits_source | FixedConstraints.optimal_worstCase_le_average |
| fixedConstraint_four_uniform_limits_zero | fixedConstraint_exact_uniformLimits_source |
| fixedConstraint_four_uniform_limits_zero | fixedConstraint_verification_uniformLimits_source |
| fixedConstraint_uniform_converse | fixedConstraint_exact_uniform_converse |
| fixedConstraint_uniform_converse | fixedConstraint_four_uniform_limits_zero |

The assignment-extension part of the frozen count has these additional links:
`restrictAssignment_surjective → restrictionCharacterHom_surjective`,
`restrictAssignment_surjective → assignmentCharacterEquiv_restrict`,
`card_assignmentRestrictionFiber → card_assignmentRestrictionFiber_eq`,
`card_assignmentRestrictionFiber_eq → assignmentRestrictionFiberEquiv`, and
`card_compatibleAssignments → card_assignmentRestrictionFiber`.
The exact restriction-fiber theorem is now on the actual compatible-list to
original-verification chain, through `card_phaseReportCover_le`. The direct
intersection corollary `card_compatibleAssignments` is additionally available
for the later sharper shell count.
