# Independent semantic review of phase-compatible list counting

Review date: 2026-10-11. The reviewer inspected the actual Lean definitions and proofs in the independent counting directory without editing either the counting or integration directory. No blocking mathematical or interface issue was found within the scope below. Full root builds, clean reconstruction, and the all-declaration axiom audit remain the responsibility of the integration acceptance records.

## Reviewed sources

Counting-branch commit: `c9ab64c58aa940f468c989a5b5e6eff316a186df`.

- `FixedConstraints/CompatibleListCounting.lean`:
  `23c43e12a4ab47df9f59fe924a6b7df156be7971f01de0bf0632697b459e3cf8`
- `Quantum/AssignmentExtension.lean`:
  `48358c083610e58f19001e900cc597358ed518c1d814e5ee759356e385ed01ec`
- `FixedConstraints/CompatibleList.lean`:
  `7aee48fbda5aafb6d1cf5b31bfa1f6e09ce0c3f46bba357450ae54f63dbfe7b9`

These are complete file SHA-256 hashes for the initial review. Byte-level correspondence after the integration freeze is checked separately at the end of this document.

## Mathematical and interface checks

1. `genericCompatibleList` retains the target realized by an actual generic physical input, the original report-distance condition, and phase compatibility on the entire intersection. Its centre may still be any original legal report. The counting argument does not replace this actual list by an assumed one.

2. The distance condition implies that the intersection has dimension at least `m-D`. `exists_le_finrank_eq` constructs an actual subspace from a linearly independent family; `phaseReportCoverEncode` chooses one such common subspace `I` for each target. This choice may depend on the target: a covering count does not require one `I` shared by all targets.

3. The covering object retains the target's complete legal report subspace `K` and assignment `η`. `phaseReportCoverEncode_injective` recovers the original report directly from that object, so choosing a common subspace does not merge distinct targets. Additional objects in the cover only increase the upper bound.

4. Equality of phases on the full intersection implies equality on the selected `I` through the actual restriction map. `ReportsCompatible.restrict_common` compares the finite assignment values for the original Pauli section; it does not discard phase information. The cover permits additional reports incompatible on a larger intersection, but this is an explicit and valid relaxation for an upper bound.

5. The exact fibre theorem has the correct direction. `I ≤ K` gives a restriction map from `Assignment K` to `Assignment I`, and the assignment to extend is the centre report's assignment restricted to `I`. Isotropy of `K` comes from the original `ReportSubspace W`; isotropy of the smaller space follows from inclusion. `AssignmentExtension` constructs character extensions through a linear retraction, then obtains surjectivity through the proved assignment/character torsor equivalence. Equal fibre cardinalities and the total assignment count yield exactly `p^(dim K-dim I)`; existence and the fibre count are not premises.

6. Two interval-subspace counts respectively bound `I ≤ r.K` and `I ≤ K ≤ PhaseSpace`, with parameters satisfying the actual dimension conditions. The second count relaxes the set of legal report spaces through an injection while retaining the isotropy needed for the phase fibre. For `a=m-D`, the total exponent is
   `(m-D)D + D(2n-m) + D = 2nD-D²+D`.
   Dropping the nonpositive term `-D²` gives `16*p^(2nD+D)`, and `D≤m` then gives the asymptotic interface `16*p^(2nD+m)`. The maximum-list bound holds simultaneously for all centres and all original fixed `W`.

7. At `D=0`, the selected `I` has the same dimension as the centre, and a candidate `K` contains `I` with the same dimension. The actual phase fibre has size `p^0=1`. The current bound with constant 16 is not sharp, but it is valid. If `m=0`, then `D≤m` forces `D=0`, covered by the same proof. At `D=m`, `I=0` and the fibre has size `p^m`; no zero-dimensional division arises. When `n=0`, the constraint `m≤n` places the problem in this boundary case.

8. The proof requires only `Fact p.Prime`; it introduces no odd-prime, `p≠2`, or invertibility-of-two condition on phases. Character extension, the existing assignment-encoding equivalence, and the phase restriction therefore include characteristic 2.

## Limits of the conclusion

This review establishes a uniform finite upper bound for the actual phase-compatible list and the exact count of assignment-restriction fibres. This suffices to connect the proved graded-to-exact comparison to the asymptotic remainder for the uniform exponent `J`.

The paper's sharper exact Gaussian shell count and original exact list formula are not supplied by these proofs and must remain open. The covering injection is not a parameterizing bijection between the original list and the cover, and the two Grassmann bounds are not equalities. This limitation does not prevent use of the present finite upper bound in the original verification-to-zero result.

This review does not upgrade the main theorem from statement only to proved. Its final status depends on the actual main proof chain, the axiom audit, and the remaining direct direction.

## Recheck of the integration freeze

Mathematical freeze `583897b83f2714c9b1a4d27fb1cfd2fc988ee7e8` was rechecked read-only:

- `CompatibleListCounting.lean` is byte-identical to the reviewed baseline above.
- `CompatibleList.lean` is byte-identical to that baseline.
- The frozen SHA-256 of `AssignmentExtension.lean` is
  `b75ab5226db74a085c7058f43e8c4c4a382eb1cd1461a62032930b07b04f73df`.
  The only substantive change from the baseline is the addition of the corollaries `card_compatibleAssignments` and `natCard_compatibleAssignments`; all earlier definitions and proofs retain their original bytes.

The two added corollaries were reviewed mathematically. Fix the centre's original assignment on `V`, restrict it to the actual intersection `U⊓V`, and apply the existing exact restriction-fibre theorem to `U⊓V≤U`. The number of candidate assignments is `p^(dim U-dim(U⊓V))`. The first corollary applies the proved fibre theorem directly; the second only converts finite-cardinality notation. Isotropy of the extension space `U` is an explicit parameter. The centre supplies an actual `Assignment V`, without assuming any further existence or counting formula for compatible assignments. The restriction direction and boundary cases are correct; no new blocker was found.

This independent semantic review therefore covers the frozen versions of all three files and the two added corollaries. The main task reported completion of the root build and actual proof-dependency preflight. Formal clean reconstruction and the all-declaration axiom audit were still running when this document was updated; this review does not record them as passed in advance or mark the project main theorem complete.
