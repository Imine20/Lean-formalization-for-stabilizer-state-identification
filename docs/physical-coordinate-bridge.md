# Bridging the Original Physical P_id to the Uniform J Bound

This stage proves that the original physical `P_id` in the standard transverse chart is exactly equal to the existing coordinate optimum, then connects it to the proved finite counting results and uniform `J` converse. The original paper, `Main.lean`, public quantum definitions, and `FixedConstraints` definitions remain byte-for-byte unchanged. Arbitrary reference frames, the fixed-W operational comparison, verification, direct results, and the final main theorem are outside the scope completed here.

## Physical objects are not defined as coordinate images

`TransverseState` is the subtype of the original `StabilizerState` (distinct density matrices) satisfying transversality. The proof first shows that a projector matrix recovers the complete physical label, then establishes a bijection between all transverse Lagrangians and unique symmetric-matrix graphs. The original uniform prior is transported through these bijections; a uniform distribution over labels with multiplicity is not substituted for the uniform distribution over states.

`CanonicalReport` consists of all directions satisfying the reference-dual constraints for the standard public frame, together with a complete original `Assignment` on their actual linear span. Its definition does not require a coordinate realization or an unknown input state. `physicalCanonicalTarget` is constructed from the inverse of the projection on the actual input Lagrangian and the restriction of its original phase assignment. The subsequent theorem `physicalCanonicalTarget_surjective` proves that every legal report is realizable.

The odd-prime and binary branches each establish equality between the original projector matrices and the paper's normalized coordinate densities, a bijection for complete assignments, and a report bijection. The binary branch retains the full ZMod 4 phase; the odd-prime branch retains the actual XZ cocycle, quadratic correction, and original report sign convention. The final theorems do not assume the bijections, normalization, or key physical identities.

## Priors, tensor copies, and all POVMs

`oddPhysicalMeasurementEquiv` and `binaryPhysicalMeasurementEquiv` are actual equivalences of all finite collective POVMs, including positivity and normalization of effect matrices and transformations in both directions. Equality of scores is first proved for every measurement, followed by equality of the complete score sets. This yields equality of suprema without assuming the existence of an optimal measurement.

The k-fold tensor power is taken separately for each original physical state before averaging uniformly over the hidden parameters. The complete physical-state bijection transports the uniform prior to the product distribution on visible and hidden parameters. A tensor power of a mixed state is not substituted for multiple copies of the same hidden state.

Main interfaces:

- `physicalIdentificationOptimal_eq_coordinate`: equality of the optima for all primes and all finite m, b, and k.
- `physical_probability_le_converseEnvelope`: the actual physical probability satisfies the envelope via the finite counting chain, retaining the original full denominator, clipping, and feasible domain.
- `physical_common_converse_source`: the original linear little-o scaling, an explicit uniform o(N²) remainder, the actual logarithmic limsup, and convergence to zero.

The finite equivalence includes m=0, b=0, and k=0. The asymptotic theorem retains 0≤α<1, 0<β≤1, and the task's intrinsic constraint m≤N. The existing uniform optimization chain covers the boundaries α=0, β=1, and α+β=1. The case m=N is the full endpoint of the transverse chart; it does not establish an unconditional task over all stabilizer states.

## Acceptance of the other task's Pauli/projector results

The independent rebuild and full audit evidence for the first source freeze, `491d0ab`, has been incorporated into `validation/2026-10-11-pauli-projectors/`. The eight general Assignment modules from the second source freeze, `79003a8`, were incorporated file by file and revalidated in the complete root dependency chain rebuilt during this stage.

New general foundational results show that every isotropic U admits an original Assignment; every complex phase satisfying the original unit-norm and cocycle conditions has a unique finite encoding; the complete family of assignments has p^dim(U) elements; and the original joint projectors are pairwise orthogonal, sum to the identity, have rank p^(n−dim(U)), and form an actual POVM. These results require no externally supplied base assignment or decomposition. All primes and the zero-qubit case are covered. The number of assignments for a fixed U is not reported as the total number of Lagrangians or stabilizer states.

## Actual dependencies and acceptance

The root entry point imports the modules from this stage. The proof term for the physical converse depends on the physical/coordinate equivalence, odd-prime and binary finite probability bounds, actual moment-completion inclusions, exact completion counts, prescribed-rank bounds, row-space event probabilities, variational optimization over the full feasible domain, and the uniform remainder. `Audit.lean` checks actual reachability within these proof terms rather than relying solely on a manually maintained dependency graph.

An independent semantic review confirmed the scope of the states, targets, priors, POVMs, and all boundary cases. The exact commits used for machine acceptance, source hashes, compilation and axiom logs, comparison between the two runs, and main-theorem release-gate results are recorded in this stage's `validation/` directory.

## Remaining work and schedule

The accepted standard-chart physical bridge, equivalence of all POVMs, physical reduction to the uniform J bound, general assignment existence, and complete projector families are removed from the remaining work. The remaining critical path consists of the symplectic/Clifford realization of arbitrary frames; fixed-W incidence, exceptional mass, and exact and Lüders verification comparisons; unrestricted direct measurements and a uniform statewise success bound; and finally the combination of the four operational limits and the original copy-rate=1 main theorem.

These mathematical branches do not yet have completed end-to-end examples suitable for extrapolation, so no new, spuriously precise calendar or GPU-hour estimate is provided. Acceptance compilation times are used only to schedule cloud CPU resources. The main theorem is still unproved at this stage, and the strict release gate should continue to reject it. The results completed here do not amount to a formalization of the whole paper.

Acceptance commit: `ce043d6c1de0cda69dc3ed6163aedf23717833a5`. The audit covers 1,639 theorems, 2,116 project declarations, and 167 actual dependency checks. The complete audit logs from the two runs are byte-for-byte identical and use only the three standard axioms. The independent cloud rebuild took 1142.603 seconds in total. See the [acceptance records](validation/2026-10-11-physical-coordinate/README.md).
