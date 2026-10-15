# Assignments on arbitrary isotropic subspaces and complete projector families

Proof freeze: **79003a8b1905f94ed8c681ca4bab8ebdb8a3dc1d**. Lean 4.24.0 and the original mathlib lock are retained. The local results below have passed two complete builds and recursive axiom audits; the final main theorem is still **statement only** at this milestone.

## Precisely completed interfaces

All interfaces below are in the StabilizerLearning.Quantum namespace and use the original PhaseSpace, Assignment, jointProjector, and POVM definitions; d denotes the dimension of U.

| Mathematical result | Lean declaration | Status |
|---|---|---|
| Every prime p, every n, and every isotropic U admit an original finite assignment | nonempty_assignment_of_isIsotropic | All dependencies proved |
| The original finite encoding is in bijection with all unit-norm complex assignments satisfying the original cocycle | assignmentComplexEquiv | All dependencies proved |
| Assignments exist if and only if U is isotropic | nonempty_assignment_iff_isIsotropic, nonempty_complexAssignment_iff_isIsotropic | All dependencies proved |
| The complete assignment set is in bijection with the complete character group, and its exact cardinality is p^d | isotropicAssignmentCharacterEquiv, card_assignment | All dependencies proved |
| Projectors for distinct assignments are orthogonal, and all projectors sum to the identity matrix | jointProjector_mul, sum_jointProjector | All dependencies proved |
| Vectors fixed by a projector are exactly the common eigenvectors of the original Pauli equations; its rank is p^(n-d) | jointProjector_mulVec_eq_self_iff, rank_jointProjector | All dependencies proved |
| The direct Fourier projector for any compatible complex assignment equals the original projector after encoding | jointProjector_complexAssignmentEncode, complexJointProjector_mulVec_eq_self_iff | All dependencies proved |
| The complete projector family is an original POVM; every actual Pauli operator z∈U has a complete spectral decomposition | assignmentMeasurement, pauli_eq_sum_jointProjector | All dependencies proved |
| For every original density matrix, the Born probabilities of this complete measurement sum to 1 | sum_assignmentMeasurement_born | All dependencies proved |
| Combined nonemptiness, exact count, orthogonality, identity resolution, positivity, and exact rank | complete_jointProjector_family | All dependencies proved |

The final inputs to existence, counting, and the identity resolution are only primality and the original IsIsotropic U. No reference assignment, common eigenvector, phase encoding, bijection, or completeness result must be supplied externally. The results cover characteristic 2, zero qubits, the zero subspace, and the maximal-isotropic endpoint. For zero qubits the computational basis is a singleton and the Hilbert space is one-dimensional.

ComplexCompatible requires only unit norm and the original multiplication law. Membership of its values in the 2p-th roots of unity is derived by complexAssignment_pow_two_mul; encoding completeness is not built into the definition. The conclusions concern the project's original fixed XZ section and do not additionally claim gauge transport for arbitrary sections.

## Actual proof route

~~~mermaid
flowchart TD
  P[Original Pauli multiplication and unitarity] --> C[Isotropy gives actual matrix commutativity]
  E[Proved common eigenvector theorem for finite commuting families] --> X[Construct a full compatible complex assignment]
  C --> X
  P --> X
  R[Compatibility implies 2p-th roots of unity] --> B[Original finite encoding bijects with all complex assignments]
  X --> N[Every isotropic U admits an original Assignment]
  B --> N
  N --> T[All Assignments biject with the full character group]
  T --> K[Exact counting and phase orthogonality sums]
  K --> I[All original projectors sum to the identity]
  S[Original projector eigenspaces and exact rank] --> F[Complete projector family and actual POVM]
  I --> F
~~~

The common eigenvector theorem proceeds by induction over a finite set, constructing a nonzero invariant subspace and then taking an eigenspace. Algebraic closure of the complex numbers comes from mathlib's proved fundamental theorem of algebra. The reference assignment used in the character parameterization is obtained internally from proved nonemptiness; every sum ranges over all elements of the original Assignment type.

The root chain StabilizerLearning → Main → Verified → CompleteMeasurement covers every formal module in this stage. Audit checks declaration existence, recursive axioms of all project declarations, and actual proof-term dependencies. The final main theorem has no proof yet at this milestone: integration here means inclusion in the formal root build and in audited, reusable mathematical dependencies, not use by a main proof that does not yet exist.

## Acceptance and preservation of meaning

See the [acceptance comparison](validation/2026-10-11-assignment-completeness/comparison.json) and the [independent mathematical review](assignment-completeness-review.md).

- The integration directory deleted its own project cache before a complete rebuild and audit.
- A second directory fetched the exact Git dependencies from scratch and used a separate official mathlib cache; it contained zero project oleans before building.
- Source hashes, complete axiom logs, and kernel dependency graphs agree across both runs. The only allowed axioms are propext, Classical.choice, and Quot.sound.
- Hashes of the original main statement, states, Pauli operators, assignments, reports, success probabilities, and FixedConstraints definitions are unchanged. All mathematical source files predating this stage remain unchanged.
- Both directories reuse a version-checked compiler on the same Linux host; no validation on a second operating system is claimed.
- The strict main-release gate rejects as expected: statement_only. Declaration and audit-edge counts describe coverage, not the fraction of mathematics completed.

## Coordination and revised assessment of remaining work

Another primary process exclusively owns the Mac working directory and connects the physical chart, original target, uniform prior, and all POVMs to the coordinate converse and uniform J. This stage's three proof branches each used separate cloud directories, branches, and caches, followed by integration in one designated directory. The physical-to-coordinate bridge was not developed in duplicate.

Remove four items from the remaining work: general assignment existence, completeness of finite phase encoding, the exact assignment count for fixed U, and the complete projector family. The other process can call these results directly rather than assume them as unproved premises.

Independent acceptance is still needed for arbitrary frame/Clifford transformations, fixed-W operational comparison and exceptional mass, the complete verification reduction, unrestricted direct, and the original main theorem. The standard physical-chart-to-J connection is governed by the other process's frozen source and acceptance evidence; this branch makes no completion claim on its behalf. Counting for fixed U is not counting all Lagrangians or all stabilizer states.

The task list has been reduced using actual proved dependencies, but there are not enough comparable completed examples for a reliable total calendar estimate. The next calibration point is the complete physical-experiment-to-J connection and the subsequent fixed-W/verification results actually proved. Compilation minutes, code volume, and server/GPT runtime are not converted into proof-development time.
