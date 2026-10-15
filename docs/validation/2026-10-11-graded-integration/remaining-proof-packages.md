# Remaining proof packages after the graded candidate

This is a read-only dependency assessment of frozen `583897b`, not a collection
of new proved bounds. It does not change the public definitions or accept the
candidate before `comparison.json` passes. No calendar duration is inferred
from this assessment.

## Actual unrestricted statewise decoder

The pinned mathlib has positive matrix square roots, spectral decomposition and
continuous functional calculus. The project does not yet have a complete actual
PGM/support inverse, its normalization, or a Gram-square-root per-state success
identity. Ordinary `Matrix.inv` is zero on singular matrices and cannot serve as
the support inverse.

A proposed route uses a column matrix A of pure states, G=A* A, spectral support
inverse square root B, and V=A B. One must prove VV* is the support projection,
construct the effects from columns of V, and complete them with I-VV* at a legal
output. The relation to the actual density matrices and tensor states must also
be proved. No normalization or Gram identity may be supplied as a premise.

The proposed diagonal inequality with H=sqrt(G), diag(G)=1, is
`H_ii^2 >= 1 - sum_(j != i) |G_ij|^2`. Scalar/CFC and polynomial-factorization
routes have been identified but are not formalized in the frozen source. A
statewise bound may avoid proving full ensemble transitivity or PGM optimality
first; the paper's stronger optimality statements would remain separate.

## Actual overlap shell and state-uniform error sum

Already available:

- `Quantum.ProjectorOverlap.trace_jointProjector_overlap` and
  `born_jointProjector_overlap` give the full phase-compatible overlap spectrum.
- `Quantum.stabilizerLabelStateEquiv` gives distinct physical states without
  overcounting labels; `card_assignmentRestrictionFiber` and
  `card_compatibleAssignments` give the actual p^r compatible phase factor.
- `tensorPower_mul` and `trace_tensorPower` give tensor overlap identities.
- `card_rankSubspaces_le`, `card_symmetricMatrices_prime`, reference-frame
  standardization and transverse-graph equivalences provide local counting tools.
- `Bounds/Asymptotic.lean` already proves the scalar damped-tail limit when the
  signed learner-copy overhead k-n tends to infinity.

Still needed: for fixed L0 and K<=L0 of codimension r, construct an injection
from the actual fiber `{L | L intersect L0 = K}` into r-dimensional symmetric
graph data (a bijection would prove the stronger literal shell formula).
An adapted frame and deletion of the common tail require a new, reversible
subspace argument; the existing whole-space transverse graph theorem does not
already supply this quotient bridge. A full ambient Grassmannian overcount
would lose the unit-rate threshold and cannot replace it.

Then define the actual per-state overlap energy, group it by intersection
codimension, and combine the shell count with the exact p^r compatible phase
count. A sufficient target is four times the existing damped tail, uniformly in
the input. The k=0 case cannot silently remove incompatible terms because
0^0=1; the asymptotic direct regime eventually has k>0. The zero-dimensional
empty error sum must also be covered.

## Original fixed-W direct and final rates

Even after a legal unrestricted decoder succeeds statewise, the current generic
target machinery alone does not cover every exceptional input. The all-input
dimension formula, deterministic legal complement/report choice and POVM
postprocessing need closure. Finally prove all four original uniform limits to
one and the original liminf/sInf copy-rate identities before the unchanged Main
can pass its strict release gate.

Literal Gaussian shell formulas and kappa constants, refined-verification
interfaces, and complete covariance statements remain separately tracked.
They must not be called proved because an alternative sufficient bound closes
the original converse. The exact precedence of these stronger interfaces is
distinct from the minimal route to a direct success bound.

Reviewers: `/root/clifford_implementation` (matrix/decoder primitives) and
`/root/frame_geometry` (actual overlap shells and all-input postprocessing).
