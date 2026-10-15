# Normalized PGM semantic review

Status: independent read-only review completed for frozen mathematical commit
`a1f4d122949298a9f8dd465dd16f5680287cb275`. The integration worktree was clean,
and all six inspected files were byte-identical to this Git commit. Root build
and proof-link preflight had passed; the full clean-build and axiom-audit runs
were still in progress at this review. This review does not mark the milestone
accepted or replace those checks.

Reviewed modules:

- `FiniteCopy/ColumnMeasurement.lean`
- `FiniteCopy/GramEnergy.lean`
- `FiniteCopy/SupportedSynthesis.lean`
- `FiniteCopy/PrettyGoodMeasurement.lean`
- `FiniteCopy/StabilizerPGM.lean`
- `Quantum/PureStateVectors.lean`

No mathematical blocker was found in the frozen candidate. Every pre-existing
mathematical Lean file under `StabilizerLearning/` is byte-preserved relative
to `87597a5`; the only changed pre-existing Lean file there is the import-only
`Verified.lean` entry. The six new files contain the implementation.

## Original physical objects and normalization

The physical probability is the existing `born E ρ = Re(trace(E * ρ))).
Each chosen vector represents the original rank-one density matrix exactly;
the eigenvalue argument proves unit norm from Hermitian rank one and trace one.
The choices do not create additional ensemble labels: `StabilizerState` remains
the original subtype of distinct density matrices.

The synthesis matrix has unweighted unit columns. Its Gram matrix is exactly
`Sᴴ * S`, so its diagonal is one. The supported synthesis is
`T = S * cfc (fun x => (Real.sqrt x)⁻¹) (Sᴴ * S)`.
This normalization is the uniform-prior pure-state PGM normalization: scaling
every column by the square root of the common prior cancels against the inverse
root. The formal theorem itself uses the explicit construction and exact Born
identity, without relying on that informal equivalence or inserting an ensemble
cardinality into a statewise probability.

## Singular support and completion

The spectral inverse root has value zero at zero. Its use of continuous functional
calculus is valid because every scalar function is continuous on the finite
matrix spectrum. No full-rank or spectral-gap condition is present.

The proof constructs `Tᴴ * S = CFC.sqrt (Sᴴ * S)`, identifies `Tᴴ * T`
with the Gram support, and proves that `P = T * Tᴴ` is Hermitian, idempotent,
positive, and satisfies `P * S = S`. Thus `1 - P` is positive and annihilates
every signal. Assigning this complement to the chosen legal report makes the
effects sum to the full identity and changes none of their Born probabilities
on any ensemble member. Idempotence and support containment appear as hypotheses
only in reusable algebraic helpers; the final PGM supplies their proved values.

The construction permits repeated or linearly dependent signal vectors.
The support lemmas allow empty finite index types. A completed measurement takes
an actual report `i₀`; this is the necessary nonempty outcome witness, and the
stabilizer instantiation obtains it from the existing proved state nonemptiness.

## Statewise bound and boundary cases

For every positive semidefinite Gram matrix with diagonal one, the polynomial
`(H - I)ᴴ * (G + 2H) * (H - I) = G² - 3G + 2H`, where `H = CFC.sqrt G`,
is positive. Its diagonal gives `Hii ≥ 1 - Ei / 2`, with actual off-diagonal
row energy `Ei = ∑ j ≠ i, normSq (Gij)`. The proof handles both `Ei ≤ 1`
and `Ei > 1` internally, yielding `normSq (Hii) ≥ 1 - Ei`.
It assumes neither this matrix inequality nor a bound on the energy.

The final theorem constructs a single normalized POVM and proves its lower bound
for every original stabilizer state. The lower bound is expressed by actual
Born overlaps of original tensor density matrices; it does not assume those
overlaps are small.

All primes, including two, and every natural dimension and copy number are
retained. Tensor-vector identities include zero copies by the empty product.
At zero copies the repeated columns make the Gram matrix singular, already
covered by the support argument. Zero-dimensional physical systems are retained.
No asymptotic positivity or nonzero-copy hypothesis is added here.

## Scope kept open

This package proves finite, statewise achievability by a real normalized PGM.
It does not prove transitive PGM optimality, the exact transitive average-success
formula, or mixed-state quotient-ensemble optimality. It also does not itself
close sharp stabilizer overlap counting, fixed-W report postprocessing, the
four direct limits, copy-rate infima, or the final Main target. Those remain
separate dependencies and must not be marked proved by this package.


## Frozen source fingerprints

SHA-256 values checked against both the worktree and the frozen Git blobs:

| Source | SHA-256 |
| --- | --- |
| `FiniteCopy/ColumnMeasurement.lean` | `938e2b0f20deaeaff78deff821e8155b867a3397848f75a33e6e6eac4f644d71` |
| `FiniteCopy/GramEnergy.lean` | `739a59feed1212beaade2da93927dd68b59f25f3f3f89ecc7bfa6608cf17aa44` |
| `FiniteCopy/SupportedSynthesis.lean` | `7347e9ba49d99bb6c05c20b9041e979be0405be6a3a4f6c024d3eab8915700cd` |
| `FiniteCopy/PrettyGoodMeasurement.lean` | `d9d36721b04b4ce4ebb677c790c42c1bf51535434bfeecef1dfd26117e7dcdc3` |
| `FiniteCopy/StabilizerPGM.lean` | `1955c320d4ccddb45fbfd617c16b788af03b6ffc030bfc282ee461afe65fe0fe` |
| `Quantum/PureStateVectors.lean` | `4b759082c8ac68decec0e394e85d67a2b96593d05095a64886126b5abe3eea5b` |
