# Actual normalized PGM and pointwise direct interface

Mathematical baseline: Lean 4.24.0, the fixed mathlib commit, and the original Quantum/FixedConstraints definitions are retained. This package adds six modules to the jointly accepted baseline 87597a5 without redefining states, POVMs, Born probabilities, or tensor powers.

## Construction and actual dependencies

For an arbitrary finite rectangular complex matrix S, let G=S†S, B=cfc(x↦(sqrt x)⁻¹)(G), T=SB, and P=TT†. The inverse square root at a zero eigenvalue is 0. Functional calculus on the finite spectrum requires neither a spectral gap nor invertibility of G. The proof establishes T†S=sqrt G, P†=P, P²=P, and PS=S. Assigning the complementary effect I−P, where P is the sum of the rank-one column effects, to one legal outcome produces the original POVM structure. The identity (I−P)S=0 proves that this completion contributes zero probability on every signal.

The unweighted Gram matrix corresponds to unit columns, and the actual Born probability is normSq(sqrt G_ij), with no additional cardinality factor. For unit columns the Gram diagonal equals 1. Writing H=sqrt G, positivity of
(H−I)†(G+2H)(H−I)=G²−3G+2H implies Hi_i≥1−Ei/2. Splitting into Ei≤1 and Ei≥1 then gives correct probability ≥1−Ei. Low energy is not a theorem premise.

A unit vector is constructed from the Hermitian, rank-one, trace-one properties of the original StabilizerState. Full tensor and density identities then give the original k-copy state. Choosing a global phase is only a choice of vector representative; reports remain indexed by the original distinct density matrices, without counting labels multiple times.

## Final interface for the other process

Module: `StabilizerLearning.FiniteCopy.StabilizerPGM`.
Namespace: `StabilizerLearning.Quantum`.

`stabilizerPGM p n k` is an original `POVM (Fin k → Configuration p n) (StabilizerState p n)`.
`stabilizerPGM_success_ge_overlap p n k x` proves
`1 − (∑ y, if y=x then 0 else born (tensorPower y.val k) (tensorPower x.val k)) ≤ born ((stabilizerPGM p n k).effect x) (tensorPower x.val k)`.
`exists_stabilizer_POVM_success_ge_overlap` gives the existential form for that same explicit measurement.

The only inputs are p, n, k, and the original prime instance. Normalization, key matrix bounds, Gram identities, and success-rate bounds are not premises. All primes, n=0, and k=0 are retained. The general construction permits repeated or linearly dependent signals and a singular Gram matrix. A concrete legal outcome in the finite label set is specified only when needed to obtain a POVM on the whole space; nonemptiness of the original ensemble has already been proved.

## Scope and remaining tasks

This package proves pointwise achievability. It does not claim the paper's transitive PGM optimality, equal success probabilities, or mixed-state optimality. Sharp overlap counting, fixed-W postprocessing for all inputs, the four uniform limits to one, and rate/Main are being developed independently by another process. This package does not present any unproved key bound from those tasks as a completed direct result.

Stage status is determined by the complete clean-build and axiom-audit records. Module compilation alone does not establish acceptance of a project milestone.
