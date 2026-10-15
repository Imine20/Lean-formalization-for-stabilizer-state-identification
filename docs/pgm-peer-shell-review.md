# Independent read-only review of exact Lagrangian shell counting by the PGM process

Review date: 2026-10-11 (Asia/Shanghai). Reviewer: the PGM support-algebra task.
Conclusion: no blocking issue was found in the immutable versions and semantic scope listed below. This is a second reviewer's source-level semantic review; it is not presented as independent kernel compilation, an axiom audit, or acceptance of the complete direct argument.

## Immutable review targets

- Coarse geometric bound commit: `46453617bb6b6c772ffce2ce847d8339b5ee3822`.
- Exact counting commit: `b0134e684c52a48fe6da0ba06768abd3abcc920b`.
- `merge-base --is-ancestor` in the private bare Git repository confirmed that the former is an ancestor of the latter.
- All reads used `git show <commit>:<path>`. They did not depend on a worker's mutable working tree and did not write to any worker directory or the Mac project directory.

| File | Git blob | SHA-256 |
| --- | --- | --- |
| `StabilizerLearning/Quantum/LagrangianShellGeometry.lean` | `6482f3f542e31a499e9884cb45a30a775868dc32` | `e2c7d4c7871dd8f5811f9dd9d32c01c694393629520c48b405ee23dca0634612` |
| `StabilizerLearning/Quantum/LagrangianShellExact.lean` | `2be0e7d47c451db3c038de574fee462f4a1dec9b` | `9a32073d1cf9764dad8f7d541320c9e0374835bf45d25e4538ffc9a34c2e4d0f` |

## Original objects and assumptions

The counting domain of the final `card_lagrangianIntersectionFiber_eq` is the original public type
`{L : Lagrangian p n // L.val ⊓ L₀.val = K}`.
The public `Lagrangian` definition is still the subtype of actual phase-space subspaces that are isotropic and have dimension `n`. A matrix parameter space has not replaced the object being counted.

The final interface requires only `[Fact p.Prime]`, an actual `L₀`, `K ≤ L₀.val`, `r ≤ n`, and `finrank K = n-r`. Coordinate realizability, complement existence, a parameterizing bijection, the target cardinality, and probability bounds are not parameters. `shellConstraint` derives isotropy from the given inclusion and constructs the original Constraint from the dimension condition. `adaptedReferenceFrame` is constructed by proved basis extension; no standardization witness is required from the caller.

## Checks of the two proof chains

The coarse-bound file first maps an actual `L` to a complement in `K⊥/K`. Inclusion, quotient dimension, zero intersection, a sum equal to the whole space, and recovery by pullback are all proved. An actual linear projection relative to a fixed complement then encodes this object as a matrix, and the encoding is proved to recover the complement. This establishes only the all-matrices bound `p^(r*r)`; that file does not claim an exact symmetric-matrix count.

The exact-count file additionally establishes a full bijection:

1. On the standard fibre, `shellReduce` removes the shared vertical tail. `shell_fst_tail_zero` uses actual isotropy and single-coordinate vectors in that tail to prove that the first-coordinate tail vanishes.
2. `shell_reduce_fst_zero` uses the original exact intersection identity to show that the kernel is precisely the shared tail. Rank-nullity gives dimension `r` for the reduced subspace, which is also proved isotropic and transverse.
3. `shellInflateMap` reassembles an actual transverse Lagrangian with an arbitrary common-tail vector, proving its dimension, isotropy, and intersection exactly equal to the common tail. `shellReduced_inflated` and `shellInflated_reduced` establish both inverse laws. The second direction explicitly uses `t-shellTailValue w` to restore the difference, rather than proving only injectivity.
4. An arbitrary original `(L₀,K)` is transported by symplectic coordinates adapted to the actual `K`. `shellReferenceFrame_map_vertical` and `shellReferenceFrame_map_tail` send `L₀` and `K` respectively to the required objects. `shellReferenceFrame_intersection_iff` uses intersection preservation by an invertible linear map and injectivity of map to preserve the original exact-intersection predicate in both directions.
5. `lagrangianIntersectionFiberEquivSymmetricMatrices` composes these bijections with the proved classification by transverse graph matrices. `Nat.card_congr` and the proved count of independent symmetric entries give `p^(r*(r+1)/2)`. No step assumes the target exact cardinality.

## Characteristic and boundary cases

- Every new interface requires only primality and includes `p=2`. The reference symplectic-basis correction uses upper-triangular coefficients, without division by two; equivalence between graph isotropy and matrix symmetry comes from the bilinear pairing. Symmetric matrices retain free diagonal entries and are not incorrectly replaced by zero-diagonal alternating matrices in characteristic two.
- `/2` in the exponent is natural-number combinatorial counting, not division in the field.
- `r=0`: the matrix index is `Fin 0`, the parameter space is a singleton, and the formula is one. The original hypotheses imply `K=L₀`, so the fibre is indeed a singleton.
- `n=0`: `r≤n` forces `r=0`. All bases, tails, and assembly maps permit empty indices. No nonempty-index, positive-dimension, or positive-rank premise is used.
- `r=n`: the common tail is zero, leaving the complete transverse graph classification. This boundary is retained.
- `Nat.exists_eq_add_of_le` only rewrites `n` as `r+b`. The original `n-r` dimension condition becomes `b`, without any extra feasibility condition.

## Existing dependencies traced

All of the following were read at exact commit `b0134e684c52a48fe6da0ba06768abd3abcc920b`:

| File | SHA-256 |
| --- | --- |
| `Quantum/ReferenceFrame.lean` | `8d458d4707404159290e915fdfce584c5776a4b155ee9cc811c10c3812f3b5bd` |
| `FixedConstraints/AdaptedFrame.lean` | `b24cedd8b3fb395734fef992f0cc142358d686a32fad53aacff58dffceb76706` |
| `Quantum/TransverseGraph.lean` | `5bb2a097f9f2b12fac65f5e682bb9a1ced037b05246a329f667be206d3dfc339` |
| `Foundations/FiniteCounting.lean` | `aa10f5856aff983563ecb365fac1e5e8386a75c914892c507d8b7f76dce742a8` |
| `Quantum/Stabilizer.lean` | `00eb0c655930879fb9efe38d6f81ae7dd9a5e015c392b99679666d4f988d775d` |

A lexical scan of the two new source files found no `sorry`, `axiom`, or `admit`. This scan is supplementary; acceptance still requires the main process's clean rebuild and recursive axiom audit.

## Coverage and integration requirements

This package completes the exact Lagrangian fibre for a fixed actual common intersection `K`. A complete shell by distance still requires summing over all `K` and connecting the count to phase-compatible assignments, actual state overlaps, and tensor-copy row energy. None of these is an implicit conclusion of the two files. Actual normalized PGM, fixed-W postprocessing for all inputs, and the asymptotic limits to one must also be connected by their respective modules. These scope limitations do not block the exact fibre theorem.

Integration should preserve proof-term dependency checks along the actual main chain:
`card_lagrangianIntersectionFiber_eq` → actual fibre bijection → both inverse laws for the standard fibre and equivalence of the original predicates → original graph-matrix equivalence.
Final acceptance is determined by the integrated commit's build, axiom-audit, and strict Main-gate records.

## Incremental review: from actual Grassmann cardinality to the literal Gaussian product

Immutable commit: `083c3e6dd5f0e1463a5c72502626e85aab465e31`.
New source: `StabilizerLearning/Foundations/GrassmannExact.lean`;
Git blob: `7d49f9d3a4f9992e27807a5926638117a48fdf67`;
SHA-256: `30831796bbf0f262b207dab0b0bd6ecda6de26947c65dc6921f8bb9ad5c6cbf7`.
Conclusion: no blocking semantic issue was found on the file's stated feasible domain `r ≤ n`. This incremental review is also read-only source inspection and does not claim an additional kernel compilation or complete axiom audit.

**Actual counting objects.** `RankSubspaces F n r` consists of all actual r-dimensional subspaces of the original space `Fin n → F`. The new `subspaceIndependentFamily_bijective` reuses injectivity of the existing encoding and adds actual surjectivity. Given an independent family, it takes its actual span, proves that the span has dimension `r` using `finrank_span_eq_card`, and pulls the family back along the span's chosen coordinates to obtain an independent coordinate family. Pushing forward recovers the original family term by term. This equivalence assumes no Grassmann count, frame count, or realizability result.

**Underlying counts and division.** `card_rankSubspaces_mul_card_GL_eq` combines the actual bijection with the pinned mathlib results `Matrix.equiv_GL_linearindependent` and `card_linearIndependent`. The latter's source inducts on the length of an independent family, choosing each new vector outside the current span; its length-zero base case explicitly uses the empty product. It is not a new unproved counting axiom. `Matrix.card_GL_field` is likewise derived from independent-family counting.

`card_rankSubspaces_eq_prod_div` first proves a product identity in natural numbers and then casts it to the reals. For each truncated subtraction, `cast_independent_product` supplies power monotonicity from `i ≤ r ≤ n`, ensuring that `Nat.cast_sub` is not misused as ordinary subtraction. The full denominator product equals the actual cardinality of `GL r F`. That group is finite and contains the identity, so `Nat.card_pos` gives strict positivity. `eq_div_iff hpos.ne'` eliminates the denominator only after nonzeroness is proved. The proof does not silently rely on Lean's totalized division at a zero denominator. Positivity of each denominator factor is not a separate public lemma, but also follows mathematically from the finite-field condition `q≥2` and `i<r`; the file's proof needs only the established nonzero product.

**Agreement with the paper's literal formula.** `card_rankSubspaces_eq_gaussian_product` factors out and cancels `q^i` from the numerator and denominator for each `i : Fin r`. The required `q^i ≠ 0` follows from `Fintype.card_ne_zero` and `pow_ne_zero`. Exponent splitting uses `i≤n` and `i≤r` respectively, so natural-number truncation of negative exponents causes no gap. The resulting right-hand side is
`∏ i : Fin r, (q^(n-i.val)-1)/(q^(r-i.val)-1)`,
which agrees term by term with the convention `j=0,...,r-1` in the paper's `eq:Gaussian-binomial-definition`. The right-hand side is not defined to be a cardinality. The prime specialization uses only `[Fact p.Prime]` and `ZMod.card`.

**Boundary cases.**

- `r=0`: both independent families are the unique empty family, `GL 0 F` is a singleton, and all products are empty products equal to one, corresponding to the unique zero subspace. No factorwise division is performed.
- `n=0`: feasibility forces `r=0`, reducing to the preceding case.
- `r=n`: every actual factor has equal, nonzero numerator and denominator, so the formula equals one, corresponding to the unique whole space. This boundary is not excluded.
- `p=2` is covered together with all other primes; there is no division-by-two step in the field.
- `r>n` lies outside the theorem's stated domain, consistently with the paper's `0≤r≤n`.

**Coverage.** The literal formula in this file directly counts r-dimensional subspaces. In subsequent shell sums, the common intersection often has dimension `n-r`. Rewriting its product in the paper's codimension-r notation still requires an explicit Gaussian symmetry identity or a subspace-duality equivalence. This is not an error in the new theorem, but the unstated symmetry interface cannot be counted as completed by this file. This increment also does not prove positivity of the paper's infinite product `κ_q` or its associated bounds.

Immutable dependencies traced:

| Object | SHA-256 |
| --- | --- |
| `Foundations/RankCounting.lean` at commit 083c3e6 | `340b2579a41a1b14d5c4ea0e77d0c18db5089167ec579bff167dabf16749df54` |
| `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean` in pinned mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` | `d1654075b40e7e9526f02c0b27a3211adf2d615b1719d6eb7259fc8140ac668f` |
| `paper/main-stabilizer2.tex` at commit 083c3e6 | `c172bf686f08d7c0b643fa45b29323ba07416c494db6531edd5990fced34bd61` |

A lexical scan of the new source found no `sorry`, `axiom`, or `admit`. That scan cannot replace kernel checks of actual proof dependencies and the recursive axiom audit during integration.
