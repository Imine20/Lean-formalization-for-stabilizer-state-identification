# Immutable overlap package review

Reviewed on 2026-10-11 (Asia/Shanghai), by the independent pure-state/Gram bridge worker.

The reviewed mathematical input is commit `5d83c537fced9f4bc1dd9f970ee710ec0048077e` from private branch `codex/direct-overlap-counting`. This review used `git show <commit>:<path>`, not mutable files in the implementation worker's directory. The reviewer wrote only this document in its own `/data/lean/tasks/pgm-states` checkout.

**Disposition: no blocking mathematical or original-definition mismatch found in this scope.** This is a source and dependency semantics review; it does not claim an independent build, a completed whole-project axiom audit, or completion of Main.

## Scope and exclusions

The package adds exactly four formal files relative to accepted base `87597a5`: `LagrangianShellGeometry`, `OverlapEnergy`, `OverlapShellCounting`, and `OverlapEnergyAsymptotics`. Previously accepted original state, finite phase, Born, tensor, and version definitions are unchanged.

This review covers the proved coarse shell bound and its exact decomposition of overlap energy. It does **not** cover later commit `661bf2d`, symmetric-matrix exact intersection-fiber cardinalities, a sharpened exact shell-cardinality formula, or a later `4 * dampedTail` inequality. Those require review of their own frozen input. The present package does not prove PGM normalization, PGM statewise success, fixed-W postprocessing, or the four direct limits.

## Checks

1. **Actual states and labels.** `stabilizerOverlapEnergy` sums over the original `StabilizerState p n`, excluding equality of original density-matrix subtypes. Its relabeling uses `stabilizerLabelStateEquiv`, whose injectivity follows from actual projector/submodule/assignment uniqueness and whose surjectivity follows from the original state's label witness. There is no multiplicity of global vector phase, no replacement by coordinate states, and no assumed bijection. The sigma sum is over actual Lagrangians and their actual compatible finite assignments.

2. **Original overlap and tensor expression.** `born_labelProjector_eq` specializes the previously proved physical `born_jointProjector_overlap`: the overlap is `p^(-r)` precisely when the actual assignments agree on `M ∩ L`, and is zero otherwise. `born_tensorPower` uses the original entrywise tensor-product multiplication/trace identities and the proved real trace of a product of PSD matrices. Thus the tensor overlap is exactly `(born A B)^k`; no independence or moment/probability hypothesis is introduced. This expression agrees directly with the pure-vector bridge's `tensor_born_eq_normSq`, although the two packages need not import one another.

3. **Exact phase fibers.** `sum_assignment_overlap_pow` invokes the proved `card_compatibleAssignments`, which reduces to the actual restriction-fiber equivalence and character-extension surjectivity. The count is exactly `p^r` for a fixed M at distance r from L. The phases are original finite section-compatible assignments, including characteristic two; no odd-prime convention or compatibility-count premise is used.

4. **Zero copies and 0^0.** `born_tensorPower`, `stabilizerOverlapEnergy`, and `stabilizerOverlapEnergy_add_one` allow k=0. At zero copies every tensor overlap is one, including orthogonal distinct inputs; the energy is therefore the ensemble cardinality minus one. The phase-sum and shell-decomposition theorems explicitly require `0 < k`, so their use of `zero_pow` does not incorrectly discard the zero-copy orthogonal contributions. The eventual theorem derives positive copies from the original asymptotic premise.

5. **Distance zero and removal of the identical state.** The distance definition proves `r=0 ↔ M=L`, using equal dimensions and exact intersection inclusion. Thus the distance-zero Lagrangian shell has cardinality one. At positive k, the phase sum over this shell equals one: its one compatible assignment is the center's assignment and all other phases have zero overlap. The proof first establishes `energy + 1`, then subtracts this actual r=0 contribution; it does not remove every state with the same Lagrangian by definition. The resulting sum is over r+1 for r in range n. For n=0 this is the empty sum, consistently giving zero energy.

6. **Actual geometric injection.** `exists_injective_lagrangianIntersectionFiber_matrix` starts from the full subtype of actual Lagrangians whose intersection with the center is K. Isotropy places each source in K-perp. Inside K-perp/K, its image complements the center/K; quotient dimensions and injective reconstruction are proved. Choosing an arbitrary complement and bases gives an injection into all r-by-r matrices. This supports only the coarse `p^(r*r)` upper bound, exactly as stated. No symmetry, exact cardinality, or hidden coordinate-realizability assumption appears. The shell is then injected into the sigma type of its actual intersections and fibers.

7. **Uniform count and tail.** The previously proved interval-subspace estimate gives at most `4 * p^((n-r)*r)` possible intersections. Multiplying by the actual fiber upper bound proves `shellCount ≤ 4 * p^(n*r)` for r≤n. Together with the exact phase sum this yields the genuine energy bound
   `4 * sum_{s=1}^n (p^(-1))^(s*(k-n-1))`
   under `n+1≤k`. The endpoint k=n+1 is permitted (a finite coarse bound); the infinite geometric comparison is used only when overhead>0.

8. **Original real excess-copy hypothesis and quantifiers.** The only asymptotic premise is
   `Tendsto (fun N => (k N : ℝ) - (N : ℝ)) atTop atTop`.
   `real_copy_overhead_tendsto_nat` proves the natural truncated overhead `k N-N-1` tends to infinity from this premise. The proof does not replace it with a stronger assumed natural/integer condition. The tail comparison is independent of the input state and dimension; `stabilizerOverlapEnergy_eventually_lt` yields `∀ᶠ N, ∀ x : StabilizerState p N, energy ... x < ε`, preserving uniformity over all inputs. Its eventual `N+1≤k N` is derived, not assumed separately. All prime characteristics are covered through `Fact p.Prime`.

## Nonblocking documentation observation

The unchanged module comment in `StabilizerEquivalence.lean` still says assignment existence is open. That statement is stale relative to the imported and accepted `AssignmentExistence/AssignmentExtension` chain. It does not add a formal premise or affect the reviewed proof; a future documentation cleanup can correct it independently.

## Immutable source SHA-256

| File | SHA-256 |
| --- | --- |
| Quantum/OverlapEnergy.lean | `72677fe0e78d3174a062ade7337c06fde767309bf05a3de82843f257a31f2959` |
| Quantum/OverlapShellCounting.lean | `43ce5063bef2c2e670cd95d487d11b0ea4756e6fe59feca70ba4b46dd7e13bdf` |
| Bounds/OverlapEnergyAsymptotics.lean | `368e4fd0c38d205c04ff449211403fedba5c3aa6a6b3e754d07b9804d4a778e1` |
| Quantum/LagrangianShellGeometry.lean | `e2c7d4c7871dd8f5811f9dd9d32c01c694393629520c48b405ee23dca0634612` |
| Quantum/StabilizerEquivalence.lean | `9ee8c6fd0ae24f708ceaca5b17aa3f3dd7e1447af58db463acb50bf8cc839355` |
| Quantum/AssignmentExtension.lean | `b75ab5226db74a085c7058f43e8c4c4a382eb1cd1461a62032930b07b04f73df` |
| Quantum/ProjectorOverlap.lean | `bf34325a36da3eede908a6fc572b52c705c48e66e1fb4b3887a31489c1a432c2` |
| Quantum/TensorProbability.lean | `7f44c721afeb141920ab98e02521249fcd27046e73303e4ee2832c00a4866b3f` |
| Foundations/IntervalSubspaces.lean | `b37ae3ed8dba1c87bd7622837c61766ef69eb2a440c17413aa033c3021f72095` |
| lean-toolchain | `42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434` |
| lake-manifest.json | `0ae1e12b18776157f4c8215f8491d669c74a10913031b15ac4cc6204994d98fc` |

Formal source paths above are relative to `StabilizerLearning/`, except the two root version files.

## Incremental review: exact fibers and damped tail

Reviewed frozen commit `d4a993db1b34a6e70c9d419677bcbabaf261390d` on 2026-10-11 (Asia/Shanghai). Relative to the preceding reviewed `5d83c537`, this adds only `Quantum/LagrangianShellExact.lean` and `Quantum/OverlapShellExactCounting.lean`. Earlier reviewed files and version pins are byte-identical. The previous scope exclusion for the exact-fiber work is superseded **only for the contents present in this new frozen commit**.

**Disposition: no blocking mathematical or original-definition mismatch found.** This remains an independent source/semantic review, not a new compilation or whole-project axiom-audit claim.

### Genuine exact intersection fibers

- `shellReferenceFrame` uses a constructed basis extension adapted to the actual K inside the actual center Lagrangian. The existing symplectic frame standardization preserves pairings. The new proofs identify its images of L0 and K as exactly the vertical and tail subspaces, respectively, and prove an iff for the original intersection predicate. A suitable frame, its invertibility, and the relevant image identities are not input assumptions.
- For the standard fiber, isotropy with the included common tail proves that all first-coordinate tail entries vanish. Reduction to the initial r coordinates preserves the symplectic form on these vectors. Its kernel is proved to be precisely the common tail, so rank-nullity gives dimension r; exact intersection with the vertical subspace gives transversality.
- Inflation takes the image of the actual reduced Lagrangian times the common tail under an injective assembly map. It proves isotropy, dimension r+b, and the required exact intersection. The two reconstruction theorems `shellReduced_inflated` and `shellInflated_reduced` establish inverse operations, including the required adjustment by a tail vector. Thus `standardShellFiberEquivTransverse` covers every actual fiber element in both directions.
- The existing all-characteristic `transverseLagrangianEquivSymmetricMatrices` is an actual graph equivalence, not an enumeration premise. The exact symmetric count comes from independent upper-triangle coordinates, with division only in the natural-number exponent. Hence `card_lagrangianIntersectionFiber_eq` proves `p^(r*(r+1)/2)` for the full actual fiber, including p=2, r=0, and n=0.

### Shell sum, phases, and boundary conditions

- `lagrangianShellEquivIntersectionFibers` is a genuine equivalence between the actual distance-r shell and the sigma type of its actual intersections K and exact fibers. Its inverse recovers the shell distance from dim K=n-r. This strengthens the earlier counting injection and proves
  `shellCount = card(actual (n-r)-subspaces in L) * p^(r*(r+1)/2)`.
- `stabilizerOverlapEnergy_eq_grassmann_sum` starts from the already reviewed original-state shell decomposition. The factor `p^r` of compatible phase assignments remains the exact restriction-fiber count in the previous package; multiplying it by `p^(-rk)` gives `p^(-r*(k-1))`. No phase multiplicity is silently changed in the new formula.
- The exact energy formula still requires `0<k`. It does not extend the positive-copy phase simplification to k=0, where orthogonal overlaps tensor to one. The r=0 contribution remains the unique center state after the phase sum, removed via the proved energy-plus-one identity. Reindexing by r+1 therefore preserves the intended self exclusion.
- The r=0 exact geometric fiber consists of the sole 0-by-0 symmetric matrix. For n=0, the positive-shell energy sum and damped tail are empty; all formulas are consistent. No new nonempty-index or positive-dimension premise appears.

### Interfaces intended for Main

`stabilizerOverlapEnergy_le_dampedTail` has only the prime instance, the original actual state, and the finite copy condition `n+1≤k` as relevant inputs. It proves
`energy ≤ 4 * dampedTail (p:ℝ)⁻¹ n (k-n-1)`
by the exact fiber formula and the previously proved interval-subspace count. In particular, it does not take a shell bound, Gram bound, or probability bound as a hypothesis.

For s=r+1, the proof's arithmetic identity is exactly
`s*(k-1) = (n-s)*s + s*(s+1)/2 + s*(k-n-1) + s*(s-1)/2`.
The divisibility facts for consecutive integer products justify both triangular exponents; this is natural-number arithmetic, not division by two in the coefficient field. After cancellation of positive powers of p, it leaves the exact exponent used by the original `dampedTail`.

The finite theorem permits k=n+1, so its natural overhead can equal zero. The eventual geometric comparison requires positive overhead only where the already proved scalar tail theorem requires it. The new `dampedOverlapBound_tendsto_zero` takes **the original real** premise
`Tendsto (fun N => (k N:ℝ)-(N:ℝ)) atTop atTop`
and explicitly invokes `real_copy_overhead_tendsto_nat`. It does not use the older integer-overhead theorem from `Bounds/Asymptotic.lean`. The numerical bound is independent of the state and W, enabling the same eventual index to work for every input state. This review does not itself claim that the four direct limits or Main have been integrated.

### Still outside this frozen scope

The factor called Grassmann cardinality is the literal cardinality of actual subspaces. Commits `ba3a903` and `b280693`, which evaluate and attach its Gaussian product, are later than this frozen input and are **not reviewed here**. Neither their exact product formula nor its connection to paper-specific constants is accepted by this note. PGM normalization/row-energy success and fixed-W postprocessing also remain separate review scopes.

### Additional source SHA-256 at d4a993db

| File (relative to StabilizerLearning/) | SHA-256 |
| --- | --- |
| Quantum/LagrangianShellExact.lean | `9a32073d1cf9764dad8f7d541320c9e0374835bf45d25e4538ffc9a34c2e4d0f` |
| Quantum/OverlapShellExactCounting.lean | `b1209b09f53f3ec9f78eb588e67542744e118a83cce4ce12b9eeedf687617431` |
| Bounds/Asymptotic.lean | `48cfb87f4e4ef519e85691acb0afa14c4a213f98a2ebe759678482ed915aed7c` |
| Quantum/TransverseGraph.lean | `5bb2a097f9f2b12fac65f5e682bb9a1ced037b05246a329f667be206d3dfc339` |
| FixedConstraints/AdaptedFrame.lean | `b24cedd8b3fb395734fef992f0cc142358d686a32fad53aacff58dffceb76706` |
| Foundations/FiniteCounting.lean | `aa10f5856aff983563ecb365fac1e5e8386a75c914892c507d8b7f76dce742a8` |

## Incremental review: literal Gaussian product wrapper

Reviewed frozen commit `b2806935a71994eb752018e7ef6457f674c647db` on 2026-10-11 (Asia/Shanghai). Relative to `d4a993db`, it adds `Foundations/GrassmannExact.lean` and `Quantum/OverlapShellProduct.lean`. The Grassmann source is byte-identical to the separately supplied dependency commit `083c3e6dd5f0e1463a5c72502626e85aab465e31`; its ancestor in this branch is `ba3a903`. The previous note's exclusion of these product files is superseded for precisely this frozen source.

**Disposition: no blocking mathematical or original-definition mismatch found.** This source review does not claim another independent build, a complete axiom audit, or Main completion.

### Exact actual-cardinality bridge

`subspaceIndependentFamily_bijective` strengthens the accepted frame encoding to a genuine bijection. For an arbitrary independent family, its actual span has the required dimension, and the inverse coordinates are taken in the selected basis of that span. Injectivity uses the proved equality between the span of a full independent family and the original subspace. The exact counting identity therefore counts the genuine Grassmannian times its genuine bases; the number of bases is identified with the actual general linear group. No Gaussian identity is assumed.

`lagrangianSubspacesEquivRankSubspaces` first moves an actual subspace K⊆L into L by `submoduleOf`, with inverse given by the injective subtype map. It then transports that subspace through a basis equivalence of the actual L. Both inverse identities and dimension preservation are proved. This connects the exact shell-cardinality factor from the previous review to the actual standard Grassmannian before evaluating any product.

### Denominators and natural subtraction

The real-valued quotient theorem casts the exact natural frame-count identity only after proving each natural difference has its untruncated value: the index satisfies i<r≤n. Its total denominator is the GL cardinality, which is strictly positive because the finite GL type contains the identity, also at r=0. The proof rewrites the product denominator to that positive cardinality before division. Thus it does not obtain a spurious result from Lean's totalized division by zero.

The descending-exponent product factors each numerator and denominator by q^i and cancels that nonzero factor, where q is the finite field cardinality. For the prime specialization, p>1 and each denominator exponent r-i is positive, so each factor denominator p^(r-i)-1 is nonzero. The source proves the needed overall denominator nonzero through GL positivity; it does not introduce a new separate denominator hypothesis.

### Shell index and endpoints

`lagrangianShellCount_eq_gaussian_product` uses `Fin (n-r)` because the counted intersection has dimension n-r. Its coefficient is the literal product for **[n choose n-r] over the prime field**, multiplied by the already proved exact symmetric-fiber factor p^(r(r+1)/2). This indexing matches the actual intersection subtype; it is not a product for r-dimensional subspaces mislabeled as one for n-r.

- At distance r=0, the coefficient uses Fin n, numerator and denominator coincide and are nonzero, every ratio is one, and the fiber exponent is zero. The actual shell has one member.
- At r=n, the product over Fin 0 is one and the result is p^(n(n+1)/2), agreeing with the transverse exact fiber.
- At n=0, r≤n forces r=0; both the product and fiber count are one. The positive-shell energy sum is empty.
- `stabilizerOverlapEnergy_eq_gaussian_product_sum` keeps the earlier positive-copy hypothesis, actual state/label equivalence, phase factor and self exclusion. It only replaces each existing shell coefficient by the proved product. It does not change the zero-copy convention or add a probability premise.

### Explicitly unproved wrapper and dependency scope

This frozen package does **not** provide a separate Lean wrapper proving Gaussian symmetry `[n choose n-r]_p = [n choose r]_p`. The mathematical equality is not counted as a formalized declaration here. The accepted formula is the literal Fin(n-r) product displayed in the theorem; changing its presentation to the complementary index remains a separate proof obligation if required.

The intended Main path through `stabilizerOverlapEnergy_le_dampedTail` uses the sharp actual-cardinality theorem, the interval-subspace bound, and the exact phase sum. It does not depend on Gaussian symmetry or on this optional product wrapper. This review therefore neither strengthens the Main claim nor conceals a needed symmetry premise.

### Additional source SHA-256 at b2806935

| File (relative to StabilizerLearning/) | SHA-256 |
| --- | --- |
| Quantum/OverlapShellProduct.lean | `ef83f86cb029427923ebf8d13d68c97c076f913eadf45daf12c08e660b5bef66` |
| Foundations/GrassmannExact.lean | `30831796bbf0f262b207dab0b0bd6ecda6de26947c65dc6921f8bb9ad5c6cbf7` |
| Foundations/RankCounting.lean | `340b2579a41a1b14d5c4ea0e77d0c18db5089167ec579bff167dabf16749df54` |
