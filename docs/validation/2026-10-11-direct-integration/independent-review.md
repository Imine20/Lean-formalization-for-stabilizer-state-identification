# Main direct proof chain: independent semantic review

Status: the independent semantic review of final mathematical source 6d17da20d7a7625333ecf87d23824f031a01a6ae passed without blockers. Clean rebuilds, the all-declaration axiom audit, and the exact-type Main release gate are separate acceptance evidence and cannot be replaced by this record.

## Actual PGM (a1f4d122949298a9f8dd465dd16f5680287cb275)

The root process and `/root/fixedw_geometry` each performed a read-only review. No semantic blocker was found.

- `PureStateVectors` extracts unit eigenvectors from the original Hermitian, rank=1, trace=1 conditions; their densities are exactly the original entrywise tensors. Choosing global phases does not enlarge the original distinct-density labels.
- `SupportedSynthesis` defines the inverse square root on the finite spectrum to be zero at zero eigenvalues and actually proves `T†S=√G`, `P²=P`, and `PS=S`, allowing singular, duplicate, and linearly dependent signals.
- Positivity of `completedColumnPOVM` and its sum being the identity are proved; `(I−P)S=0` ensures that the complementary-space effect assigned to the default valid outcome contributes zero on every signal.
- Gram polynomial positivity gives the per-state lower bound; the relationship between row energy and the actual Born sum has the correct direction. The final `stabilizerPGM_success_ge_overlap` accepts only p, n, k, a prime instance, and an original state; it assumes no key support, normalization, counting, invertibility, or success bound.
- p=2, n=0, and k=0 are retained. The package does not prove the paper's transitive-PGM optimality or equal-success propositions; a per-state lower bound must not stand in for them.

## Fixed-W for all inputs (f25413b7e90f6ca261b9b8949531f11088af0cc8)

The root process reviewed `/root/fixedw_geometry`'s implementation read-only and found no semantic blocker.

- The dimension identity actually proves `dim(L∩W⊥)=m+dim(L∩W)` without a genericity assumption.
- K is constructed from an actual complement; its dimension, isotropy, orthogonality, and K∩W=0 are proved, and its sum with L∩W is exactly L∩W⊥.
- Restriction of the original assignment gives a valid report for every actual input. The deterministic decoder is a fixed function of the measurement outcome, with no access to the unrevealed true input or verifier outcome.
- `POVM.pushforward` preserves all original valid measurements; the probability term for the correct full state is included in exact success, then lifted using the original verification≥exact inequality. `sup_M inf_x` is not exchanged, and exceptional inputs are not discarded.

## Actual coarse intersection fibers (46453617bb6b6c772ffce2ce847d8339b5ee3822)

The root process and `/root/fixedw_geometry` each performed a read-only review and found no semantic blocker.

The actual domain contains all `{L : Lagrangian | L∩L₀=K}`. After restriction to K⊥ and quotienting by K, the proof internally establishes that the quotient has dimension 2r, L₀/K has dimension r, the images are complementary, and reconstruction through the quotient map is injective. Actual projection onto a fixed complement then gives a matrix injection, yielding `card fiber ≤ p^(r*r)`. This coarse bound covers all primes and r=0, n=0, and suffices to preserve the unit copy-rate threshold; it does not claim exact symmetric-matrix fibers or the Gaussian shell formula.

## Original quantifiers and rate tools

`/root/fixedw_geometry` reviewed the root process's `DirectLimits`, `RateLowerBound`, and `RateWitness` read-only and found no semantic blocker.

- UniformLimit retains `∀ε>0 ∃N ∀n≥N ∀W`; propagation and squeeze results are only auxiliary lemmas, and the key finite success bound must come separately from actual PGM/counting proofs.
- The proved converse implies that every achievable rate is ≥1 using the original liminf; the sInf lemma uses an actual rate=1 witness to establish nonemptiness and does not rely on empty-set conventions.
- Floor dimensions include β=1 and n=0; nonemptiness of the actual valid-W type is established constructively. `n+Nat.sqrt n` has normalized rate 1, while its real difference tends to positive infinity.

## Final exact chain and independent review

Subsequent exact fibers replaced the coarse matrix-injection route in Main: actual intersection shells are bijective with Σ-fibers, which are in turn bijective with all symmetric matrices; the actual phase-restriction fiber count p^r, tensor Born sums, and cancellation of the self term are derived from the original objects. The final error is 4*dampedTail, whose uniform decay follows from the original real k−n→∞. The original full-input decoder gives four UniformLimit1 conclusions; actual floor/sqrt sequences give a rate-one achievability witness, the original converse excludes achievable rates below 1, and Main's proof has exactly the unchanged original target type.

Independently reviewed files and immutable commits:

- [Six PGM modules](../../pgm-semantic-review.md): `1f1502c`.
- [Actual exact shells and Grassmann counts](../../pgm-peer-shell-review.md): `64eabb2`, including the earlier `97fa507/65a6b4d` exact-fiber reviews.
- [Actual phase/tensor energy, sharp tail, and literal product](../../pgm-peer-overlap-review.md): `a9f6b8d`, including the `d4a993d` incremental review.
- [Complete Main and rate quantifiers](../../direct-main-semantic-review.md): `bb7f820`, bound to 6d17da20.
- [Another independent Main/PGM/sharp review](../2026-10-11-direct-final/semantic-review-fixedw.md): `5c76695`; its author's own FullW/Covariance portion is explicitly identified as self-review only.
- [Independent covariance and literal-product review](../2026-10-11-direct/semantic-review-covariance-shell-product.md): `9067b64`.

These reviews found no key containment, normalization, counting, or success claim converted into a final assumption, no restriction of the original input/POVM domains, and no sup-inf exchange. All-prime, zero-dimensional, and relevant zero-copy semantics were checked; the positive-copy energy formula explicitly requires k>0, and the final limit derives that condition from the original overhead.

The literal Gaussian product is indexed by Fin(n−r), the actual intersection-subspace dimension; no separate Gaussian-symmetry wrapper rewrites it as the paper's Fin r. PGM optimality, equal success probabilities, and the κ constant are not assumptions of this Main-closure route and have not been falsely claimed as proved.
