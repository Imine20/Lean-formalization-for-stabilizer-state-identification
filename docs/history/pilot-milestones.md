> Historical record: this document preserves conclusions and backup links from the pilot stage before migration (baseline `d8d2b7f`).
> For the current project, main statement, and proof status, consult the [theorem map](../theorem-map.md).

# Stabilizer learning — Lean pilot

Subject: the user-provided `arXiv-2609.13923v1.tar.gz`; the source's main theorem is
`thm:fixed-W-no-discount` (`paper/main-stabilizer2.tex:1397`).
This project has closed the three initial pilots, the prescribed-rank counting chain, the radical-rank identity,
parametrizing bijection, and exact count for the actual ambient matrix-completion set, together with the upper bounds from ordinary and binary enhanced moments
to that completion set, the actual row-space Gram-rank identity, prescribed-radical subspace counts,
and uniform row-space event-probability bounds. **The entire paper is not yet formalized.**
The main theorem has no Lean declaration yet; its axiom audit and final acceptance remain incomplete.

## Closed local proofs

| Category | Source / main declaration | Exact scope |
|---|---|---|
| Complex-matrix optimization | `pilot/StabilizerPilot/MatrixOptimization.lean` / `blockwise_seed_optimum` | Arbitrary finite complex Hermitian PSD matrices with diagonal d≥0 and nonnegative real weights; proves the maximum d(Σc)² and a feasible maximizer. Entry bounds follow from PSD. |
| Finite-field counting | `pilot/StabilizerPilot/FiniteCounting.lean` / `card_symmetricMatrices_prime` | An explicit upper-triangular bijection proves that the number of symmetric n×n matrices is p^(n(n+1)/2), including p=2 and n=0. This is an underlying dependency of the new prescribed-rank counting proof; the Lagrangian shell is not yet closed. |
| Asymptotic inequalities | `pilot/StabilizerPilot/Asymptotic.lean` / `dampedTail_le`, `direct_tail_of_copy_overhead` | A geometric upper bound on a finite damped tail sum; integer divergence k_n−n→∞ gives a zero limit with any fixed coefficient. This is not the complete PGM/counting-to-success-probability bridge. |

Each stage's acceptance data and verified backups are retained at the end of this document; an earlier stage's theorem count is not presented as the current total.
The axiom audit covers every theorem in the project's public and private namespaces,
allowing only `propext`, `Classical.choice`, and `Quot.sound`. Theorem-declaration counts include generated auxiliary declarations
and do not represent equally many independent mathematical results. This stage's final counts, cloud rebuild times, and backup links will be appended after acceptance.
A grep finding no sorry is not a replacement for kernel proof checking; native_decide and custom mathematical axioms are not used.

## Locked environment

- Lean **4.24.0**, compiler commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- mathlib commit **`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**.
- `pilot/lake-manifest.json` pins the full SHA of mathlib and its eight transitive dependencies.
- `toolchain-lock.json` records the SHA-256 of the compiler archives for macOS ARM64 and Linux x86_64,
  together with the input paper archive's hash; both platforms use the same Lean commit and dependency SHAs.
- The local environment is macOS ARM64; this stage adds Linux x86_64 in the cloud, with 8 vCPUs and 30 GiB memory.
  The final clean cloud rebuild and audit results are governed by this stage's acceptance records.
- Cloud dependencies are fetched through a temporary SSH loopback proxy, without changing global network configuration.

Rebuild and audit an existing directory:

```sh
./scripts/lake.sh build
./scripts/lake.sh env lean Audit.lean
```

On a new machine (macOS ARM64 or Linux x86_64, requiring Python 3.10+, git, curl, and tar with zstd support;
bootstrap is compatible with Python 3.10):

```sh
python3 scripts/bootstrap.py
python3 scripts/reproduce.py --dest /tmp/stabilizer-fresh
```

The destination directory must not exist. The reproduction script starts in a new directory, fetches and verifies each locked SHA,
checks the peeled commits of release tags such as ProofWidgets, uses an independent mathlib cache,
builds from zero project `.olean` files, and then recursively audits axioms; after building it checks that the manifest is unchanged.
Dependencies use the official precompiled mathlib cache. This process reuses the host OS and version-verified compiler;
it is not verification on a fresh OS or a source bootstrap of the entire Lean/mathlib stack.
The scope of output `result=pass` is explicitly `pilot_only`, with `main_theorem_complete=false`.

## Final acceptance gate for the main theorem

1. The formal statement must match the original main theorem: all primes including characteristic two, arbitrary isotropic W_n, the original
   cocycle-compatible reports, multiple correct outputs for exceptional inputs, all stabilizer inputs,
   the learner reporting before the test outcome, and unchanged worst-case / uniform-average / verification
   quantifiers and objectives, retaining both β>0, α<1 and diverging-overhead directions.
2. Define the actual quantum/POVM optima and recursively trace all Lean dependencies from the final main declaration.
   Do not add key counting/completion/probability/Clifford/representation bounds as assumptions.
3. Independent semantic review of the main declaration, a clean-directory build of locked sources, and recursive axiom audit must all pass.
   Without a main declaration the result must be marked incomplete; this pilot audit cannot substitute for it.

## Closed stage: prescribed-rank counting

- `UniformGL.lean`: proves from mathlib's actual GL cardinality formula and finite products
  that `|GL(T,q)| ≥ q^(T²)/4`, without assuming positivity of an infinite product.
- `RankCounting.lean`: injectively encodes `(subspace, independent frame)` into all ambient tuples.
- `RankGeometry.lean`: compression and injective reconstruction of symmetric matrices with a fixed image, covering characteristic two.
- `UniformRank.lean`: the actual symmetric prescribed-rank set satisfies
  `N_sym(D,T;q) ≤ 4 q^[T(D−T)+T(T+1)/2]`.
- `RectangularRank.lean`: the actual rectangular prescribed-rank set satisfies
  `N_rect(M,S,L;q) ≤ 4 q^[L(M+S−L)]`. The source's fixed κ_GL⁻¹ coefficient is not claimed as proved.
- `RankConsequences.lean`: the source's exponent identities and exact division by two, existence of a uniform positive constant,
  odd-prime/binary versions, partial rank sums, and cardinality bounds for actual rank≤R sets; both prescribed-rank bounds are directly applied
  to the finite completion-count expression over the full valid rank budget, yielding `16(m+1)²q^(sup E)`.

This fully closes the source's `lem:symmetric-rank-bound`,
`lem:integrated-binary-symmetric-rank-bound`, and `cor:symmetric-rank-partial-sum`.
All targets retain actual `Matrix.rank`, symmetry, and the original dimension domain, without counting-bound assumptions.

The prescribed-rank stage closed only the finite counting expression. The radical-rank identity, parametrizing bijection,
and exact completion count still unproved then were supplied by later proofs for the actual set. This stage additionally closes
the actual row-space parameter correspondence `rank B = a−u`; the source's specified κ expression and subsequent normalized-exponent interfaces remain open.

`planning/paper-dependency-graph.json` is the continually used graph of paper obligations;
stage reports also contain actual dependency graphs extracted from Lean-checked declarations. The audit checks key proof terms'
transitive dependencies to ensure that actual-set counts and downstream upper bounds use the proved normal forms, bijections, rank identities, and prescribed-rank bounds,
rather than merely importing their files or declaring assumptions with the same names.

## Closed stage: the actual matrix-completion set

`CompletionPairs B m k` in `CompletionTypes.lean` is defined directly from actual matrix pairs `(Q,C)`:
`Q` is symmetric and `rank [[Q,C],[Cᵀ,B]] ≤ k`. It is not defined by the rank formula or counting expression to be proved.

- `CompletionNormalForms.lean` constructs normal coordinates from complements of actual kernels and images, proving existence of rectangular and symmetric
  normal forms, two-sided inverse equations for every coordinate matrix, and invertibility of the nondegenerate symmetric block.
- `RadicalRank.lean` gives an explicit linear equivalence for the full radical-block kernel, yielding
  `rank [[A,C₀],[C₀ᵀ,0]] = 2 rank C₀ + rank A₂₂`.
  The proof does not divide by two and covers characteristic two and zero dimensions.
- `CompletionEquiv.lean` and `CompletionBijection.lean` construct the Schur shift, coordinate changes,
  the symmetric matrix's three-block coordinate bijection, and their inverses. For each actual `C₀`, normal coordinates whose existence is proved are chosen only once;
  those coordinates are not counting parameters. `completionAllEquiv_rank` proves that the actual completed matrix has rank
  `rank B + 2 rank C₀ + rank A₂₂`; `completionPairsEquiv` uses this to restrict to the exact rank budget.
- `CompletionParameters.lean`, `CompletionStrata.lean`, and `CompletionFormula.lean`
  count actual five-component parameters stratified by their actual ranks, proving the source's nested summation ranges, floor division by two, and free-block exponent.
  The count is separately proved zero when `k < rank B`.
- `card_completionPairs_eq_source` in `CompletionCounting.lean` gives the source's exact counting formula
  for the actual set; `card_completionPairs_rank_only` proves that the count depends only on `rank B`.
  Through that equality, `completionPairs_count_bound` invokes the two proved prescribed-rank bounds to give the actual-set upper bound
  `16(m+1)²q^(sup E)`. Prime-field and binary-field specializations are both proved.

These main entry points require only an actual symmetric matrix, a finite field, and a rank budget in the source's domain; they do not assume normal-form existence,
a bijection, rank identity, or counting formula. The local exact-counting chain is connected; the main theorem is still unstated.
Two parametrization nodes in the paper graph are marked `Lean_verified_counting_route`: the actual bijection and rank stratification
are closed, but the literal interface for a single fixed-rank fiber under arbitrary externally specified P/R/S has not been separately stated;
this does not affect the fully proved exact count of the actual set. The other six new nodes are closed with their original conclusions.

The exactly counted objects are actual matrix pairs in the source's enlarged/ambient set `R_ζ`,
**not** the moment-derived realizable set `V_ζ`. This stage separately proves an injection of the ordinary realizable moment fiber
into that set, and a cardinality upper bound with factor `2^m` for the binary enhanced fiber through a forgetful map,
without identifying the realizable and ambient cardinalities. The current explicit constant 16 does not mean
that the source's specified `κ_GL⁻¹ K_sym` expression has been formalized; that named constant, the original `E_fin`
normalization, and the truncated structural-branch interfaces remain proof obligations.

## Closed in this stage: moments, Gram matrices, and actual row-space probabilities

- `RowSpaceDefs.lean` and `RowSpaceGeometry.lean` define the row space `W` of an actual matrix `Z`,
  its standard-dot-product orthogonal complement, and radical `W ∩ W⊥` (defined in Lean as `W ⊓ W⊥`), proving
  `rank (Z Zᵀ) = dim W − dim (W ∩ W⊥)`. A corresponding interface handles augmentation by one deterministic-vector row.
  The proof works over any field, including characteristic two and zero dimensions.
- `IntervalSubspaces.lean` constructs an injection for actual interval subspaces using a quotient space;
  `PrescribedRadical.lean` uses stepwise counts of isotropic independent frames, the GL lower bound, and interval-subspace bounds
  to prove that the number of actual subspaces with `dim W=a` and `dim (W∩W⊥)=u` is at most
  `(16q)^k q^[a(k−a)−u(u+1)/2]`. No key counting bound is assumed; impossible parameters give an empty set,
  `k=0` is handled separately, and negative exponents use integer powers.
- `RowSpaceProbabilityBase.lean` and `RowSpaceProbability.lean` define probabilities using the actual
  uniform PMF on all `r×k` matrices; an actual classification injection and the proved subspace count give
  `Pr[dim W=a, dim rad W=u] ≤ (16q)^k q^[−(k−a)(r−a)−u(u+1)/2]`.
  Ordinary row spaces, events containing a specified vector, and row spaces augmented by a specified vector share `K=16q`;
  the augmented case still samples only the original `r` rows.
- `MomentCompletion.lean` and `MomentRowSpace.lean` fix the entire lower moment `ζ`;
  the fiber contains all moment values realizable by any full tuple whose lower moment is `ζ`,
  counting distinct moment values rather than fixing one lower matrix and thereby shrinking the fiber.
  A bijection between the realizable fiber and visible-coordinate set, an injection into the actual completion set,
  augmented Gram rank at most `k`, and `rank B_ζ=a−u` are proved, then used to invoke exact completion counting and the constant-16 upper bound.
- `BinaryMomentCompletion.lean` and `BinaryMomentRowSpace.lean` use actual enhanced-moment coordinates with mod-4 diagonals
  and mod-2 off-diagonals, prove coordinate equivalence and at most `2^m` elements in each forgetful fiber,
  and obtain an upper bound of `2^m` times the actual completion-set count. This uses the unaugmented Gram matrix and its `a−u`
  rank formula, retaining the extra `2^m` factor rather than replacing enhanced moments with ordinary binary moments.

`MomentProbabilityBridge.lean` passed local and cloud compilation, recursive axiom audit, and independent semantic review:
actual uniform finite averages over all lower matrices are stratified by actual `(a,u)` values and connected to
a double finite sum of row-space probability bounds times exact completion counts, then to the proved completion upper bound;
the binary enhanced branch retains `2^m`. The double sum covers the full `0..k` parameter square, allowing
extra nonnegative infeasible terms after relaxation. This is an unnormalized, untruncated finite-set counting average; the original weighted quantum-PGM
interface is not yet closed.

## Schedule update

Removed from the remaining work: GL/Grassmann upper bounds, a shared odd/even symmetric prescribed-rank bound, partial rank sums,
the constant-4 rectangular bound, the finite-expression maximum-term estimate, normal-form existence, the radical-rank identity,
the actual completion-set parametrizing bijection, exact counting, and its explicit constant-16 upper bound.
Additionally removed in this stage: the actual Gram `a−u` identity, prescribed-radical subspace counting, actual uniform
row-space probability bounds, containment of ordinary moments in the completion set, the binary enhanced-moment
coordinates and `2^m` forgetful-fiber bound, and the actual finite-average chain invoking these results.
These stages are closed and are no longer listed as development work for the next round.

This stage's finite-average bridge, independent review, and cross-platform rebuild acceptance are complete. The next acceptance milestone is a finite probability–completion reduction retaining
the original normalization denominator, `min(1,…)` truncation, and feasible region.
Subsequent remaining work includes actual quantum/POVM and PGM weighted interfaces, phase/Clifford/Witt constructions and original-task semantics,
the normalized finite structural branch with truncation retained, asymptotic optimization and reductions, and the original main theorem's formal statement,
dependency closure, and final acceptance. The source's specified κ expression and `E_fin` interface, and the literal coordinate interface for a single fixed fiber
under arbitrary externally specified P/R/S, remain separately listed; the proved route using chosen normal coordinates does not erase those obligations.

There are still too few calibrated examples to estimate the total remaining calendar time, so no number of days is promised. Theorem-declaration counts, paper-node counts,
source-line counts, and compilation seconds cannot be treated as equivalent units of proof effort, much less directly converted to GPU hours.
Subsequent estimates will be calibrated using this stage's actual closed scope and records of development, rework, and acceptance for the remaining interfaces.

Original paper sources, Lean sources, lock files, the current working dependency graph, scripts, and runtime dependencies are retained locally.
Completed reports and build evidence are backed up according to the user's preferences.

## Initial pilot verification and verified backups

After complete SHA-256 readback verification of the 20 completed reports/evidence files above, the backup service removed their local copies.
Lean sources, the original paper, locks, scripts, and runtime dependencies are retained. No credentials were copied into this project.

To regenerate the reports, first restore their evidence inputs from the manifest; mathematical builds do not depend on these archived reports.

## Prescribed-rank chain verification (2026-10-11)

- Reproduction in a fresh directory passed: 134.956 seconds; build 35.253 seconds, axiom/dependency audit 24.594 seconds.
- Recursive audit passed for 92 theorem declarations; the actual project dependency graph contains 111 declarations and 178 direct edges, with 6 additional key transitive dependencies checked.
- Per-file source SHAs match the independent semantic review and clean directory exactly.
- The build scope is the current local proof project; `main_theorem_complete=false`.

The 14 reports and evidence files above passed complete SHA-256 readback verification, after which the backup service removed their local copies; sources, locks, the current working dependency graph, and runtime dependencies are retained. See `backup-receipt-rank.json` for the backup receipt.

## Actual completion-set verification (2026-10-11)

- Reproduction in a fresh directory passed: 174.502 seconds; project build 42.374 seconds, axiom/dependency audit 35.238 seconds.
- Started with zero project `.olean` files; refetched dependencies at locked SHAs and used an independent official mathlib cache.
- Recursive audit passed for 252 theorem declarations; the actual project dependency graph contains 331 declarations and 825 direct edges, with 15 additional key transitive dependencies checked.
- All project source SHAs match the independent semantic review and clean directory; mathematical sources were unchanged after acceptance.
- A total of 452 nodes across both graphs passed navigation, search, and edge-endpoint integrity checks; these were JavaScript/mock-DOM checks, not browser visual acceptance.
- This stage confirms exact counting of the actual ambient completion set; for the original main theorem, `main_theorem_complete=false`.

The 16 reports and evidence files above passed complete SHA-256 readback verification, after which the backup service removed local report copies; sources, locks, the current working dependency graph, and runtime dependencies are retained. See `backup-receipt-completion.json` for the backup receipt.

## Moment and row-space verification (2026-10-11)

- The local whole-package incremental build took 14.309 seconds and the recursive axiom audit 75.704 seconds; both passed.
- Cloud `lean-server` (Linux x86_64, 8 vCPUs, approximately 30 GiB RAM) was actually used for verification;
  a new independent directory began with zero project `.olean` files and fetched all dependencies at locked SHAs plus the official mathlib cache.
- The cloud total was 247.497 seconds: cache 59.755 seconds, build 60.590 seconds, axiom/dependency audit 116.804 seconds,
  with the remainder spent on independent dependency checkouts and related setup. The host OS and verified compiler were reused; this was not a full-stack source bootstrap.
- Recursive audit passed for 423 theorem declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
  The 549 project declarations, 1610 direct dependencies, and 41 key transitive dependencies match exactly across both platforms.
- Source SHAs of this stage's 12 new mathematical modules match the independent semantic review and cloud rebuild.
- Six original statements in the paper graph are closed; both branches' actual finite averages connect to existing exact completion counts and prescribed-rank bounds.
  The original weighted success-probability interface remains partial, and the original main theorem has no Lean declaration.
- A total of 670 nodes across both graphs passed data-integrity, JS-syntax, and mock-DOM navigation/search checks; browser visual acceptance is not claimed.

The cloud retains working copy `/home/ubuntu/lean-formalization`, the pinned Linux toolchain, and
final rebuild directory `/home/ubuntu/lean-rowspace-final-20261011-0334`. Local work will continue to handle
editing and incremental checks, while the cloud handles full rebuilds, audits, and independent compilation; no additional rented server is needed.
Dependency downloads in this stage used temporary SSH proxy forwarding bound only to a remote loopback port, without modifying global proxy settings.
The local and cloud build scopes differ, so these times cannot directly be interpreted as a speedup ratio or proof-development schedule.

The 19 reports and evidence files above passed complete SHA-256 readback verification, after which the backup service removed their completed local copies;
Lean sources, the original paper, locks, the continually used working dependency graph, scripts, and runtime dependencies are retained.
See `backup-receipt-rowspace.json` for the backup receipt. The temporary SSH proxy tunnel has been closed.

