# Acceptance of the finite coordinate-probability reduction

Frozen commit: `77a26052318427bdd01798625d1dbecde046159b`.
Both local and cloud checks passed; [comparison.json](comparison.json) confirms matching source hashes,
kernel-extracted dependency graphs, axiom results, and hashes of independently reviewed files.

## Scope closed in this stage

The ordinary branch `odd_coordinate_probability_completion_reduction` and binary branch
`binary_coordinate_probability_completion_reduction` start from the original coordinate phase densities
and prove finite bounds for actual tensor copies, the hidden uniform average after tensoring, and all collective POVMs.
The parameter/character bijections, transport of the complete measurement space, actual moment counts, and counting-to-probability reduction are all proved,
rather than assumed by the final theorem.

The full visible-label denominator, `min(1, …)`, the actual positive-mass row-space support, and the source completion feasible region are retained.
The exact completion counts, prescribed-rank bounds, and row-space probability bounds occur in the actual proof dependencies of the final finite upper bound.
The source's signed finite exponent and a maximizing parameter attained within the domain are proved; the current structural bound uses the proved
constants `Ccomp=16` and `Kclass=16*q`, without representing them as the source's specified infinite-product coefficient.

The ordinary branch requires only primality and `2 ≠ 0`; the binary branch fixes `ZMod 2`; the remaining parameters are dimensions.
The project's `n` is the number of lower rows, while the paper's total dimension is `N=m+n`. No new reduction, counting, or physical-equivalence assumptions are introduced.

## Build and axiom evidence

| Check | Result and scope |
|---|---|
| [Local checks](local/check.json) | Full-project build, recursive axiom audit, and key dependency checks passed on fixed sources |
| [Clean cloud rebuild](cloud/reproduction.json) | New project directory; zero existing project `.olean` files; independent fetching of fixed Git dependencies and official caches |
| [Local axiom log](local/axioms.log) / [cloud axiom log](cloud/axioms.log) | 970 theorems and all 1340 project declarations audited; only `propext`, `Classical.choice`, and `Quot.sound` |
| Key dependencies | All 82 transitive dependency checks on actual proof terms passed; not merely an import check or a handwritten dependency graph |
| [Release gate](local/main-release-gate.log) | Correct rejection: the main theorem is still only stated; no main proof exists to pass the release audit |
| [Independent semantic review](semantic-review.json) | Original phases, priors, quantifiers, denominator, truncation, and feasible region checked; partial-coverage boundaries recorded |

Lean `4.24.0` and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
remain locked. The cloud run reused the locked, version-checked compiler and existing operating system; it does not claim
to have reinstalled the operating system or rebuilt all of mathlib from source. Dependency Git checkouts, cache directories, and project compilation
artifacts are independent of the development directory.

The cloud run took `568.042 s` from dependency fetching through complete checks, including `93.810 s` for the project build
and `402.387 s` for the recursive axiom audit. The local incremental build took `49.465 s`, and its audit `238.317 s`.
These are reproducible-build costs, not mathematical proof-development time or remaining schedule estimates.

An integration check before the freeze was rejected by the input-hash gate because sources changed during the check; it is not final
passing evidence. Both final records above target the same immutable commit and began with clean working trees.

To reproduce, run the following on the research branch with version locks preserved:
`python3 scripts/check.py --output /absolute/path/to/new/check-directory`, followed by
`python3 scripts/reproduce.py --dest /absolute/path/to/nonexistent/rebuild-directory`.
Strict release additionally requires `python3 scripts/check.py --require-main-proof`, which is currently expected to reject the project.

## Boundaries relative to the source and main theorem

The original paper, `Main.lean`, and shared `Quantum` and `FixedConstraints` definitions are unchanged.
The physical comparison between the coordinate experiment and the full stabilizer/frame/fixed-W operational tasks, uniform asymptotic optimization,
achievability, and the main proof remain open. The exact PGM formula, specified κ coefficient, and original standard character-sum formulas not yet separately instantiated
remain separately listed and must not be marked complete merely because this stage's direct POVM upper bound holds.

The [remaining plan](../../remaining-work.json) was updated after acceptance on both hosts; there are not yet enough calibrated timing samples
for these distinct proof branches, so no unsupported calendar deadline is given.
The temporary cloud proxy tunnel has been closed; source code, necessary caches, and acceptance logs are retained.
The user assigned GitHub to another process; this stage synchronizes only the existing private Git branch.
