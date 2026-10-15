# Acceptance of the original physical P_id bridge

Frozen source: `ce043d6c1de0cda69dc3ed6163aedf23717833a5`. The complete axiom logs and actual dependency graphs from local macOS ARM64 and cloud Linux x86_64 are byte-for-byte identical. The [comparison script](compare.py) and [results](comparison.json) support rechecking.

## Accepted scope

The distinct physical density matrices in the original standard transversal chart, the complete reference-dual reports and actual targets, the uniform prior, and all collective POVMs are connected to the proved coordinate model through actual bijections and matrix identities. `physical_common_converse_source` establishes a common J, a common remainder, the actual log-limsup, and convergence to zero under the original little-o scaling. All primes, finite zero-dimensional and zero-copy cases, and the original asymptotic boundary cases are retained; no key physical equivalence or probability bound is assumed.

Acceptance records for the two batches of Pauli/projector results from another process are available in the [Pauli stage](../2026-10-11-pauli-projectors/comparison.json) and [general Assignment stage](../2026-10-11-assignment-completeness/comparison.json). This stage rechecked that the eight general modules were byte-for-byte identical to their frozen sources and independently revalidated the complete integrated root import chain.

## Machine evidence

- [Local checks](local/check.json): build 70.864 seconds; full axiom audit 521.586 seconds.
- [Clean cloud rebuild](cloud/reproduction.json): independent exact Git dependencies, official cache, initially zero project oleans; total 1142.603 seconds.
- [Recursive audit](local/axioms.log): 1639 theorems and 2116 project declarations; only `propext`, `Classical.choice`, and `Quot.sound`. No new mathematical axioms or sorryAx.
- All 167 actual transitive dependency checks passed; the physical converse connects to the odd-prime/binary finite-probability, counting, row-space, and common-J chains.
- [Isolation evidence](cloud/isolation.json): all nine dependencies exactly pinned, tracked working trees clean; no dependency/cache symlinks or Git alternates.
- [Semantic review](semantic-review.json) and [preservation of original definition bytes](public-definitions-unchanged.json).
- The [main-theorem gate](local/main-release-gate.log) correctly rejected `statement_only`. This stage does not claim a proof of the main theorem.

Lean 4.24.0 and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` are fixed. Cloud directory: `/data/lean/StabilizerLearning-clean-20261011-physical-ce043d6c1de0`; the host system and verified compiler are reused, with no claim of a full-stack bootstrap. The temporary download channel on port 17892 has been closed.

## Reproduction and remaining scope

In a new environment, run `scripts/bootstrap.py`, then `scripts/check.py`; use `scripts/reproduce.py --dest /new/nonexistent/directory` for independent acceptance. With the original layout preserved, run this directory's `compare.py` to compare current sources against the frozen evidence from both hosts. The strict final acceptance command `scripts/check.py --require-main-proof` must continue to reject the project until the original main theorem is actually proved.

The [stage description](../../physical-coordinate-bridge.md) and [remaining-work estimates](../../remaining-work.json) were updated after both sets of checks and all comparisons passed. Arbitrary frames/Clifford implementations, fixed-W, actual verification, unrestricted direct achievability, and the final main theorem remain on the critical path. Compilation times are used only for resource scheduling, not extrapolated to mathematical development time. GitHub is handled by another process.
