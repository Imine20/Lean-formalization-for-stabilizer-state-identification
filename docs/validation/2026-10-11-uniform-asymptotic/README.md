# Acceptance of the uniform asymptotic reduction

Frozen proof commit: `08c15fea0aca23c8b8b93839551a222dfa83f857`.
The [comparison script](compare.py) passed, checking local/cloud source hashes, complete axiom logs, kernel dependency graphs,
locked dependency commits, and hashes of independently reviewed files; see [comparison.json](comparison.json).

## Scope of the result

[`coordinate_common_converse_source`](../../../StabilizerLearning/Bounds/CoordinateConverse.lean)
starts from the actual coordinate experiment, the source's little-o assumption, and the actual dimension domain to prove a common `J`, an explicit `o(N²)` remainder,
an actual real-logarithmic limsup, and convergence of the success probability to zero. Finite counts, row-space probabilities, the full feasible region, truncation,
variational optimization, and asymptotic estimates are all closed within the internal proof chain, rather than assumed by the key conclusion.

This covers `α=0`, `β=1`, `α+β=1`, degenerate ranks, and all completion-parameter boundary cases.
The closed-square cases `β=0` and `α=1` also have exact scalar optimization and zero-exponent identities, without a false claim of probability convergence to zero.
The state/target/prior bridge from the source's physical P_id to the coordinate experiment is still unproved, so the corresponding paper entry is conservatively marked partially closed.
See the [mathematical explanation](../../uniform-asymptotic-converse.md) and [independent review](semantic-review.json).

## Verification evidence

| Check | Result |
|---|---|
| [Local checks](local/check.json) | Full-project compilation and recursive audit passed |
| [Clean cloud rebuild](cloud/reproduction.json) | Fresh dependency directory; independent fetching of fixed Git commits and official caches; initially 0 project `.olean` files |
| [Axiom audit](local/axioms.log) | 1115 theorems and all 1496 project declarations; only `propext`, `Classical.choice`, and `Quot.sound` |
| [Cloud axiom log](cloud/axioms.log) | Byte-for-byte identical to the complete local log |
| Key proof dependencies | 106 transitive dependencies passed, including links from the final asymptotic leaf to the original finite-coordinate, exact-counting, and prescribed-rank chains |
| [Strict main gate](local/main-release-gate.log) | Correct rejection: the fixed-W main proof does not yet exist |
| Source paper and shared definitions | paper, Main, Quantum, and FixedConstraints remain byte-for-byte unchanged from the finite-stage baseline |

Lean `4.24.0` and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` are fixed.
The cloud uses the new directory `/data/lean/StabilizerLearning-clean-20261011-converse-08c15fea0aca`, reusing the existing host operating system and version-checked pinned Lean compiler;
no complete rebuild of mathlib from source or operating-system reinstallation is claimed.
All project-owned sources were recompiled in the independent environment; both checks began with clean working trees of the frozen sources.

The total cloud verification cost was `694.886s`: independent cache fetching `61.111s`,
project build `111.540s`, and axiom audit `509.409s`; the local incremental build took `73.835s`
and its audit `307.486s`. These values inform resource planning, not mathematical proof-development estimates.
Local compilation fixes in new modules before the freeze do not count as passing acceptance evidence.

## Reproduction and remaining tasks

On the frozen research branch, first run `python3 scripts/check.py --output /new/check-directory`,
then `python3 scripts/reproduce.py --dest /new/nonexistent/directory`.
Copy both the local and Linux results into the same local/cloud layout, then run this directory's `compare.py`.
Strict release still requires `python3 scripts/check.py --require-main-proof`, which should currently reject the project.

The [remaining-work estimates](../../remaining-work.json) were updated only after acceptance on both hosts and successful item-by-item comparison.
The coordinate-asymptotic branch has been removed from the remaining work; physical identification/comparison, direct construction, and the final main proof remain on the critical path.
Completed comparable examples of those branches are lacking, so no unsupported number of days or GPU hours is given.

Physical-projector work has been coordinated with another user-authorized process, with separate branches and directories.
Its unintegrated results do not count toward this stage's closed scope. GitHub remains assigned to other processes;
this task pushes only the research branch on private `origin`.
The cloud's temporary loopback proxy has been closed; source code, configuration, necessary caches, and audit logs are retained.
