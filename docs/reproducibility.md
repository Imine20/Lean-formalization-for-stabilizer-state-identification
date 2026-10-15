# Reproducing the verified proof

## Locked versions

- Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Every transitive dependency is fixed to a full commit SHA in `lake-manifest.json`.
- Linux x86_64 and macOS ARM64 compiler archive SHA-256 values are in `toolchain-lock.json`.

Git, Python 3.10+, curl, tar, and zstd are needed. The project uses Mathlib's matrix, positivity, trace, and tensor APIs; it does not depend on an additional quantum-information library. Version upgrades require a separate compatibility branch and all checks. Do not track Mathlib HEAD.

## Complete first-paper acceptance (recommended)

Use a fresh clone of the exact revision being assessed. From the repository root, run the same proof checks documented in the root README:

```sh
python3 scripts/bootstrap.py
./scripts/lake.sh exe cache get $(cat scripts/cache-imports.txt)
python3 scripts/check.py --require-main-proof
./scripts/lake.sh env lean docs/validation/2026-10-11-direct-integration/independent-expected/IndependentAcceptance.lean
```

For an existing checkout, run the same complete sequence. Require every command to exit successfully; record the exact revision and any working-tree changes. A clean, fixed checkout is required for release acceptance.

The strict gate writes its build, recursive axiom audit, and Main-check results to `artifacts/check/`. Require `check.json` to report `result = pass`, `main_status = dependencies_closed`, and `main_theorem_complete = true`, with a successful `axioms.log` and `MAIN_RELEASE_OK` in `main-release-gate.log`.

The final command is a separate, mandatory check of the independently expanded original Main statement. It must exit successfully and print `INDEPENDENT_ACCEPTANCE_OK`. Neither `check.py` nor the isolated wrapper below executes this extra check. The manual command prints its result to the terminal; preserve that output separately. GitHub Actions additionally saves `independent-main.log` and `independent-main.json`, and checks that the commit, tree, and input hashes remain unchanged in a clean checkout.

The complete audit can take tens of minutes. A normal build's successful exit alone is insufficient. While the repository is private, obtaining its source requires repository access. Verification then needs only public dependency downloads; no author-specific SSH host, internal checkout path or backup service is required.

## Isolated core reproduction (limited coverage)

The older wrapper remains available for a fresh-directory reproduction of the build, recursive axiom audit, and strict Main gate:

```sh
python3 scripts/bootstrap.py
python3 scripts/reproduce.py --require-main-proof --dest /tmp/stabilizer-main-fresh
```

The destination must not exist. Choose another path for another run. The script fetches exact dependency revisions into a new directory and downloads an independent official Mathlib cache. It begins with zero project oleans. A version-checked compiler installation and the host OS are reused; this is not a bootstrap of the full toolchain from source.

Expected results for this narrower reproduction:

- `reproduction.json`: `result = pass`, `main_status = dependencies_closed`, `main_theorem_complete = true`.
- `logs/axioms.log`: a complete successful audit, with all required proof links.
- `logs/main-release-gate.log`: `MAIN_RELEASE_OK`.

These results do not certify execution of `IndependentAcceptance.lean`. The wrapper neither copies nor runs that file, and its isolated project does not contain `scripts/lake.sh`. Do not treat its pass receipt as the complete acceptance sequence above, or try to append the root-relative independent-check command inside its destination. Use the recommended complete sequence in a fresh repository clone instead. Historical receipts retain their original coverage and are not retroactively expanded by this documentation correction.

## What is checked

`scripts/ReleaseAudit.lean` requires a genuine theorem declaration with the exact reviewed type. It rejects a missing proof or a replacement that assumes the main conclusion. `Audit.lean` recursively inspects all project declarations, including definitions, opaque declarations, and private declarations. Its only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` and extra mathematical axioms are rejected.

`check_layout.py` verifies the explicit two-project layout, each project's import of Main and complete formal-module reachability, separate namespaces, exclusion of Scratch, and matching version locks. The first project's build and axiom audit remain separate from the second project's strict gate. Build-input hashes are recorded before the check and checked again afterward. The initial Git HEAD is reported separately from the checked file hashes.

The [accepted complete Main milestone](validation/2026-10-11-direct-integration/README.md) used mathematical freeze `6d17da2`, a Mac project-clean build, and a Linux reproduction with independent exact dependencies/cache. Full audit logs and strict Main checks agree. An additional independently expanded expected-statement check is retained under that milestone.

## Historical records and English provenance

Earlier milestones correctly recorded a missing Main proof or failed preliminary checks. Those outcomes remain historical evidence; they are not rewritten as later successes. English narrative translations do not change mathematical Lean files or retroactively issue new certificates. See [English-edition provenance](english-edition.md) for the source snapshot and translated-file hashes.

The first-paper theorem map distinguishes the completed original main theorem from separately tracked auxiliary interfaces. Its proof does not certify every specified constant or the second paper. arXiv:2610.00266 has its own [theorem map](../proofs/arxiv-2610.00266/docs/theorem-map.md) and [independent reproduction](../proofs/arxiv-2610.00266/docs/reproduction.md).

## Source preservation

Keep formal source, version locks, the paper version, design decisions, and required audit records in Git. Compiler installations, official caches, and compiled files stay on execution machines and can be rebuilt. Never commit SSH keys, passwords, API credentials, or a live cache directory.

The owner's static snapshot workflow additionally preserves useful uncommitted research and file hashes in a verified backup. Private backup receipts are historical provenance, not prerequisites for public reproduction. Do not place a live `.git` or `.lake` directory under real-time WebDAV synchronization. Translation work preserves these historical records and does not contact the backup service.
