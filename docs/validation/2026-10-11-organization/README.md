# Project-organization acceptance, 2026-10-11

**The main theorem is stated but unproved; this stage is not final acceptance of the main theorem.**

- Final cloud evidence: `cloud-final-reproduction.json`, commit `2fff4a1`, a new directory with zero project oleans, independent dependencies, and official platform caches; the axiom audit passed for all project declarations.
- Local integration evidence: `local-integration-check.json`, exact commit `d7b0b5b`; fast-forwarded to main after the build and recursive audit passed. Subsequent changes only added evidence/documentation and an ignore rule for toolchain symlinks.
- The frozen formal Lean sources, version locks, and build/audit scripts have identical hashes on both hosts, as do the actual declaration dependency graphs. See `index.json` for the SHA-256 of every log and the provenance of the evidence.
- Both main-proof release gates correctly rejected `statement_only`. Passing development checks did not upgrade the main theorem's status.
- Initial local logs lacked complete run metadata and were superseded by the final records bound to the commits above. Preliminary runs are separately identified and do not serve as final rebuild evidence.
- The pinned compiler and host OS were reused; no full-system bootstrap from source is claimed. An untracked compiler symlink on the cloud host was not included in the new project; tracked sources were unchanged.
- Caches remain on the execution machines. The final Linux cache was moved to the primary cloud working copy for subsequent incremental builds; duplicate preliminary caches were removed, while sources and acceptance logs were retained.

`statement-review.json`, `organization-review.json`, and `theorem-map-review.json` are independent read-only review records; `migration-review.json` records that existing proofs changed only in namespace and import paths. Concrete physical equivalences and main-proof obligations remain listed in the theorem map.

Schedule estimates are not derived from declaration counts, file counts, or compilation times. The next stage must close the Pauli/projector semantics, the bridge from PGM to the existing moment chain, normalization and truncation, asymptotic optimization, and fixed-W comparison, then update estimates using actual proof-development time.
