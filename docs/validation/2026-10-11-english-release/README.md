# English edition: strict Main verification

This independent Linux check ran 'python3 scripts/check.py --require-main-proof --output artifacts/english-release' with LEAN_NUM_THREADS=2 in the standalone release checkout. The root build, complete project axiom audit, and exact-type Main release gate all passed.

The git_commit field in check.json is the source snapshot HEAD at check start. English documentation and three active tooling scripts were uncommitted at that time. The certificate records SHA-256 hashes of every build input and asserts the same hashes at completion. The edition manifest matches those hashes to the delivered files; it does not claim the translated edition had already been committed when this local check began. GitHub CI is configured to run a separate check of the published commit.

The mathematical Lean files are unchanged from the accepted source. The complete axiom-audit log is byte-identical to the accepted original Main audit. Historical failures elsewhere remain historical failures. This check certifies the complete original fixed-W Main theorem and the project declaration audit; it does not prove every auxiliary paper statement or the planned arXiv:2610.00266 formalization.

See [edition provenance](../../english-edition.md) and [the hash manifest](../../english-edition-manifest.json).
