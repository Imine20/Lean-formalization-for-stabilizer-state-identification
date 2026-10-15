# Verification evidence and provenance

Mathematical/audit source: `a741ad2633d99a28fb4bbbe86e3a9a0ac5b7970b`.
Upstream evidence container: `eb39f8270ea0bb736b388748c456c5b0ab7fee16`.

The [source-to-release map](source-to-release-map.json) records original commit, blob, path, destination and SHA-256 for each imported core/evidence file. All 400 upstream formal/build/checker inputs are preserved byte-for-byte. Current English guides and repository-level publication tooling are separate additions, subject to exact-release validation.

The complete [upstream V3 record](validation/2026-10-12/main-release-correspondence-a741ad2-strict-v3/) contains the actual successful build, axiom scan, literal-type and original-proof-body runs. The [V3 sealing tools](validation/2026-10-12/evidence-tools-v3/) and their pinned hashes are retained. The upstream gate ended at 2026-10-12 15:33:30 UTC; strict evidence sealing exited zero at 15:34:53 UTC.

These records are historical upstream evidence. Their original paths and bytes are preserved, including private machine paths that describe where the original checks ran. Those paths are not public reproduction dependencies. Historical logs are not renamed or relabeled as this release's independent results.

The independent server run uses a separately reconstructed project, freshly extracted hash-checked compiler, independent writable dependency directories and initially empty project caches. Reuse of this publication task's previously independently fetched public dependencies is explicitly distinguished from using research caches.

The publication process also verifies the exact proposed release on GitHub Actions. Inspect each run's commit/tree, source hashes, command exits and full artifacts. Published source acceptance, server independence, GitHub reconstruction and semantic review are distinct evidence. An unchanged theorem count or a matching historical HEAD alone cannot establish any of them.

The publication coordinator's [source-bound independent semantic review](validation/publication-source-a741ad2/independent-semantic-review.json) records the revised statements, formula/endpoint checks and limits. The [prior core review](validation/publication-source-a741ad2/prior-core-semantic-review.json) is preserved verbatim and reused only for unchanged original theorem statements/proofs; it is not a mechanical pass for the revised source.

## Independent frozen-source acceptance

The [independent server record](validation/2026-10-12/independent-source-a741ad2/README.md) completed successfully at 2026-10-12 18:17:29 UTC. Its [binding receipt](validation/2026-10-12/independent-source-a741ad2/independent-source-binding.json) validates all 400 immutable inputs, all five command logs, source-derived type/body coverage and the six required release bodies. Full logs and public-dependency acquisition provenance are included separately from upstream evidence. This result does not replace the required exact packaged-tree and GitHub checks.
