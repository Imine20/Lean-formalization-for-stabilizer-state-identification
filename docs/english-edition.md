# English edition and verification provenance

This document records the first paper's earlier English-edition release and preserves its original scope. The formerly reserved second-paper entry now has a [separate formalization and verification contract](../proofs/arxiv-2610.00266/README.md); its claims are not inherited from the first paper's acceptance.

This edition labels the existing formalization as **lean proof of https://arxiv.org/abs/2609.13923**. It reserves arXiv:2610.00266 as a separate planned proof and keeps the GitHub repository private, as requested.

## Accepted mathematical source

The complete original Main proof was accepted at mathematical freeze `6d17da20d7a7625333ecf87d23824f031a01a6ae`. Its final evidence container is `6b1e089cf1ec19b81e6683656c4afe41ff116c38`, with source tree `90da27179c34b6bc31d96e6dfceb9ea9483f70c5`.

This repository imports that exact tree in commit `0b4b66a485b4c29b9bcf1328e84f99807648467b`. It is a source snapshot, not a claim that the original intermediate research history is present. The mathematical Lean files, original paper, and dependency/toolchain locks remain byte-identical in the English edition. Both the original Main target and the independent expanded statement are retained.

The accepted original checks used one Mac project-clean build and one independent Linux reconstruction. They covered 181 build inputs and produced byte-identical full audit logs for 2,759 theorems, 3,448 declarations, and 345 required proof links. Both exact-type Main gates succeeded. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

## What the English edition changes

- English project instructions, topic notes, semantic reviews, milestone descriptions, theorem maps, and human-facing historical report text.
- A consistent English status vocabulary in the theorem map, with structural machine fields, theorem identifiers, formulas, and source labels preserved.
- The theorem-map generator's default input now points to the accepted complete-Main audit, so its default output matches the current map.
- A paper index and a clearly unverified placeholder for the future paper.
- Reproduction instructions and a GitHub workflow that always requires the exact Main proof.
- The source snapshot policy includes the paper index; no additional mathematical library or Lean toolchain is introduced.

[The edition manifest](english-edition-manifest.json) records original and English file hashes, mathematical-source equality, and the fresh release checks. This allows a reviewer to distinguish the accepted mathematical content from translated commentary and updated tooling.

## Historical evidence

Raw build/audit/release logs and recorded past outcomes retain their original meaning. Earlier missing-Main results and failed preliminary checks remain failures of those earlier attempts.

A historical certificate hashes the original files at its stated freeze. It does not automatically certify a later translated Markdown file at the same path. When a human-readable review is translated, its before/after hashes are listed in the edition manifest; raw historical certificates are not rewritten to invent a new past result. Historical reconstruction scripts may require the original research revision and environment. Use the current [reproduction procedure](reproducibility.md) to check the delivered proof.

Private static-backup receipts remain archival provenance. They are not dependency sources, build prerequisites, or proof assumptions. Verification does not access the author's private server or backup storage.

## Scope

The entire original fixed-W Main theorem is proved. The [paper map](theorem-map.md) separately records auxiliary statements that are only partially covered or remain open. Neither this English translation nor Main acceptance establishes every distinct paper formula or the later arXiv:2610.00266 critical curve.
