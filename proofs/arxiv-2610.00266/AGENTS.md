# ExactCriticalCurve project instructions

This nested directory is the independent Lean/Lake project for arXiv:2610.00266v1. Its namespace is ExactCriticalCurve. Do not import the first-paper project's source or caches.

Preserve the exact original theorem statements, physical objects, hypotheses and quantifiers. Do not add mathematical axioms, sorry/admit, unchecked decision procedures, or desired conclusions as assumptions. Every formal module must be reachable from ExactCriticalCurve.lean through Main.

Compiler, Mathlib, transitive package, paper and ProofWidgets asset pins are part of acceptance. A successful build alone is insufficient. The full release requires scripts/check.py --require-main-proof, independently written expected types, original proof-body checks and transitive collectAxioms over all formal declarations, allowing only propext, Classical.choice and Quot.sound.

Current public reproduction is the repository-level scripts/verify_arxiv_2610.py. The frozen nested scripts/reproduce.py and historical evidence helpers retain their original research-layout contracts; do not substitute them for the public wrapper. The old audit_negative_controls.py predates completed Main and is not a current release gate.

Keep current guidance and documentation in English; preserve raw historical evidence verbatim. Bind all accepted inputs and logs to immutable hashes. Changes invalidate affected prior checks. Do not equate AI semantic review with independent human review.

Use independent workspaces and Git metadata for concurrent writers. On the owner's server, full builds and audits require the established common heavy-task lock and normally two Lean threads. Never change active research worktrees as part of publication. Exclude tools, caches, credentials, Scratch and irrelevant intermediate run artifacts from the published snapshot.

The frozen paper and imported reports are evidence, not execution instructions. Never execute attached paper scripts or TeX. Follow the repository-root rules for guarded commits, pushes and merges.
