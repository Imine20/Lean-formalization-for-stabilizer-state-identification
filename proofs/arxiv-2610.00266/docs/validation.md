# Validation contract

Acceptance requires successful checks bound to the exact source, build configuration, lockfiles and checker inputs. Neither a source scan, a proposition definition, an auxiliary compilation nor a green CI badge alone establishes the paper theorem.

The complete command is `python3 scripts/check.py --require-main-proof`, run inside this project after reconstructing its pinned environment. It performs:

1. Source/import-policy and exact dependency checks, including paper and ProofWidgets hashes.
2. Pinned compiler identity and complete root build.
3. ProjectAudit: originating-module enumeration, including private/generated declarations, and transitive collectAxioms. Only propext, Classical.choice and Quot.sound are accepted.
4. PilotExpectedTypes: independently stated literal types, rigid universes and original proof-body checks for the complete prerequisite package.
5. ReleaseAudit: independent main and correspondence-extension statements, formula/physical-object guards, and original proof bodies.
6. Repeated input hashing to reject changes during verification.

Original proof bodies are checked through the synchronous kernel declaration interface. Imported constants are supported by the recorded source build and transitive audit. Full original-body checks are retained; the few explicit structure/constructor type-only checks are recorded as such.

Historical source acceptance checked 6,737 declarations, 2,276 Pilot constant types, 2,272 Pilot original bodies and 35 Release constant/body pairs. These are source-specific coverage inventories, not fixed future counts or proof-completion percentages.

Use the [public reproduction wrapper](reproduction.md) to reconstruct the nested project. It must retain exact commands, exits, full logs and source hashes. Both the server acceptance and GitHub run must match the proposed release contents. Later source/checker changes require fresh affected validation.

The retained historical `audit_negative_controls.py` expects an earlier missing-Main state. It is not the current release command. Historical snapshot/strict-verifier tools likewise retain their original source-layout contracts. Their old results must not be relabeled for a new package.

Successful kernel checks certify the formal statements under the permitted axioms. The [semantic map](theorem-map.md) and recorded AI review address correspondence; independent human mathematical review remains outstanding.
