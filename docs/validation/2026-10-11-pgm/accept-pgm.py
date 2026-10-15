from pathlib import Path
import json
r=Path('/data/lean/tasks/pgm-integration')
d=r/'docs/validation/2026-10-11-pgm'
c=json.loads((d/'comparison.json').read_text())
assert c['result']=='pass'
scope={
 'frozen_commit':c['frozen_commit'],'validation':'docs/validation/2026-10-11-pgm/comparison.json',
 'actual_normalized_POVM':True,'singular_support_handled':True,
 'original_state_vector_tensor_bridge':True,'actual_Gram_Born_identity':True,
 'statewise_overlap_energy_bound':True,'critical_matrix_or_probability_bounds_are_premises':False,
 'original_definitions_changed':False,'project_root_imports_PGM':True,
 'original_full_Main_proved_in_this_frozen_package':False,
 'paper_transitive_PGM_optimality_complete':False,
 'paper_transitive_average_error_fixed_center_wrapper_complete':False,
 'status':'dependencies_closed_after_clean_build_and_full_axiom_audit'}
(d/'closure.json').write_text(json.dumps(scope,ensure_ascii=False,indent=2)+'\n')
plan={
 'accepted_scope':'Actual normalized PGM construction, singular support, original-state tensor bridge, Gram identity and statewise direct error comparison',
 'this_package_remaining_mathematical_work':[],
 'removed_from_critical_path':['existence of the actual normalized PGM','singular support and support-complement completion','original density to unit-vector bridge','Gram/Born identity','unconditional statewise row-energy lower bound'],
 'external_integration_dependencies':['actual overlap energy uniformly bounded over the original ensemble','all-input fixed-W legal report postprocessing','original real k-n overhead to four uniform one-limits','exact copy-rate infima and original complete Main'],
 'remaining_duration_estimate':{'calendar_days':None,'reason':'PGM package is closed; the peer coordinates distinct geometric counting and final integration. Their current proof/acceptance state must be checked at their own frozen revision; no estimate is inferred from theorem counts or CPU time.'},
 'paper_statements_not_claimed':['transitive pure PGM minimum-error optimality','constant success probabilities','transitive fixed-center energy bound for average PGM success','mixed-state PGM optimality and exact finite formula'],
 'coordination':'Peer main task owns overlap counting, fixed-W postprocessing, final direct/rate/Main and global theorem-map. This branch supplies an independently audited closed PGM package.'}
(d/'remaining-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
text=f"""# Acceptance of the actual PGM and per-state direct bound

Mathematical freeze: `{c['frozen_commit']}`; original baseline: `{c['base_commit']}`.
**All dependencies of this PGM package are closed and accepted; this frozen snapshot excludes the final Main being integrated by another process.**

The actual measurement is defined as `Quantum.stabilizerPGM p n k`; the per-state theorem is
`Quantum.stabilizerPGM_success_ge_overlap`:
the original full-state measurement's probability of a correct outcome is at least 1 minus the sum of the k-copy Born overlaps with the other original input states.
The proof covers all primes, including characteristic 2, dimension zero, and zero copies; it assumes no key matrix or probability bound, invertibility, or energy below 1.

The six modules successively establish unit-vector representations of the original Hermitian rank-one trace-one states, singular spectral inverse square roots, support projections,
completion to a full POVM, actual Gram/Born identities, a PSD polynomial lower bound, and the per-input direct interface for the original stabilizer states.
`Main → Verified → StabilizerPGM` makes every new module reachable from the formal root; Scratch is outside the formal dependency chain.

## Acceptance evidence

- After deleting the project's compiled artifacts from the execution copy, the full root build and axiom audit passed.
- A second directory uses newly fetched exact Git dependencies and an independent official cache, with no dependency symlinks/alternates and initially zero project oleans; the root build and audit passed.
- The two complete axiom logs are byte-for-byte identical: `{c['audit_sha256']}`.
- All {c['all_project_theorems']} theorems and {c['all_project_declarations']} project declarations, including private declarations, were recursively audited; {c['actual_proof_links']} specified actual dependency edges passed, including {c['new_actual_proof_links']} new edges.
- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; no sorryAx or new unproved mathematical axiom occurs.
- All {c['formal_input_files']} formal inputs remained identical across the frozen version, both builds, and final evidence collection. All preceding mathematical files remained byte-for-byte unchanged; only Verified gained an import. The original states, POVMs, Born definitions, tensor products, and Main target were unchanged.
- The measured compiler-archive SHA matches the version lock; the fixed Lean/mathlib/other dependency versions were not upgraded.
- This frozen snapshot's strict Main gate still correctly rejects it because the package does not contain the complete main proof.

The isolation scope consists of two project builds on the same Linux execution host. The execution copy reads the existing locked dependency cache;
the second copy has genuinely independent dependencies and caches. The compiler is reused and its archive verified. No new operating system or independent Mac/Linux acceptance of this package is claimed.

## Correspondence to the paper and main task

The support-vector construction, normalization, and Gram identity of the source's `thm:transitive-pure-pgm` are covered;
optimality, transitivity, and equality of per-state probabilities are not proved in this package.
The new alternative route for `lem:transitive-pgm-overlap-energy` is a per-state bound for arbitrary pure-state families:
it suffices, together with an actual energy upper bound uniform over all centers, to establish the Main direct result.
The original lemma compares average success with the energy at any fixed center and still needs a transitivity/equal-energy wrapper; the entire original lemma must therefore not be marked closed.

Sharp overlap counting, fixed-W postprocessing for all inputs, and the four limits equal to one under the original real overhead are handled by another process,
and are not extra assumptions of this package's theorems. The final complete Main status must be read from the independent acceptance records for the unified integration.

Schedule update: this PGM package has no remaining mathematical tasks; the coordinating main task maintains the remaining status of geometric counting, postprocessing, and final direct/rate integration.
This record does not estimate remaining days from declaration counts, code volume, or audit times.

Detailed records: [dual comparison](comparison.json), [closed scope](closure.json), [original-source preservation](source-preservation.json),
[dependency checkouts](dependency-checkouts.json), [compiler verification](compiler-pin.json), and [remaining plan](remaining-plan.json).
See `../../pgm-semantic-review.md` for the independent semantic review.
"""
(d/'README.md').write_text(text)
print('PGM_ACCEPTANCE_DOCS_WRITTEN')
