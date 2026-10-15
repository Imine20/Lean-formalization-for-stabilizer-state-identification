#!/usr/bin/env python3
"""Update current scope and scheduling only after the three-way comparison passes."""
from pathlib import Path
import datetime, json, subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
DOC=ROOT/'docs'
result=json.loads((HERE/'comparison.json').read_text())
assert result['result']=='pass'
plan=json.loads((HERE/'acceptance-plan.json').read_text())
plan.update(status='accepted_after_three_complete_checks_and_source_comparison',remaining_gates=[],result_record='comparison.json')
(HERE/'acceptance-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
validation='docs/validation/2026-10-11-graded-integration/comparison.json'
r=json.loads((DOC/'remaining-work.json').read_text())
closed=[
 'actual prescribed-subspace phase-assignment extension and exact restriction fiber count for all primes',
 'realizable phase-compatible original report lists and proved uniform bound 16*p^(2*n*D+D) for D<=m',
 'constructive positive normalized all-POVM bounded-list Bayes decoder preserving the physical input prior',
 'actual compatible-event graded-to-exact inequality and restoration of the original full distinct-state prior',
 'explicit W-independent graded remainder o(N^2), square-root tail and exceptional mass tending to zero',
 'original complete converse clause: exact common-J bounds and all four original UniformLimit zero conclusions'
]
r['updated_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
r['newly_removed_from_remaining_work']+= [x for x in closed if x not in r['newly_removed_from_remaining_work']]
r['next_acceptance_milestone']='Construct a legal unrestricted direct measurement and prove original state-uniform success for every diverging k-n overhead; then close four direct limits and copy-rate/Main.'
r['remaining_major_branches']=[
 'unrestricted legal direct measurement/PGM, actual Gram success identity and overlap shell bound giving state-uniform success under k-n -> infinity',
 'original fixed-W postprocessing and all four UniformLimit one conclusions',
 'remaining covariance interfaces, exact rate liminf/sInf identities and the unchanged complete Main proof with strict release'
]
r['remaining_source_interface_details']=[x.replace('literal partial-label fiber cardinality and prescribed proper-subspace assignment extension fibers','literal partial-label fiber cardinality; prescribed-subspace phase-assignment extension fibers are now closed') for x in r['remaining_source_interface_details']]
extra=[
 'literal Gaussian intersection-shell count, shell sum and specified kappa coefficient; original compatible-list converse is already closed through an alternative proved ambient cover',
 'refined-verification-specific finite rank-list and limit interfaces; original basis-free verification limits are closed',
 'named generic-only uniform-limit wrapper; explicit W-uniform generic bound and its vanishing envelope are already proved'
]
r['remaining_source_interface_details'] += [x for x in extra if x not in r['remaining_source_interface_details']]
r['reason']='The original graded verification and full original converse are accepted. Remove their actual-list, Bayes, tail and uniform-limit obligations from the critical path. The unrestricted direct construction has no accepted comparable full proof sample yet; no reliable calendar duration follows from compilation times or declaration counts.'
r['calendar_deadline']=None
r['main_complete']=False
r['remaining_duration_estimate']={
 'calendar_days':None,
 'confidence':'Original converse is complete; remaining unrestricted direct and rate closure have not been calibrated by an accepted comparable proof.',
 'schedule_change':'The accepted original graded verification package has no remaining acceptance blocker. Main-critical work now consists of direct achievability, its fixed-W consequences and rate/Main closure.',
 'next_calibration_event':'Acceptance of a complete actual normalized direct decoder with state-uniform success and sharp enough overlap-shell estimate.',
 'not_used_as_effort_estimates':['declaration counts','code lines','build/audit seconds','GPU hours']}
r['next_acceptance_packages']=[
 {'id':'unrestricted-direct','acceptance':'Actual legal unrestricted POVM, normalization, actual per-state success identity and bound valid whenever k-n diverges.'},
 {'id':'fixed-W-direct-and-main','acceptance':'Original fixed-W postprocessing, all four uniform limits to one, required covariance/rate identities, original unchanged Main theorem and strict release.'}]
r['graded_verification_milestone']={
 'scope':closed,'frozen_commit':result['peer_frozen_commit'],'integration_commit':result['local_integration_commit'],
 'validation':validation,'passed':True,'original_hypotheses_and_conclusions_preserved':True,
 'all_POVMs_preserved':True,'critical_bounds_are_premises':False,
 'original_main_and_public_definitions_changed':False,'complete_original_converse_closed':True,
 'literal_Gaussian_shell_formula_closed':False,'main_complete':False}
r['resource_allocation'].update({
 'local':'This coordinator is the sole Mac writer; independent project-clean whole-root check and full audit.',
 'cloud':'Peer-owned isolated execution directory plus a fresh exact-dependency/cache reproduction; both reused for this acceptance instead of creating a third cloud build.',
 'comparison_scope':'One Mac check plus two Linux checks; all frozen formal inputs and complete audit logs agree.',
 'measurement_record':validation,'measured_cloud_total_seconds':result['fresh_cloud_total_seconds'],
 'mounted_data_disk':'User-authorized nominal 200GiB disk at /data; fresh reconstruction and proof workers use it.',
 'allocation_conclusion':'Existing 8-vCPU/~30GiB cloud resources remain sufficient; no GPU or larger server is justified by this milestone. GitHub is external.'})
r['organization_milestone']['main_statement']='Original complete Main unchanged. Its full converse clause is proved; direct limits to one, exact copy rates and final Main proof remain open.'
r['coordinated_next_work']['verification']='Peer graded verification 583897b accepted after two Linux checks and an independent Mac check, complete audit/source comparison and three semantic reviews.'
r['coordinated_next_work'].pop('unaccepted_peer_development',None)
(DOC/'remaining-work.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')

g=json.loads((DOC/'paper-dependency-graph.json').read_text())
nodes={n['id']:n for n in g['nodes']}
def update(key,status,decls,scope,remaining=''):
    n=nodes[key]
    n.update(formal_status=status,lean_declarations=decls,semantic_scope=scope,
             paper_coverage=scope,remaining=remaining,validation=validation)
q='StabilizerLearning.Quantum.'
w='StabilizerLearning.FixedConstraints.'
s='StabilizerLearning.'
update('foundation:character-extension-count','Lean_verified_statement',
 [q+'exists_assignment_extension',q+'card_assignmentRestrictionFiber',q+'card_compatibleAssignments'],
  "Surjectivity of the actual original assignment restriction, exact fibers, and compatible-assignment counts on intersections are closed for all primes.")
update('lem:generic-original-score-spectrum','Lean_verified_statement',
 [w+'verificationPayoff_eq_generic_spectrum',w+'reportsCompatible_genericLabel_iff'],
  "The intersection subspace and full phase compatibility of actual generic targets are connected to the original Luders score spectrum.")
update('lem:generic-bayes-bounded-list-conversion','Lean_verified_statement',
 [q+'POVM.boundedListDecoder',q+'POVM.boundedList_bayes_le_decoder',w+'compatibleNearProbability_mean_le_list_mul_exact'],
  "An actual positive normalized decoding POVM is constructed, allowing different alphabets, noninjective targets, and nonuniform target priors; the original generic optimum bound is closed.")
update('lem:generic-original-list-count','partial_actual_compatible_cover_bound',
 [w+'genericCompatibleListSize_le_phase',w+'genericCompatibleListSize_le_coarse',q+'card_assignmentRestrictionFiber'],
  "The uniform upper bound 16*p^(2*n*D+D) for actual realizable phase-compatible lists when D≤m is closed; the original Gaussian shell sum is not the literal result of this cover.",
  "The original Gaussian intersection-dimension shell bijection, summation formula, and specified kappa coefficient remain open; the exact phase-extension factor is closed.")
update('thm:generic-original-bounded-rank-graded-to-exact','Lean_verified_statement',
 [w+'genericVerificationOptimal_le_graded_exact',w+'optimal_verification_average_le_graded_exact'],
  "Both finite graded-to-exact bounds for all original basis-free POVMs are closed, retaining actual L, delta, 1-delta, and p^(-(D+1)).")
update('thm:generic-fixed-W-Bayes-verification-converse','partial_closed_uniform_quantitative_envelope',
 [s+'fixedConstraint_verification_uniform_bounds_source',s+'tendsto_gradedConverseEnvelope_zero',s+'tendsto_gradedTail_zero'],
  "The explicit common-J bound, common o(N²) remainder, and vanishing envelope for the original generic case are proved; uniform limits for the original full task have separate explicit interfaces.",
  "A generic-only UniformLimit/Tendsto wrapper has not been separately stated; existing quantified bounds and envelope decay are not presented as that named endpoint.")
update('cor:full-fixed-W-verification-converse','Lean_verified_statement',
 [s+'fixedConstraint_verification_uniformLimits_source',s+'fixedConstraint_four_uniform_limits_zero'],
  "The average/worst verification UniformLimit 0 results for the original full-state prior and all POVMs are closed, as are all four original converse limits.")
n=nodes['thm:fixed-W-no-discount']
n['formal_status']='statement_only'
n['remaining']="The original Main is unchanged and still has no final proof. The complete original converse clause (both original exact bounds and all four UniformLimit 0 results) is closed; unrestricted direct achievability, four limits to one, rate/Main, and separately listed covariance interfaces remain open."
n['paper_coverage']="The complete original main target remains a statement only; its entire converse clause has closed dependencies but is not the complete Main."
g['graded_validation']={'record':validation,'frozen_commit':result['peer_frozen_commit'],'entire_original_converse_closed':True,'main_complete':False}
g['semantic_milestones']['luders-reduction']['remaining']="The average identity does not claim equality of scores conditioned on each ν. A fixed 1/p residual does not imply decay to zero; this stage closes the original verification converse using actual phase-compatible lists and a tail vanishing with D."
g['semantic_milestones']['section-bridges']['remaining']="Literal phase-adjusted Weyl/W_A/W_C and named verifier-operator interfaces remain partly open; this stage closes the original compatible-list argument and complete converse. Refined-verification-specific interfaces, direct achievability, and Main remain separately open."
(DOC/'paper-dependency-graph.json').write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
subprocess.run(['python3','scripts/theorem_map.py','--audit-log',str(HERE/'local/axioms.log')],cwd=ROOT,check=True)

diagram='''flowchart BT
  Counts[Actual completion / prescribed ranks / row-space] --> J[Finite probability bound and common J]
  Phase[Actual phase extension and restriction fibers] --> List[Actual realizable compatible-list bound]
  List --> Bayes[Positive normalized POVM list decoding]
  Luders[Original Luders scores and compatible spectra] --> Graded[Finite graded-to-exact]
  Bayes --> Graded
  Graded --> Verification[Two original uniform verification limits to zero]
  J --> Verification
  Delta[Actual full prior and exceptional mass] --> Verification
  J --> Exact[Two original exact bounds and two uniform limits to zero]
  Exact --> Converse[Complete original converse clause proved]
  Verification --> Converse
  Converse -. proved component; Main still unproved .-> Main[Original Main remains a statement only]
  Direct[Actual decoder / overlap shells / all-input W postprocessing pending] -.-> Main
  Rates[Four limits to one and copy-rate pending] -.-> Main
'''
report=f'''# Original graded verification and the complete converse: three-way acceptance

Mathematical freeze: `{result['peer_frozen_commit']}`. Mac integration: `{result['local_integration_commit']}`.
Lean 4.24.0 and mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` remain locked.

**The entire converse clause of the original main target has been accepted; the complete Main is still a statement only.**
The original paper, Main, and shared Pauli/state/task/Rates definitions are unchanged; counting, probability, and asymptotic bounds have not been made assumptions of the endpoint theorem.

## Proofs actually closed

- Actual phase-assignment extension and exact restriction-fiber cardinalities; the uniform bound `L_D <= 16*p^(2*n*D+D)` for the original realizable, phase-compatible lists when `D≤m`, covering all primes and finite-dimensional boundary cases.
- For any original POVM, construct a positive semidefinite, normalized list decoder, allowing distinct report/target alphabets and noninjective targets; the average retains the actual input prior. Empty lists have a valid fallback output.
- The finite bound from the original Lüders compatible-near event to exact identification, and restoration of the actual full prior: `S_av <= delta+(1-delta)*(L_D*P_generic_exact+p^(-(D+1)))`.
- Set `D=Nat.sqrt N` and prove its growth, feasibility, and the `o(N^2)` size of the extra exponent. Retain the common J, square-root tail, and complete-prior exceptional term; choose the remainder and threshold uniformly before all W.
- `fixedConstraint_uniform_converse` returns the original two exact bounds and four original `UniformLimit ... 0` conclusions, preserving all POVMs, all inputs, and the `sup_M inf_x` order.

[Constructive Bayes reduction](../../../StabilizerLearning/FiniteCopy/BoundedList.lean) · [Finite graded comparison](../../../StabilizerLearning/FixedConstraints/GradedComparison.lean) · [Original converse endpoint](../../../StabilizerLearning/Bounds/VerificationConverse.lean)

## Acceptance evidence

Both Linux checks from the other process passed: the execution copy's project artifacts were cleared, and a second directory independently checked out exact dependencies and obtained the official cache, with zero project oleans before building. This process additionally cleared the Mac project cache, rebuilt the entire root, audited all declarations, and ran the original Main release gate. Existing compilers on both platforms were reused; their versions and installation-archive SHA-256 values were checked against the locks.

The three complete axiom logs are byte-for-byte identical, as are the hashes of the {result['formal_input_files']} frozen formal inputs.
The audit covers {result['total_declarations_audited']} project declarations, including {result['theorem_declarations_audited']} theorems; all {result['required_transitive_proof_links']} specified actual dependencies passed. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. These counts describe audit coverage, not completion percentages or schedule metrics.

[Three-way comparison](comparison.json) · [Mac checks](local/check.json) · [The other process's two Linux records](../2026-10-11-graded-verification/comparison.json) · [Independent semantic review](independent-review.md) · [Actual proof paths](converse-closure.json)

```mermaid
{diagram}```

## Scope and remaining schedule

The actual sufficient list bound is proved; the paper's exact Gaussian shell sum and specified kappa coefficient remain unproved and must not be marked as closed original formulas merely because the converse is closed. Explicit uniform quantified bounds and a vanishing envelope specific to the generic case are proved, but their named Tendsto wrapper has not been separately stated; the original full task's two uniform verification limits have complete endpoints.

The original Main release gate still correctly rejects the project: unrestricted direct achievability, fixed-W postprocessing for all inputs, the four limits to one, and rate/Main closure are missing. Full covariance, refined verification, and related interfaces are listed separately in the correspondence table. Importing Main from the root does not mean that a main proof exists.

The list, Bayes, graded, and original-converse obligations actually closed in this stage have been removed from the remaining critical path. The next acceptance package is an actual per-state decoder, actual overlap shells, and fixed-W postprocessing for all inputs. No comparable complete direct proof is available to support a reliable total number of days; audit minutes, declaration counts, and GPU hours are not converted into proof-development time.

[Inventory of remaining proof packages](remaining-proof-packages.md) · [Remaining-work checklist](../../remaining-work.json) · [Itemized theorem correspondence](../../theorem-map.md)

The cloud uses the user-authorized mounted data disk `/data` (nominally 200 GiB); it reuses the other process's two independent acceptance runs rather than launching a third cloud build. The Mac has a single writer. GitHub remains assigned to other processes; this task synchronizes only the private branch.
'''
(HERE/'README.md').write_text(report)
arch=DOC/'architecture.md'
text=arch.read_text()
start=text.index('```mermaid')
end=text.index('```',start+3)+3
arch.write_text(text[:start]+'```mermaid\n'+diagram+'```'+text[end:])
main=DOC/'main-statement.md'
text=main.read_text()
start=text.index('\u672c\u8f6e\u53e6\u5df2\u9a8c\u6536')
end=text.index('\u8fd9\u4e9b\u90fd\u4e0d\u80fd\u4f5c\u4e3a\u672a\u6765\u4e3b\u5b9a\u7406\u7684\u65b0\u589e\u5047\u8bbe\u3002',start)
text=text[:start]+'''Arbitrary frames/Clifford implementations, actual Luders scores, the original fixed-W exact comparisons, and exceptional mass have been accepted.
This stage additionally closes actual phase-compatible lists, the Bayes reduction for all POVMs, finite graded-to-exact,
and uniform verification decay. `fixedConstraint_uniform_converse` supplies the entire original Rates
converse clause: both original exact bounds and all four UniformLimit 0 results.
See `theorem-map.md` for current open obligations: unrestricted direct achievability, W postprocessing for all inputs, four limits to one,
covariance, and final rate/Main; exact Gaussian shells and refined-verification interfaces are listed separately.
'''+text[end:]
main.write_text(text)
readme=ROOT/'README.md'
text=readme.read_text()
text=text.replace('- [\u4efb\u610f\u6846\u67b6\u4e0e\u539f fixed-W exact converse \u9a8c\u6536]',
  '- [Original graded verification and complete converse: three-way acceptance](docs/validation/2026-10-11-graded-integration/README.md)\n- [Acceptance of arbitrary frames and the original fixed-W exact converse]',1)
start=text.index('\u8fd9\u4e9b\u5c40\u90e8\u7ed3\u8bba\u6ca1\u6709\u5047\u8bbe\u5173\u952e\u8ba1\u6570\u754c')
end=text.index('\n## \u6784\u5efa',start)
text=text[:start]+'''Arbitrary frames/Clifford implementations, actual Luders scores, the original fixed-W finite exact comparisons, and exceptional mass are closed.
Actual phase-compatible lists, the constructive all-POVM Bayes reduction, and uniform verification decay have also been accepted,
giving the entire converse clause of the original main target; the key counting and asymptotic bounds are proved.
The complete Main still needs unrestricted direct achievability, W postprocessing for all inputs, limits to one, and rate closure.
Exact Gaussian shells, refined verification, and full covariance retain separately scoped statuses; not every paper entry is claimed as proved.
See the correspondence table for remaining obligations; completion is not reported by lines of code, declaration counts, or compilation time.
'''+text[end:]
start=text.index('\u5f53\u524d\u9636\u6bb5\u9a8c\u6536\u8bb0\u5f55\uff1a')
end=text.index('\n\n',start)
text=text[:start]+'''Current stage acceptance record: [original graded verification and complete converse](docs/validation/2026-10-11-graded-integration/README.md).
Mathematical freeze `583897b`; the Mac and two Linux rebuilds/complete audits passed, with identical sources and complete audit logs and only the three standard axioms. The final Main gate still correctly rejects the missing complete proof.'''+text[end:]
readme.write_text(text)
cloud=json.loads((DOC/'cloud-runtime.json').read_text())
cloud.update(verified_clean_build='/data/lean/StabilizerLearning-clean-20261011-graded-583897b83f27',
 verified_source_hashes_record='docs/validation/2026-10-11-graded-verification/fresh/reproduction.json',
 last_stage_total_seconds=result['fresh_cloud_total_seconds'],
 cloud_state='Original graded verification and complete original converse accepted after two Linux checks plus independent Mac check; direct/rates/Main remain open.',
 temporary_tunnel_status='Own previous 17894 tunnel and peer-owned graded download 17895 tunnel were closed by their owners after downloads; no unrelated tunnel modified.',
 final_validation_source_clone='/data/lean/tasks/graded-integration',
 network='Peer used task-scoped proxy 127.0.0.1:17895 for exact fresh dependencies and official cache; no global networking changes. This coordinator reused its read-only validation evidence.')
cloud['storage']['measurement_record']='docs/validation/2026-10-11-graded-integration/cloud-postflight.json'
meta=json.loads((HERE/'cloud-postflight.json').read_text())
cloud['storage']['postflight_df']=meta['storage']
for line in meta['storage'].splitlines():
 parts=line.split()
 if len(parts)>=6 and parts[-1]=='/data' and parts[3].endswith('G'):
  cloud['storage']['data_available_gib_after_stage_approx']=float(parts[3][:-1])
 if len(parts)>=6 and parts[-1]=='/' and parts[3].endswith('G'):
  cloud['storage']['root_volume_free_gib_approx']=float(parts[3][:-1])
cloud['final_validation_source_directory']=cloud.pop('final_validation_source_clone')
(DOC/'cloud-runtime.json').write_text(json.dumps(cloud,ensure_ascii=False,indent=2)+'\n')
print('Updated scope and remaining work from completed three-way acceptance.')
