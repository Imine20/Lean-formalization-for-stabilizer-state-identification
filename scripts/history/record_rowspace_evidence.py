#!/usr/bin/env python3
"""Bind the moment/probability closure to reviewed source and Linux clean-build proof terms."""
from pathlib import Path
import datetime,hashlib,json,re
R=Path(__file__).resolve().parents[1]; E=R/'evidence'
def read(name): return json.loads((E/name).read_text())
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
c=read('rowspace-cloud-reproduction.json')
assert c['result']=='pass' and c['platform']=='Linux-x86_64'
assert c['fresh_project_oleans_before_build']==0 and not c['main_theorem_complete']
assert c['compiler_archive_sha256']==json.loads((R/'toolchain-lock.json').read_text())['compiler_assets']['Linux-x86_64']['sha256']
for name,h in c['project_source_sha256'].items(): assert digest(R/'pilot'/name)==h,name
metrics=read('rowspace-local-metrics.json');assert len(metrics)==2 and all(s['exit_code']==0 for s in metrics)
reviewed=set()
for name in ['rowspace-counting-independent-review.json','moment-rowspace-independent-review.json','prescribed-radical-independent-review.json','moment-average-independent-review.json']:
 d=read(name)
 status=d.get('status',d.get('result',d.get('review_status','')))
 assert status.startswith('pass'),(name,status)
 assert not d.get('issues') and not d.get('findings'),name
 pairs=list(d.get('source_sha256',{}).items())
 pairs += [(x['path'],x['sha256']) for x in d.get('files',[])]
 assert pairs,name
 for p,h in pairs:
  p=Path(p);p=p if p.is_absolute() else R/p
  assert digest(p)==h,(name,str(p));reviewed.add(str(p.relative_to(R)))
new_modules=['RowSpaceDefs','RowSpaceGeometry','IntervalSubspaces','PrescribedRadicalArithmetic','PrescribedRadical','RowSpaceProbabilityBase','RowSpaceProbability','MomentCompletion','MomentRowSpace','BinaryMomentCompletion','BinaryMomentRowSpace','MomentProbabilityBridge']
assert {f'pilot/StabilizerPilot/{n}.lean' for n in new_modules} <= reviewed

def parse(log):
 assert 'AUDIT_OK' in log and 'error:' not in log
 rows=[json.loads(x.split('DEPENDENCY_JSON ',1)[1]) for x in log.splitlines() if 'DEPENDENCY_JSON ' in x]
 return {'nodes':[{'id':d['declaration']} for d in rows],
  'edges':[{'from':p,'to':d['declaration']} for d in rows for p in d['direct_project_dependencies']],
  'audit_count':int(re.search(r'AUDIT_OK.*?: (\d+) theorem declarations',log)[1]),
  'checked_transitive_links':[x.split('DEPENDENCY_OK ',1)[1] for x in log.splitlines() if 'DEPENDENCY_OK ' in x]}
l=parse((E/'rowspace-cloud-axioms.log').read_text());local=parse((E/'rowspace-local-axioms.log').read_text())
assert l['audit_count']==local['audit_count']
assert {x['id'] for x in l['nodes']}=={x['id'] for x in local['nodes']}
assert {(x['from'],x['to']) for x in l['edges']}=={(x['from'],x['to']) for x in local['edges']}
assert set(l['checked_transitive_links'])==set(local['checked_transitive_links'])
l.update(kind='kernel-checked types and proof terms',edge_direction='prerequisite_to_dependent',
 main_theorem_present=False,allowed_axioms=['propext','Classical.choice','Quot.sound'],
 platforms_agree=True,reviewed_source_matches_clean_build=True)
(E/'rowspace-lean-dependencies.json').write_text(json.dumps(l,ensure_ascii=False,indent=2)+'\n')
g=json.loads((R/'planning/paper-dependency-graph.json').read_text())
assert digest(R/g['source_file'])==g['source_sha256']
mapping={
 'prop:all-prime-prescribed-radical-bound':['prescribed_radical_subspace_bound','prescribed_radical_containing_bound','exists_prescribed_radical_constant'],
 'prop:all-prime-row-space-event-bound':['rowSpace_event_probability_bound','rowSpace_event_probability_bound_containing'],
 'cor:all-prime-augmented-row-space-event-bound':['augmentedRowSpace_event_probability_bound'],
 'lem:common-Gram-radical-rank':['rank_gram_eq_finrank_sub_radical','rank_augmented_gram'],
 'lem:visible-to-ambient-completion':['momentFiberVisibleEquiv','card_momentFiber_eq_visible','visibleToCompletion','occurringMomentCount_le_exact_completion'],
 'prop:binary-enhanced-bilinear-comparison':['binaryEnhancedCoordinatesEquiv','binaryFiberToCompletion','binary_forgetful_fiber_card_le','binaryOccurringFiber_card_le_exact_completion']}
ids={n['id'] for n in g['nodes']};assert set(mapping)<=ids
leanids={n['id'] for n in l['nodes']}
for ds in mapping.values(): assert {'StabilizerPilot.'+d for d in ds}<=leanids
for n in g['nodes']:
 if n['id'] in mapping:
  n.update(formal_status='Lean_verified_statement',lean_declarations=['StabilizerPilot.'+d for d in mapping[n['id']]],
   semantic_scope='Actual finite sets and uniform matrix PMF; original source statements preserved. K=16q witnesses the permitted field-dependent constant. Includes zero dimensions and characteristic two.',
   integration='Actual finite averages invoke both the proved row-event probabilities and genuine moment-to-completion maps, exact ambient count, Gram-radical identity and prescribed-rank bounds.')
 if 'integration' in n and n['id'] not in mapping and any(s in n['integration'].lower() for s in ['moment','probability']):
  n['integration']='Actual ordinary and binary enhanced moment maps and row-space event probabilities now feed the verified finite-average counting chain. Physical PGM/POVM and original main theorem interfaces remain open.'
 if n['id'] in {'thm:converse-weighted-probability-completion-reduction','prop:binary-finite-weighted-completion-reduction'}:
  n.update(formal_status='partial_actual_finite_average_count',
   lean_declarations=['StabilizerPilot.average_occurringMomentCount_bound','StabilizerPilot.average_binaryOccurringFiber_bound'],
   remaining='The verified finite average is unnormalized and unclipped, over actual lower matrices. The original operational PGM success probability, quotient-label normalization, clipped min(1,...) and finite structural exponent interfaces are not yet formalized; no claim of full source theorem closure.')
 if n['id']=='prop:uniform-completion-bound':
  n['remaining']='Source named kappa_GL^-1*K_sym coefficient and normalized/clipped E_fin structural interface remain. Actual moment inclusion, Gram rank a-u and finite averages are now proved.'
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
g['rowspace_update']={'verified_at':now,'closed_source_statements':list(mapping),'actual_moment_maps_complete':True,
 'binary_enhanced_lift_complete':True,'actual_row_event_bounds_complete':True,'actual_finite_average_complete':True,
 'operational_weighted_success_bound_complete':False,'main_theorem_complete':False}
g['validation']['closed_rowspace_moment_source_statements']=len(mapping)
g['acceptance']['clean_rebuild']='Current full local branch passed Linux-x86_64 independent fresh-directory build and recursive audit; same checked project graph on macOS ARM64.'
g['overview_status']='Actual prescribed-rank, ambient-completion, ordinary/binary moment, row-probability and finite-average branches closed. Physical success-probability, clipped structural/asymptotic and main-theorem interfaces remain open.'
for p in [R/'planning/paper-dependency-graph.json',E/'rowspace-paper-dependency-graph.json']:
 p.write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
plan={'updated_at':now,'newly_removed_from_remaining_work':['actual ordinary moment fibre-to-visible equivalence and ambient inclusion','faithful binary enhanced coordinates, actual Gram inclusion and 2^m forgetting fibres','actual Gram rank = row dimension minus radical dimension','isotropic frames, radical-subspace count and prescribed-vector variant','ordinary and augmented actual uniform row-space event probabilities','actual finite averages calling both row probabilities and exact completion / prescribed-rank bounds'],
 'next_acceptance_milestone':'normalized and clipped finite probability/completion reduction with the original finite structural exponent and feasible domains',
 'remaining_major_branches':['connect actual quantum/POVM and PGM formula to the finite moment averages','quotient-label cardinality normalization and clipped min(1,...) completion factors','original odd/binary finite structural exponent optimization and asymptotic reduction','phase/character-group, stabilizer/Witt/Clifford and original fixed-W operational statement','final main theorem recursive dependency and axiom audit'],
 'remaining_source_interface_details':['original named kappa coefficient where a fixed expression is required','literal arbitrary-external-normalizer fixed-rank-fibre interfaces'],
 'calendar_deadline':None,'reason':'The finite counting, moment geometry and row-probability stages are now reusable. Remaining physical and asymptotic branches lack completed development-time samples; theorem counts and compiler seconds are not interchangeable proof work.',
 'resource_allocation':{'local':'editing and incremental builds; final local axiom audit','cloud':'pinned Linux compiler, independent dependency/cache checkout, fresh full build and recursive audit','cloud_cpu_hours_unrestricted_by_user':True,'measured_cloud_total_seconds':c['total_seconds'],'source_graph_matches_local':True},
 'main_complete':False}
(R/'planning/remaining-work.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
(E/'rowspace-work-estimate.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'theorems':l['audit_count'],'declarations':len(l['nodes']),'edges':len(l['edges']),'links':len(l['checked_transitive_links']),'reviewed_new_modules':len(new_modules),'source_statements':len(mapping)},ensure_ascii=False))
