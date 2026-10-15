#!/usr/bin/env python3
"""Bind actual completion closure to clean-build hashes and checked proof dependencies."""
from pathlib import Path
import json,re,hashlib,datetime
R=Path(__file__).resolve().parents[1];E=R/'evidence'
r=json.loads((E/'completion-reproduction.json').read_text())
assert r['result']=='pass' and r['fresh_project_oleans_before_build']==0
for name,h in r['project_source_sha256'].items():
 assert hashlib.sha256((R/'pilot'/name).read_bytes()).hexdigest()==h,name
review=json.loads((E/'completion-independent-review.json').read_text())
assert review['status']=='semantic_review_passed'
for name,h in review['source_sha256'].items():
 assert hashlib.sha256((R/'pilot/StabilizerPilot'/name).read_bytes()).hexdigest()==h,name
cross=(E/'completion-rank-independent-review.md').read_text()
for name,h in re.findall(r'`([^`]+\.lean)` SHA-256: `([0-9a-f]+)`',cross):
 assert hashlib.sha256((R/'pilot/StabilizerPilot'/name).read_bytes()).hexdigest()==h,name
log=(E/'completion-clean-axioms.log').read_text()
assert 'AUDIT_OK' in log and 'error:' not in log
rows=[json.loads(line.split('DEPENDENCY_JSON ',1)[1]) for line in log.splitlines() if 'DEPENDENCY_JSON ' in line]
lean={'kind':'kernel-checked types and values; direct project constant references',
 'edge_direction':'prerequisite_to_dependent','main_theorem_present':False,
 'nodes':[{'id':d['declaration']} for d in rows],
 'edges':[{'from':p,'to':d['declaration']} for d in rows for p in d['direct_project_dependencies']],
 'audit_count':int(re.search(r'AUDIT_OK.*?: (\d+) theorem declarations',log)[1]),
 'checked_transitive_links':[line.split('DEPENDENCY_OK ',1)[1] for line in log.splitlines() if 'DEPENDENCY_OK ' in line],
 'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'reviewed_source_matches_clean_build':True}
(E/'completion-lean-dependencies.json').write_text(json.dumps(lean,ensure_ascii=False,indent=2)+'\n')
g=json.loads((R/'planning/paper-dependency-graph.json').read_text())
assert hashlib.sha256((R/g['source_file']).read_bytes()).hexdigest()==g['source_sha256']
mapping={
 'lem:first-congruence':['rank_completion_first_reduction','schurTranslationEquiv','exists_symmetric_normal_form'],
 'lem:radical-rank-identity':['rank_radical_blocks','rank_radical_of_normalizers'],
 'lem:completion-bijective-parameterization':['completionAllEquiv','completionPairsRankEquiv'],
 'prop:exact-ambient-completion-count':['card_completionPairs_eq_source','card_completionPairs_zero','card_completionPairs_rank_only'],
 'lem:binary-Schur-reduction':['rank_completion_first_reduction','schurTranslationEquiv','exists_symmetric_normal_form'],
 'lem:binary-radical-rank-identity':['rank_radical_blocks','rank_radical_of_normalizers','radicalKernelEquiv'],
 'lem:binary-completion-parameterization':['completionAllEquiv','completionPairsRankEquiv'],
 'lem:integrated-binary-completion-count':['binary_completion_count','card_completionPairs_zero','card_completionPairs_rank_only']}
route_variants={'lem:completion-bijective-parameterization','lem:binary-completion-parameterization'}
ids={n['id'] for n in g['nodes']};assert set(mapping)<=ids
for n in g['nodes']:
 if n['id'] in mapping:
  n.update(formal_status='Lean_verified_statement',lean_declarations=['StabilizerPilot.'+d for d in mapping[n['id']]],
   semantic_scope='Actual ambient pairs (Q,C), Q symmetric, rank of the full block matrix <= k. Original finite sum and rank-only dependence; arbitrary finite fields include both prime branches.',
   integration='Actual completionPairs_count_bound calls the proved exact count and both prescribed-rank estimates. Moment-realizable inclusion and main theorem remain open.')
  if n['id'] in route_variants:
   n.update(formal_status='Lean_verified_counting_route',
    semantic_scope='A genuine full-space equivalence with once-chosen proved normalizers, then genuine rank stratification and budget restriction, fully proves the actual count. The source lemma interface quantified over arbitrary externally supplied P/R/S and a single fixed-rank fiber is not separately declared.',
    lean_declarations=['StabilizerPilot.'+d for d in ['completionAllEquiv','completionAllEquiv_rank','completionFiberRankEquiv','completionPairsRankEquiv']])
 if n['id'] in {'lem:symmetric-rank-bound','lem:integrated-binary-symmetric-rank-bound','cor:symmetric-rank-partial-sum'}:
  n['integration']='The actual completionPairs_count_bound now calls the proved prescribed-rank estimates via the proved actual-set cardinality formula. Probability interfaces and main theorem remain open.'
 if n['id']=='prop:uniform-completion-bound':
  n.update(formal_status='partial_actual_set_bound_constant_16',
   lean_declarations=['StabilizerPilot.completionPairs_count_bound'],
   remaining='Original specifically named kappa_GL^-1*K_sym constant and row-space parameter mapping to E_fin are not certified. Geometry and actual completion-set cardinality are closed.',
   semantic_scope='Actual ambient matrix-completion set <=16*(m+1)^2*q^(grid.sup E), unconditionally in the rank budget.')
for e in g['edges']:
 if e['to'] in mapping:
  e['route_note']='Source proof route; verified concrete kernel dependencies are in completion-lean-dependencies.json.'
g['completion_update']={'verified_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'closed_source_statements':[n for n in mapping if n not in route_variants],
 'verified_counting_route_variants':sorted(route_variants),'actual_completion_count_complete':True,
 'moment_realizable_count_exact':False,'main_theorem_complete':False,
 'public_count':'StabilizerPilot.card_completionPairs_eq_source',
 'public_bound':'StabilizerPilot.completionPairs_count_bound'}
g['validation']['closed_completion_source_statements']=len(mapping)-len(route_variants)
g['validation']['verified_completion_counting_route_variants']=len(route_variants)
g['acceptance']['clean_rebuild']='actual completion branch passed; see completion-reproduction.json'
g['scope_warning']='Curated paper obligation DAG with verified local source mappings; no Lean main declaration exists. Actual Lean proof graph is separate.'
g['overview_status']='Rank and ambient-completion branches are closed; probability, physical-model and main theorem obligations remain open.'
for dest in [R/'planning/paper-dependency-graph.json',E/'completion-paper-dependency-graph.json']:
 dest.write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
plan={'updated_at':g['completion_update']['verified_at'],
 'newly_removed_from_remaining_work':['arbitrary-field radical kernel/rank identity','proved rectangular and symmetric normalizer existence','actual completion parametrization and both inverse laws','exact cardinality, source nested sum, empty branch, rank-only dependence','actual completion set connected to proved prescribed-rank bounds'],
 'next_acceptance_milestone':'actual row-space event probability bound plus its moment-to-completion connection',
 'next_paper_targets':['prop:all-prime-row-space-event-bound','cor:all-prime-augmented-row-space-event-bound','lem:visible-to-ambient-completion'],
 'remaining_major_branches':['finite structural probability/weight estimates','uniform finite exponent optimization and asymptotic reduction','quantum/POVM, stabilizer/Witt/Clifford and quotient-PGM interfaces','original fixed-W operational main statement and recursive audit'],
 'remaining_source_interface_details':['source-defined kappa_GL^-1*K_sym coefficient and row-space mapping to E_fin','literal arbitrary-normalizer fixed-rank-fiber interfaces for the two parameterization lemmas (the exact actual-set count is already closed)'],
 'calendar_deadline':None,'reason':'Completed counting and completion chains are now reusable. Probability/representation branches still lack measured closed-development samples; compilation seconds and declaration counts are not proof-development hours.',
 'clean_build_seconds':r['total_seconds'],'main_complete':False}
(R/'planning/remaining-work.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
(E/'completion-work-estimate.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'theorem_declarations':lean['audit_count'],'declarations':len(rows),'edges':len(lean['edges']),'checked_links':len(lean['checked_transitive_links']),'new_source_mappings':len(mapping)},ensure_ascii=False))
