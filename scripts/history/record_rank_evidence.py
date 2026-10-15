#!/usr/bin/env python3
"""Record the newly kernel-checked rank chain, separately from the paper obligation DAG."""
from pathlib import Path
from collections import deque
import json, re, hashlib, datetime
ROOT = Path(__file__).resolve().parents[1]
E = ROOT / 'evidence'
repro = json.loads((E/'rank-reproduction.json').read_text())
assert repro['result'] == 'pass' and repro['fresh_project_oleans_before_build'] == 0
for relative, expected in repro['project_source_sha256'].items():
    assert hashlib.sha256((ROOT/'pilot'/relative).read_bytes()).hexdigest() == expected, relative
review = json.loads((E/'rank-independent-review.json').read_text())
for entry in review['reviewed_files']:
    assert hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest() == entry['sha256'], entry['path']
log = (E/'rank-clean-axioms.log').read_text()
assert 'AUDIT_OK' in log and 'error:' not in log
rows = [json.loads(line.split('DEPENDENCY_JSON ',1)[1]) for line in log.splitlines() if 'DEPENDENCY_JSON ' in line]
assert rows
lean = {'kind':'direct constants from kernel-checked declaration types and values',
        'edge_direction':'prerequisite_to_dependent', 'main_theorem_present':False,
        'nodes':[{'id':r['declaration']} for r in rows],
        'edges':[{'from':p,'to':r['declaration']} for r in rows for p in r['direct_project_dependencies']],
        'audit_count':int(re.search(r'AUDIT_OK.*?: (\d+) theorem declarations',log)[1]),
        'axioms_allowed':['propext','Classical.choice','Quot.sound'],
        'reviewed_source_matches_clean_build':True,
        'checked_transitive_links':[line.split('DEPENDENCY_OK ',1)[1] for line in log.splitlines() if 'DEPENDENCY_OK ' in line]}
(E/'rank-lean-dependencies.json').write_text(json.dumps(lean,ensure_ascii=False,indent=2)+'\n')
graph=json.loads((ROOT/'planning/paper-dependency-graph.json').read_text())
assert hashlib.sha256((ROOT/graph['source_file']).read_bytes()).hexdigest()==graph['source_sha256']
new={
 'lem:symmetric-rank-bound':('odd_prime_symmetric_rank_bound','exists_uniform_symmetric_rank_constant'),
 'lem:integrated-binary-symmetric-rank-bound':('binary_symmetric_rank_bound','exists_uniform_symmetric_rank_constant'),
 'cor:symmetric-rank-partial-sum':('symmetric_rank_partial_sum','card_symmetric_rank_le_bound')}
for n in graph['nodes']:
 if n['id'] in new:
  n.update(formal_status='Lean_verified_statement',
   lean_declarations=['StabilizerPilot.'+t for t in new[n['id']]],
   lean_source='pilot/StabilizerPilot/RankConsequences.lean',
   semantic_scope='Actual standard Matrix.rank and transpose-symmetric matrices. Constant 4 is independent of field and dimensions; original prime specializations and exponent are preserved.',
   integration='Called by proved completion counting expression; actual completion-set bijection and main theorem remain open.')
 elif n['id']=='prop:uniform-completion-bound':
  n.update(formal_status='partial_arithmetic_expression_only',
   lean_declarations=['StabilizerPilot.completion_count_expression_bound'],
   remaining='Actual matrix-completion bijection, original fixed kappa coefficient, parameter/exponent identification with E_fin; not accepted as this proposition.')
 elif n['id']=='foundation:rectangular-rank-count':
  n['partial_lean_result']={'declaration':'StabilizerPilot.rectangular_rank_bound','scope':'Actual count ≤ 4*q^[L(M+S-L)]. The source coefficient kappa_GL^-1 is not claimed.'}
 elif n['id']=='foundation:subspace-counts':
  n['partial_lean_result']={'declaration':'StabilizerPilot.card_rankSubspaces_le','scope':'Dimension-uniform Grassmann upper bound from genuine independent-frame encoding; full incidence/exact formulas not claimed.'}
for e in graph['edges']:
 if e['to'] in new:
  e['route_note']='Paper proof route. The verified Lean proof uses compression, independent frames, and a finite GL product; see rank-lean-dependencies.json.'
paths={}
adj={n['id']:[] for n in graph['nodes']}
for e in graph['edges']: adj[e['from']].append(e['to'])
for source in list(new)[:2]:
 queue=deque([[source]])
 while queue:
  path=queue.popleft()
  if path[-1]==graph['main_theorem']:
   paths[source]=path;break
  for nxt in adj[path[-1]]:
   if nxt not in path:queue.append(path+[nxt])
graph['rank_update']={'verified_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'closed_source_statements':list(new),'paths_to_main':paths,
 'real_Lean_chain':['geometric_product_lower','card_GL_lower','card_rankSubspaces_le','symmetric_rank_bound','symmetric_rank_partial_sum','completion_rank_slice_symmetric_bound'],
 'full_expression_chain':['symmetric_rank_bound','rectangular_rank_bound','completion_rank_summand_bound','completion_count_expression_bound'],
 'main_theorem_complete':False}
graph['scope_warning']='Paper proof-obligation DAG plus verified source-statement mappings. This is not a Lean main-theorem dependency tree; no main declaration exists. Direct proof-term graph is a separate artifact.'
graph['validation']['closed_rank_source_statements']=3
graph['acceptance']['clean_rebuild']='rank pilot passed; see rank-reproduction.json'
graph['overview_status']='Three original pilot results and three rank-source statements are locally closed; actual main theorem remains open.'
(ROOT/'planning/paper-dependency-graph.json').write_text(json.dumps(graph,ensure_ascii=False,indent=2)+'\n')
(E/'rank-paper-dependency-graph.json').write_text(json.dumps(graph,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'audit_theorems':lean['audit_count'],'project_declarations':len(rows),'project_edges':len(lean['edges']),'checked_transitive_links':len(lean['checked_transitive_links']),'closed_source_rank_statements':list(new)},ensure_ascii=False))
