#!/usr/bin/env python3
"""Rebuild the paper/Lean map from curated scope plus actual checked dependencies."""
from pathlib import Path
import argparse,hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
DOC=ROOT/'docs'
g=json.loads((DOC/'paper-dependency-graph.json').read_text())
source=(ROOT/g['source_file']).read_text()
assert hashlib.sha256(source.encode()).hexdigest()==g['source_sha256']
parser=argparse.ArgumentParser()
parser.add_argument('--audit-log',type=Path,default=DOC/'validation/2026-10-11-direct-integration/local/axioms.log')
args=parser.parse_args()
log=args.audit_log.read_text()
assert 'AUDIT_OK' in log and 'error:' not in log
raw=[json.loads(l.split('DEPENDENCY_JSON ',1)[1]) for l in log.splitlines() if 'DEPENDENCY_JSON ' in l]
ids={r['declaration'] for r in raw}
parents={r['declaration']:r['direct_project_dependencies'] for r in raw}
main_proof = ('MAIN_STATUS dependencies_closed: exact original target theorem is present' in log
              and 'StabilizerLearning.fixedW_noCopyRateDiscount' in ids)
lean={'kind':'checked declaration types and bodies; exact main type checked' if main_proof else
       'checked declaration types and bodies; main target is a definition, not a theorem',
 'main_target':'StabilizerLearning.FixedWNoCopyRateDiscount','main_proof_present':main_proof,
 'audit_log':str(args.audit_log.resolve().relative_to(ROOT)),
 'audit_log_sha256':hashlib.sha256(log.encode()).hexdigest(),
 'nodes':[{'id':r['declaration']} for r in raw],
 'edges':[{'from':d,'to':r['declaration']} for r in raw for d in r['direct_project_dependencies']],
 'axiom_allowlist':['propext','Classical.choice','Quot.sound'],
 'key_proof_links':[l.split('DEPENDENCY_OK ',1)[1] for l in log.splitlines() if 'DEPENDENCY_OK ' in l]}
(DOC/'lean-dependencies.json').write_text(json.dumps(lean,ensure_ascii=False,indent=2)+'\n')
paper_labels=[]
for b in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[[^\]]*\])?([\s\S]*?)\\end\{\1\}',source):
 label=re.search(r'\\label\{([^}]+)\}',b[2]);assert label,'Unlabelled paper statement'
 paper_labels.append(label[1])
assert set(paper_labels)<={n['id'] for n in g['nodes']}
rows=[]
for n in g['nodes']:
 status=n['formal_status']
 decls=n.get('lean_declarations',n.get('formal_source',{}).get('declarations',[]))
 assert set(decls)<=ids,(n['id'],set(decls)-ids)
 if status=='statement_only': ps='Statement only';coverage='Complete target; the final main proof is not closed'
 elif status in ['Lean_verified_statement','Lean_verified_pilot_not_integrated_into_main']:
  ps='Dependencies closed';coverage='The listed results and their actual dependencies are closed' if main_proof else 'The listed local results are closed; no main-theorem proof is available yet'
 elif status.startswith('partial_') or status=='Lean_verified_counting_route':
  ps='Checked';coverage='Partial results or an alternative route; the original item is not fully covered'
 else:ps='Not formalized';coverage='No corresponding Lean result'
 coverage=n.get('paper_coverage',coverage)
 rows.append({'paper_id':n['id'],'title':n['title'],'source_line':n['statement_start_line'],
  'is_paper_statement':n['id'] in paper_labels,'proof_status':ps,'paper_coverage':coverage,
  'lean_declarations':decls,'paper_dependencies':[e['from'] for e in g['edges'] if e['to']==n['id']],
  'lean_direct_dependencies':sorted({d for decl in decls for d in parents[decl]}),
  'remaining':n.get('remaining',n.get('semantic_scope',''))})
semantic=[
 ('phase-completeness','Periodicity and injectivity of complex phase encoding, and completeness for physical eigenvalues',['Quantum.rootPhase','Quantum.eigenPhase','Quantum.Compatible'],[]),
 ('pauli-representation','Unitarity of the concrete Pauli operators, multiplication/cocycle, and equivalence of commutation with symplectic orthogonality',['Quantum.pauli','Quantum.sectionCocycle'],['phase-completeness']),
 ('projectors','Orthogonality, self-adjointness, PSD, rank formulas, and completeness of the joint-projector family',['Quantum.jointProjector'],['pauli-representation']),
 ('stabilizer-ensemble','Every valid label projector is a pure density matrix, with a correspondence to all projective stabilizer states',['Quantum.IsPureStabilizer','Quantum.StabilizerState'],['projectors']),
 ('nonempty','Nonemptiness of stabilizer inputs, valid reports, and the set of all learner POVMs',['FixedConstraints.Report','FixedConstraints.Learner'],['projectors','stabilizer-ensemble']),
 ('exact-criterion',"Equivalence of the physical eigenvalue equations with the paper's K≤Lₓ and η=χₓ|K criterion",['FixedConstraints.Valid'],['stabilizer-ensemble']),
 ('probabilities','Positivity and normalization of tensor densities, Born probabilities, and membership of the four optima in [0,1]',['Quantum.tensorPower','Quantum.born','FixedConstraints.optimal'],['nonempty','projectors']),
 ('luders-reduction',"The actual Lüders average equals the report's Born score, and correct reports score one",['FixedConstraints.verificationPayoff'],['projectors','probabilities']),
 ('section-bridges','Bridges from the uniform XZ section to odd-prime Weyl/binary Z₄ coordinates and the proved moment chain',['Quantum.pauli'],['phase-completeness','stabilizer-ensemble']),
 ('covariance-rates','Dimension-only covariance, achievable-rate sets, and liminf/sInf properties',['FixedConstraints.AchievableExactRate','FixedConstraints.exactCopyRate'],['probabilities','exact-criterion','luders-reduction'])]
for key,title,defs,deps in semantic:
 row={'paper_id':'semantic:'+key,'title':title,'source_line':182,'is_paper_statement':False,
  'proof_status':'Not formalized','paper_coverage':'Concrete definitions are available; the stated semantic theorems have not yet been stated or proved',
  'lean_declarations':['StabilizerLearning.'+d for d in defs],
  'paper_dependencies':['semantic:'+d for d in deps],'lean_direct_dependencies':[],
  'remaining':title+'. These must not be turned into hypotheses of the main theorem.'}
 row.update(g.get('semantic_milestones',{}).get(key,{}))
 assert set(row['lean_declarations'])<=ids,(row['paper_id'],set(row['lean_declarations'])-ids)
 row['lean_direct_dependencies']=sorted({d for decl in row['lean_declarations'] for d in parents[decl]})
 rows.append(row)
result={'main_status':'Dependencies closed' if main_proof else 'Statement only','main_theorem_complete':main_proof,'paper_statement_coverage':{'total':len(paper_labels),'mapped':len(paper_labels)},
 'status_definitions':{'Not formalized':'No Lean statement of this result is available yet','Statement only':'The concrete Prop has been type-checked, but has no proof yet',
 'Proof contains placeholders':'Contains sorry, unproved mathematical axioms, or similar placeholders; permitted only on isolated experimental branches and cannot pass the formal audit',
 'Checked':'The listed local declarations have passed the kernel; the original paper item may be only partially covered',
 'Dependencies closed':'The listed complete results and their actual dependencies have been audited; the main theorem is additionally checked by the exact-type release gate'},
 'rows':rows,'progress_policy':'Use mathematical statement coverage and dependency closure, never lines or generated file counts.'}
(DOC/'theorem-map.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
out=['# Paper theorems and Lean declarations','',
 ('Main-theorem status: **Dependencies closed**. The exact type of `fixedW_noCopyRateDiscount` has passed the original-target audit.'
  if main_proof else 'Main-theorem status: **Statement only**. The root entry point imports Main; the final proof does not yet exist.'),
 'This table covers every theorem/lemma/proposition/corollary environment in the original TeX source and separately lists the required foundations and semantic obligations.',
 'Progress is not measured by line counts or generated-file counts. Source line numbers are provided only for navigation.','','## Status definitions and two kinds of dependency','']
out += ['- **'+k+'**: '+v+'.' for k,v in result['status_definitions'].items()]
out += ['','Paper dependencies come from the obligation graph of the original proof; they are not all claimed to be formalized. Actual direct Lean dependencies are recorded in',
 '`theorem-map.json` and `lean-dependencies.json`; the latter is extracted from kernel-checked declarations.',
 'Partially covered results marked Checked retain their uncovered scope; importing a file or having a declaration with the same name does not establish closure.',
 'The current formal root import chain contains no items marked Proof contains placeholders; that status is reserved for isolated experimental branches.','',
 '## Item-by-item mapping','','| Paper item / location | Lean declarations | Status and coverage | Paper dependencies |','|---|---|---|---|']
for row in rows:
 label=row['paper_id'];decl='<br>'.join('`'+d+'`' for d in row['lean_declarations']) or '—'
 deps='<br>'.join('`'+d+'`' for d in row['paper_dependencies']) or '—'
 out.append('| `'+label+'` · [source:'+str(row['source_line'])+'](../paper/main-stabilizer2.tex#L'+str(row['source_line'])+')<br>'+row['title'].replace('|','\\|')+' | '+decl+' | **'+row['proof_status']+'**<br>'+row['paper_coverage']+' | '+deps+' |')
out += ['','## Partial coverage and gaps that must be retained','']
for row in rows:
 if row['remaining'] and (row['proof_status'] in ['Statement only','Checked'] or row['paper_id'].startswith('semantic:')):
  out.append('- `'+row['paper_id']+'`: '+row['remaining'])
out+=['','See [main-statement.md](main-statement.md) for the semantic review of each part of the main statement, `validation/` for milestone acceptance evidence, and `history/pilot-milestones.md` for historical reports.','']
(DOC/'theorem-map.md').write_text('\n'.join(out))
print(json.dumps({'main_status':result['main_status'],'all_paper_statements_mapped':True,'paper_statements':len(paper_labels)},ensure_ascii=False))
