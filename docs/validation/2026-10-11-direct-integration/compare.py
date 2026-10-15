#!/usr/bin/env python3
"""Accept only identical frozen sources, two complete audits and strict Main release."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
FROZEN='6d17da20d7a7625333ecf87d23824f031a01a6ae'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
local=read(HERE/'local/check.json'); fresh=read(HERE/'fresh/reproduction.json')
meta=read(HERE/'cloud-postflight.json'); mac=read(HERE/'mac-compiler.json')
lock=read(ROOT/'toolchain-lock.json'); plan=read(HERE/'acceptance-plan.json')
assert local['result']==fresh['result']=='pass'
for record in [local,fresh]:
 assert record['git_commit']==FROZEN and not record['working_tree_status']
 assert record['main_theorem_complete'] and record['main_status']=='dependencies_closed'
 assert record['scope']=='complete_original_main_and_all_project_declarations'
assert local['layout']['source_sha256']==fresh['layout']['source_sha256']
for name,digest in local['layout']['source_sha256'].items():
 assert sha(ROOT/name)==digest,name
 assert hashlib.sha256(subprocess.check_output(['git','show',FROZEN+':'+name],cwd=ROOT)).hexdigest()==digest,name
for name,digest in fresh['project_source_sha256'].items():assert sha(ROOT/name)==digest,name
assert fresh['fresh_project_oleans_before_build']==0 and fresh['isolated_dependency_cache']
assert read(HERE/'local/clean-start.json')['project_oleans_before_build']==0
assert plan['independent_semantic_review']=='pass_no_blocking_semantic_issue_found'
for name,digest in plan['review_documents_sha256'].items():assert sha(ROOT/name)==digest,name
preserved=read(HERE/'source-preservation.json')
for row in preserved['unchanged_files']:assert sha(ROOT/row['file'])==row['sha256']
assert preserved['main_target_definition_unchanged']
baseline=preserved['baseline']
old_math=subprocess.check_output(['git','ls-tree','-r','--name-only',baseline,'StabilizerLearning'],cwd=ROOT,text=True).splitlines()
changed=[]
for name in old_math:
 if name.endswith('.lean') and subprocess.check_output(['git','show',baseline+':'+name],cwd=ROOT)!=(ROOT/name).read_bytes():changed.append(name)
assert sorted(changed)==['StabilizerLearning/Main.lean','StabilizerLearning/Verified.lean']
review_binding=read(ROOT/'docs/direct-main-semantic-review-source.json')
assert review_binding['reviewed_commit']==FROZEN
for name,digest in review_binding['source_sha256'].items():assert sha(ROOT/name)==digest,name
pattern=r'def FixedWNoCopyRateDiscount : Prop :=\n  ∀ \(p : ℕ\) \(hp : Nat.Prime p\),\n    @FixedConstraints.NoCopyRateDiscountForPrime p ⟨hp⟩'
text=re.search(pattern,(ROOT/'StabilizerLearning/Main.lean').read_text()).group()
assert hashlib.sha256(text.encode()).hexdigest()==preserved['main_target_definition_sha256']
for entry,platform in [(mac,'Darwin-arm64'),(meta,'Linux-x86_64')]:
 assert entry['compiler_archive_actual_sha256']==lock['compiler_assets'][platform]['sha256']
 assert lock['lean_version'] in entry['compiler_version'] and lock['lean_commit'] in entry['compiler_version']
assert meta['compiler_archive_actual_sha256']==fresh['compiler_archive_sha256']
assert meta['frozen_commit']==FROZEN
assert not meta['packages_directory_is_symlink'] and not meta['cache_directory_is_symlink']
manifest=read(ROOT/'lake-manifest.json')
assert {x['name']:x['actual_rev'] for x in meta['packages']}=={x['name']:x['rev'] for x in manifest['packages']}
for x in meta['packages']:
 assert x['actual_rev']==x['expected_rev'] and not x['tracked_status']
 assert not x['directory_is_symlink'] and not x['git_objects_alternates_present'] and not x['tracked_olean_files']
for name,digest in meta['evidence_sha256'].items():assert sha(HERE/'fresh'/name)==digest,name
peer=ROOT/'docs/validation/2026-10-11-pgm'
pc=read(peer/'comparison.json');pi=read(peer/'peer-interface-preservation.json')
assert pc['result']=='pass' and pc['frozen_commit']=='a1f4d122949298a9f8dd465dd16f5680287cb275'
assert pi['peer_unified_math_freeze']==FROZEN
assert (peer/'execution/axioms.log').read_bytes()==(peer/'fresh/axioms.log').read_bytes()
assert sha(peer/'execution/axioms.log')==pc['audit_sha256']
for name,digest in pi['unchanged_files_sha256'].items():assert sha(ROOT/name)==digest,name
logs=[HERE/'local/axioms.log',HERE/'fresh/logs/axioms.log']
assert logs[0].read_bytes()==logs[1].read_bytes(),'Complete audits differ'
log=logs[0].read_text()
assert 'error:' not in log and 'sorryAx' not in log
assert 'MAIN_STATUS dependencies_closed: exact original target theorem is present' in log
summary=re.findall(r'AUDIT_OK .*: (\d+) theorem declarations; (\d+) total declarations',log)
assert len(summary)==1
for folder in [HERE/'local',HERE/'fresh/logs']:
 release=(folder/'main-release-gate.log').read_text()
 assert 'MAIN_RELEASE_OK StabilizerLearning.fixedW_noCopyRateDiscount: [propext, Classical.choice, Quot.sound]' in release
links=[line.split('DEPENDENCY_OK ',1)[1] for line in log.splitlines() if 'DEPENDENCY_OK ' in line]
rows=[json.loads(line.split('DEPENDENCY_JSON ',1)[1]) for line in log.splitlines() if 'DEPENDENCY_JSON ' in line]
graph={r['declaration']:r['direct_project_dependencies'] for r in rows}
assert len(graph)==int(summary[0][1])
main='StabilizerLearning.fixedW_noCopyRateDiscount'
assert main in graph
paths={main:[main]};queue=[main]
for node in queue:
 for dep in graph.get(node,[]):
  if dep not in paths: paths[dep]=paths[node]+[dep];queue.append(dep)
targets=[l.split(' -> ',1)[1] for l in links if l.startswith(main+' -> ')]
assert len(targets)==20 and all(t in paths for t in targets)
(HERE/'main-closure.json').write_text(json.dumps({'root':main,'exact_target':'StabilizerLearning.FixedWNoCopyRateDiscount',
 'proof_source':FROZEN,'graph_source':'local/axioms.log','paths':{t:paths[t] for t in targets}},indent=2)+'\n')
result={'result':'pass','checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'frozen_commit':FROZEN,'main_theorem_complete':True,'main_exact_original_type_verified':True,
 'frozen_inputs_identical_across_two_runs':True,'formal_input_files':len(local['layout']['source_sha256']),
 'mac_clean_and_linux_fresh_checks_passed':True,'fresh_project_oleans_before_build':0,
 'fresh_dependencies_and_cache_independent':True,'compiler_reused_and_version_archive_pin_checked':True,
 'complete_audit_logs_byte_identical':True,'audit_sha256':sha(logs[0]),
 'received_cloud_evidence_hashes_verified':True,'theorem_declarations_audited':int(summary[0][0]),
 'total_declarations_audited':int(summary[0][1]),'required_transitive_proof_links':len(links),
 'main_checked_transitive_links':len(targets),'peer_pgm_component_acceptance_verified':True,
 'peer_pgm_component_frozen_commit':pc['frozen_commit'],'peer_pgm_audit_sha256':pc['audit_sha256'],'independent_semantic_review':'no unresolved blocker',
 'original_public_definitions_and_paper_unchanged':True,'preexisting_math_files_changed_only':changed,'main_target_definition_unchanged':True,
 'axiom_allowlist':['propext','Classical.choice','Quot.sound'],
 'closed_scope':'Original fixed-W Main, original all-POVM common-J converse, four uniform direct limits under real k-n divergence, exact liminf/sInf rates one, actual PGM normalization, exact shell counts, all-input postprocessing and dimension-only covariance.',
 'mac_steps':local['steps'],'cloud_steps':fresh['steps'],'fresh_cloud_total_seconds':fresh['total_seconds'],
 'remaining_scope':'Paper interfaces beyond the closed Main: PGM optimality/equal success, specified kappa constants, product symmetry wrapper, other separately mapped refined interfaces.'}
(HERE/'comparison.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['result','frozen_commit','main_theorem_complete','theorem_declarations_audited','total_declarations_audited','required_transitive_proof_links']}))
