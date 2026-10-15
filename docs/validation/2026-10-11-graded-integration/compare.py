#!/usr/bin/env python3
"""Recheck frozen proof inputs, three full audits and independent cloud metadata."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PEER = ROOT / 'docs/validation/2026-10-11-graded-verification'
FROZEN = '583897b83f2714c9b1a4d27fb1cfd2fc988ee7e8'
INTEGRATED = '9c6bacadd5fd4231f0e59955e17e565e17b7b56e'

def read(p):
    return json.loads(p.read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

local = read(HERE / 'local/check.json')
execution = read(PEER / 'execution/check.json')
fresh = read(PEER / 'fresh/reproduction.json')
peer = read(PEER / 'comparison.json')
plan = read(HERE / 'acceptance-plan.json')
meta = read(HERE / 'cloud-postflight.json')
mac_compiler = read(HERE / 'mac-compiler.json')
lock = read(ROOT / 'toolchain-lock.json')
assert mac_compiler['compiler_archive_actual_sha256'] == lock['compiler_assets']['Darwin-arm64']['sha256']
assert lock['lean_version'] in mac_compiler['compiler_version'] and lock['lean_commit'] in mac_compiler['compiler_version']
assert local['result'] == execution['result'] == fresh['result'] == peer['result'] == 'pass'
assert local['git_commit'] == INTEGRATED
assert execution['git_commit'] == fresh['git_commit'] == peer['frozen_commit'] == FROZEN
assert all(not x['working_tree_status'] for x in [local, execution, fresh])
assert local['layout']['source_sha256'] == execution['layout']['source_sha256'] == fresh['layout']['source_sha256']
for name, digest in local['layout']['source_sha256'].items():
    assert sha(ROOT / name) == digest, name
    assert hashlib.sha256(subprocess.check_output(['git', 'show', FROZEN+':'+name], cwd=ROOT)).hexdigest() == digest, name
assert fresh['fresh_project_oleans_before_build'] == 0 and fresh['isolated_dependency_cache']
assert plan['independent_semantic_review'] == 'pass_no_blocking_semantic_issue_found'
assert sha(HERE/'independent-review.md') == plan['review_document_sha256']
for section in ['reviewed_files_sha256', 'preserved_source_files']:
    for name, digest in plan[section].items():
        assert sha(ROOT / name) == digest, name
preserved = read(PEER/'source-preservation.json')
for name, digest in preserved['preserved_sha256'].items():
    assert sha(ROOT/name) == digest, name
assert meta['frozen_commit'] == FROZEN
assert meta['compiler_archive_actual_sha256'] == fresh['compiler_archive_sha256']
assert meta['compiler_archive_actual_sha256'] == lock['compiler_assets']['Linux-x86_64']['sha256']
assert lock['lean_version'] in meta['compiler_version'] and lock['lean_commit'] in meta['compiler_version']
assert not meta['packages_directory_is_symlink'] and not meta['cache_directory_is_symlink']
manifest = read(ROOT/'lake-manifest.json')
assert {p['name']:p['actual_rev'] for p in meta['packages']} == {p['name']:p['rev'] for p in manifest['packages']}
for pkg in meta['packages']:
    assert pkg['actual_rev'] == pkg['expected_rev'] and not pkg['tracked_status']
    assert not pkg['directory_is_symlink'] and not pkg['git_objects_alternates_present']
    assert not pkg['tracked_olean_files']
for name, digest in meta['evidence_sha256'].items():
    assert sha(PEER/name) == digest, name
logs = [HERE/'local/axioms.log', PEER/'execution/axioms.log', PEER/'fresh/axioms.log']
assert logs[0].read_bytes() == logs[1].read_bytes() == logs[2].read_bytes(), 'Complete audit logs differ'
log = logs[0].read_text()
assert 'error:' not in log and 'sorryAx' not in log
summary = re.findall(r'AUDIT_OK .*: (\d+) theorem declarations; (\d+) total declarations', log)
assert len(summary) == 1
links = [line.split('DEPENDENCY_OK ',1)[1] for line in log.splitlines() if 'DEPENDENCY_OK ' in line]
assert len(links) == 283
for a,b in read(ROOT/'docs/graded-audit-links.json'):
    assert a+' -> '+b in links
for record in [local, execution, fresh]:
    assert record['main_status'] == 'statement_only' and record['main_theorem_complete'] is False
for folder in [HERE/'local', PEER/'execution', PEER/'fresh']:
    assert 'MAIN_RELEASE_BLOCKED' in (folder/'main-release-gate.log').read_text()

rows = [json.loads(line.split('DEPENDENCY_JSON ',1)[1]) for line in log.splitlines() if 'DEPENDENCY_JSON ' in line]
graph = {row['declaration']:row['direct_project_dependencies'] for row in rows}
assert len(graph) == int(summary[0][1])
root = 'StabilizerLearning.fixedConstraint_uniform_converse'
targets = [b for a,b in read(ROOT/'docs/graded-audit-links.json') if a == root]
paths = {root:[root]}
queue = [root]
for node in queue:
    for dep in graph.get(node,[]):
        if dep not in paths:
            paths[dep] = paths[node]+[dep]
            queue.append(dep)
assert all(target in paths for target in targets)
(HERE/'converse-closure.json').write_text(json.dumps({
    'root':root,'proof_source':FROZEN,'main_is_only_a_definition':True,
    'graph_source':'local/axioms.log','paths':{target:paths[target] for target in targets}
},indent=2)+'\n')
result = {
    'result':'pass', 'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'peer_frozen_commit':FROZEN, 'local_integration_commit':INTEGRATED,
    'frozen_inputs_identical_across_three_runs':True,
    'formal_input_files':len(local['layout']['source_sha256']),
    'mac_project_clean_and_two_cloud_checks_passed':True,
    'fresh_project_oleans_before_build':0, 'fresh_dependencies_and_cache_independent':True,
    'compiler_reused_and_version_archive_pin_checked':True,
    'complete_audit_logs_byte_identical':True,'audit_sha256':sha(logs[0]),
    'received_cloud_evidence_hashes_verified':True,
    'theorem_declarations_audited':int(summary[0][0]),
    'total_declarations_audited':int(summary[0][1]),
    'required_transitive_proof_links':len(links),
    'independent_semantic_review':'no unresolved blocker',
    'original_public_definitions_and_paper_unchanged':True,
    'axiom_allowlist':['propext','Classical.choice','Quot.sound'],
    'closed_scope':'Original compatible-list Bayes reduction, graded comparison and full original converse component, including all four uniform limits to zero.',
    'main_theorem_complete':False,'main_release':'correctly rejected: statement_only',
    'mac_steps':local['steps'],'cloud_steps':fresh['steps'],
    'fresh_cloud_total_seconds':fresh['total_seconds'],
    'remaining_scope':'Unrestricted direct, all four uniform limits to one, copy-rate identities and original Main; separately tracked exact Gaussian shells/refined-verification/covariance interfaces.'
}
(HERE/'comparison.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['result','peer_frozen_commit','theorem_declarations_audited','total_declarations_audited','required_transitive_proof_links']}))
