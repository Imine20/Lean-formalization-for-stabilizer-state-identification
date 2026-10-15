#!/usr/bin/env python3
"""Compare this milestone's immutable local and independent cloud evidence."""
from pathlib import Path
import datetime, hashlib, json, re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FROZEN = 'ce043d6c1de0cda69dc3ed6163aedf23717833a5'
local = json.loads((HERE/'local/check.json').read_text())
cloud = json.loads((HERE/'cloud/reproduction.json').read_text())
review = json.loads((HERE/'semantic-review.json').read_text())
assert local['result'] == cloud['result'] == 'pass'
assert local['git_commit'] == cloud['git_commit'] == FROZEN
assert not local['working_tree_status'] and not cloud['working_tree_status']
assert local['layout']['source_sha256'] == cloud['layout']['source_sha256']
for name, digest in local['layout']['source_sha256'].items():
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
assert cloud['fresh_project_oleans_before_build'] == 0
assert cloud['isolated_dependency_cache'] is True
isolation = json.loads((HERE/'cloud/isolation.json').read_text())
preflight = json.loads((HERE/'cloud/preflight.json').read_text())
received = json.loads((HERE/'cloud/evidence-sha256.json').read_text())
for name, digest in received.items():
    assert hashlib.sha256((HERE/'cloud'/Path(name).name).read_bytes()).hexdigest() == digest, name
assert isolation['source_commit'] == FROZEN and not isolation['source_worktree_status']
assert not isolation['packages_directory_is_symlink'] and not isolation['mathlib_cache_is_symlink']
for pkg in isolation['packages']:
    assert pkg['expected_rev'] == pkg['actual_rev'] and not pkg['tracked_status']
    assert not pkg['directory_is_symlink'] and not pkg['git_objects_alternates_present']
    assert not pkg['tracked_olean_files']
assert {p['name']:p['actual_rev'] for p in isolation['packages']} == {p['name']:p['rev'] for p in cloud['packages']}
assert preflight['compiler_archive_actual_sha256'] == cloud['compiler_archive_sha256']
assert local['main_status'] == cloud['main_status'] == 'statement_only'
assert local['main_theorem_complete'] is cloud['main_theorem_complete'] is False
for section in ('reviewed_files_sha256', 'preserved_source_files'):
    for name, digest in review[section].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
manifest = json.loads((ROOT/'lake-manifest.json').read_text())
assert {x['name']:x['rev'] for x in manifest['packages']} == {
    x['name']:x['rev'] for x in cloud['packages']}
la = (HERE/'local/axioms.log').read_text()
ca = (HERE/'cloud/axioms.log').read_text()
assert la == ca, 'Cross-platform recursive axiom/dependency logs differ'
assert 'error:' not in la
summary = re.search(r'AUDIT_OK .*: (\d+) theorem declarations; (\d+) total declarations', la)
assert summary
links = [l.split('DEPENDENCY_OK ',1)[1] for l in la.splitlines() if 'DEPENDENCY_OK ' in l]
rows = [json.loads(l.split('DEPENDENCY_JSON ',1)[1]) for l in la.splitlines() if 'DEPENDENCY_JSON ' in l]
assert rows and len(links) == 167
for side in ('local','cloud'):
    assert 'MAIN_RELEASE_BLOCKED' in (HERE/side/'main-release-gate.log').read_text()
result = {
    'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'result':'pass', 'frozen_commit':FROZEN,
    'local_and_cloud_source_hashes_identical':True,
    'independent_dependency_checkout_and_cache':True,
    'received_cloud_evidence_hashes_verified':True,
    'exact_clean_dependency_checkouts_without_links_or_alternates':True,
    'fresh_project_oleans_before_build':0,
    'compiler_reused_but_pin_checked':True,
    'kernel_dependency_graphs_identical':True,
    'recursive_axiom_results_identical':True,
    'theorem_declarations_audited':int(summary[1]),
    'total_declarations_audited':int(summary[2]),
    'required_transitive_proof_links':len(links),
    'reviewed_source_hashes_match':True,
    'paper_main_and_public_definitions_unchanged':True,
    'axiom_allowlist':['propext','Classical.choice','Quot.sound'],
    'main_theorem_complete':False,
    'main_release':'correctly rejected: statement_only',
    'local_steps':local['steps'],
    'cloud_total_seconds':cloud['total_seconds'],
    'cloud_steps':cloud['steps'],
    'cloud_directory':'/data/lean/StabilizerLearning-clean-20261011-physical-ce043d6c1de0',
    'comparison_script':'docs/validation/2026-10-11-physical-coordinate/compare.py'}
(HERE/'comparison.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['result','frozen_commit','theorem_declarations_audited',
 'total_declarations_audited','required_transitive_proof_links','cloud_total_seconds']},ensure_ascii=False))
