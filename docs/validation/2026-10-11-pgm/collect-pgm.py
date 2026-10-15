from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess
ROOT=Path('/data/lean/tasks/pgm-integration')
FRESH=Path('/data/lean/StabilizerLearning-clean-20261011-pgm-a1f4d1229492')
STAGE=ROOT/'docs/validation/2026-10-11-pgm'
FROZEN='a1f4d122949298a9f8dd465dd16f5680287cb275'
BASE='87597a5a20d881f12696e3b7bd6946d954c9f6bd'
def sha(b):return hashlib.sha256(b).hexdigest()
def filehash(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
root=json.loads((ROOT/'artifacts/pgm-clean/check.json').read_text())
fresh=json.loads((FRESH/'reproduction.json').read_text())
assert root['result']==fresh['result']=='pass'
assert root['git_commit']==fresh['git_commit']==FROZEN
assert root['working_tree_status']==fresh['working_tree_status']==''
assert root['layout']['source_sha256']==fresh['layout']['source_sha256']
assert fresh['fresh_project_oleans_before_build']==0
assert root['main_status']==fresh['main_status']=='statement_only'
for rel,digest in root['layout']['source_sha256'].items():
 assert filehash(ROOT/rel)==digest,rel
 assert sha(git('show',FROZEN+':'+rel))==digest,rel
for rel,digest in fresh['project_source_sha256'].items():
 assert filehash(ROOT/rel)==digest,rel
aud1=(ROOT/'artifacts/pgm-clean/axioms.log').read_bytes()
aud2=(FRESH/'logs/axioms.log').read_bytes()
assert aud1==aud2,'Full audit logs differ'
log=aud1.decode()
assert 'AUDIT_OK' in log and not re.search(r'error:|sorryAx',log)
counts=re.findall(r'AUDIT_OK.*?: (\d+) theorem declarations; (\d+) total declarations',log)
assert len(counts)==1,counts
links=[l.split('DEPENDENCY_OK ',1)[1] for l in log.splitlines() if 'DEPENDENCY_OK ' in l]
expected=json.loads((ROOT/'docs/pgm-audit-links.json').read_text())
assert all(a+' -> '+b in links for a,b in expected)
basefiles=git('ls-tree','-r','--name-only',BASE).decode().splitlines()
mathfiles=[p for p in basefiles if p=='StabilizerLearning.lean' or (p.startswith('StabilizerLearning/') and p.endswith('.lean'))]
preserved={}
for p in mathfiles:
 if p=='StabilizerLearning/Verified.lean':continue
 b=git('show',BASE+':'+p);assert (ROOT/p).read_bytes()==b,p;preserved[p]=sha(b)
critical=['StabilizerLearning/Main.lean','StabilizerLearning/Quantum/Finite.lean','StabilizerLearning/Quantum/Pauli.lean','StabilizerLearning/Quantum/Stabilizer.lean','StabilizerLearning/FixedConstraints/Task.lean','StabilizerLearning/FixedConstraints/Rates.lean','paper/main-stabilizer2.tex','paper/arXiv-2609.13923v1.tar.gz','lean-toolchain','lakefile.toml','lake-manifest.json','toolchain-lock.json']
for p in critical:
 b=git('show',BASE+':'+p);assert (ROOT/p).read_bytes()==b,p;preserved[p]=sha(b)
manifest=json.loads((ROOT/'lake-manifest.json').read_text())
deps={}
for tag,project in [('execution',ROOT),('fresh',FRESH/'project')]:
 rows=[]
 for pkg in manifest['packages']:
  folder=project/'.lake/packages'/pkg['name']
  actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=folder,text=True).strip()
  assert actual==pkg['rev']
  status=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=folder,text=True)
  assert status=='',(tag,pkg['name'],status)
  no_symlink=folder.resolve()==folder.absolute()
  gitdir=subprocess.check_output(['git','rev-parse','--absolute-git-dir'],cwd=folder,text=True).strip()
  no_alternates=not (Path(gitdir)/'objects/info/alternates').exists()
  if tag=='fresh':assert no_symlink and no_alternates
  rows.append({'name':pkg['name'],'expected_rev':pkg['rev'],'actual_rev':actual,'tracked_status':status,'independent_path_without_symlink':no_symlink,'no_git_alternates':no_alternates})
 deps[tag]=rows
lock=json.loads((ROOT/'toolchain-lock.json').read_text())
asset=lock['compiler_assets']['Linux-x86_64']
archive=ROOT/'.toolchain'/'lean-4.24.0-linux.tar.zst'
actual_compiler_sha=filehash(archive)
assert actual_compiler_sha==asset['sha256']
STAGE.mkdir(parents=True,exist_ok=True)
for tag,folder in [('execution',ROOT/'artifacts/pgm-clean'),('fresh',FRESH/'logs')]:
 d=STAGE/tag;d.mkdir(exist_ok=True)
 for name in ['build.log','axioms.log','main-release-gate.log']:shutil.copy2(folder/name,d/name)
shutil.copy2(ROOT/'artifacts/pgm-clean/check.json',STAGE/'execution/check.json')
shutil.copy2(FRESH/'reproduction.json',STAGE/'fresh/reproduction.json')
shutil.copy2(ROOT/'artifacts/pgm-clean-preflight.json',STAGE/'execution/clean-preflight.json')
for p in (FRESH/'logs').glob('*-fetch.log'):shutil.copy2(p,STAGE/'fresh'/p.name)
shutil.copy2(FRESH/'logs/cache.log',STAGE/'fresh/cache.log')
shutil.copy2(ROOT/'artifacts/pgm-preflight/new-links.log',STAGE/'new-proof-links.log')
for name in ['gram','support','states']:
 folder=Path('/data/lean/tasks/pgm-'+name)/('artifacts/pgm-'+name)
 d=STAGE/'module-checks'/name;d.mkdir(parents=True,exist_ok=True)
 for p in folder.glob('*.log'):shutil.copy2(p,d/p.name)
(STAGE/'source-preservation.json').write_text(json.dumps({'base':BASE,'frozen':FROZEN,'verified_imports_only_exception':True,'preserved_sha256':preserved},indent=2)+'\n')
(STAGE/'dependency-checkouts.json').write_text(json.dumps(deps,indent=2)+'\n')
(STAGE/'compiler-pin.json').write_text(json.dumps({'compiler':fresh['compiler'],'archive':str(archive),'expected_sha256':asset['sha256'],'measured_sha256':actual_compiler_sha,'result':'pass'},indent=2)+'\n')
record={'result':'pass','frozen_commit':FROZEN,'base_commit':BASE,
 'completed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Actual normalized singular-support PGM, exact Gram/Born identity, unconditional statewise row-energy bound, and original stabilizer-state k-copy direct interface',
 'main_theorem_complete':False,'main_release':'correctly_rejected_missing_main_proof',
 'original_source_and_definitions_unchanged':True,'all_prior_mathematical_sources_unchanged_except_imports':True,
 'formal_input_files':len(root['layout']['source_sha256']),
 'fresh_initial_project_oleans':0,'exact_dependency_checkouts_clean':True,
 'fresh_dependencies_no_symlinks_or_git_alternates':True,'compiler_archive_sha256_measured':True,
 'complete_audit_logs_identical':True,'audit_sha256':sha(aud1),
 'all_project_theorems':int(counts[0][0]),'all_project_declarations':int(counts[0][1]),
 'actual_proof_links':len(links),'new_actual_proof_links':len(expected),
 'axiom_allowlist':['propext','Classical.choice','Quot.sound'],
 'all_project_and_private_declarations_audited':True,
 'execution_steps':root['steps'],'fresh_steps':fresh['steps'],'fresh_total_seconds':fresh['total_seconds'],
 'isolation':'Two Linux project rebuilds on the same host. Execution clone reused read-only pinned dependency cache; fresh project has genuinely independent exact dependency checkouts and official cache, without symlinks/alternates. Existing pinned compiler reused with measured archive checksum. No new OS or Mac/Linux comparison claimed.',
 'remaining':'Sharp enough overlap counting and all-state fixed-W postprocessing, four uniform one-limits, exact copy-rate identities and complete Main integration remain external to this PGM package; transitive PGM optimality is separately unproved.',
 'progress_policy':'Counts and runtime show validation coverage and resource cost, not proof-completion percentages or calendar-effort estimates.'}
(STAGE/'comparison.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['execution_steps','fresh_steps']},ensure_ascii=False,indent=2))
