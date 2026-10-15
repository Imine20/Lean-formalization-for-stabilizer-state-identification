#!/usr/bin/env python3
"""Fresh-directory build: exact Git pins, independent dependency cache, no project oleans.
Reuses a version-checked Lean installation. On a new machine install the lean-toolchain
release (normally with elan), then run this script with lake/lean on PATH.
"""
from pathlib import Path
import argparse, concurrent.futures, datetime, hashlib, json, os, platform, re, shutil, subprocess, time
from check_layout import check

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--require-main-proof', action='store_true')
parser.add_argument('--dest', type=Path, required=True, help='New directory; must not exist')
args = parser.parse_args()
layout = check()
dest = args.dest.resolve()
if dest.exists():
    raise SystemExit('Refusing existing destination: use a fresh directory')
dest.mkdir(parents=True)
project = dest / 'project'
project.mkdir()
source_files = [ROOT / name for name in ['lean-toolchain','lakefile.toml','lake-manifest.json',
    'StabilizerLearning.lean','Audit.lean','scripts/ReleaseAudit.lean']]
source_files += sorted((ROOT/'StabilizerLearning').rglob('*.lean'))
for source in source_files:
    target = project / source.relative_to(ROOT)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
logs = dest / 'logs'
logs.mkdir()
env = os.environ.copy()
lock = json.loads((ROOT / 'toolchain-lock.json').read_text())
host_key = platform.system() + '-' + platform.machine()
asset = lock.get('compiler_assets', {}).get(host_key)
compiler = ROOT / '.toolchain' / (asset['directory'] if asset else 'not-installed') / 'bin'
if (compiler / 'lake').exists():
    env['PATH'] = str(compiler) + os.pathsep + env['PATH']
for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LAKE_PACKAGES_DIR'):
    env.pop(key, None)
env.update(LC_ALL='C', MATHLIB_NO_CACHE_ON_UPDATE='1', MATHLIB_CACHE_DIR=str(dest / 'mathlib-cache'))
version = subprocess.check_output(['lean', '--version'], env=env, text=True).strip()
if f'version {lock["lean_version"]},' not in version or lock['lean_commit'] not in version:
    raise SystemExit('Unexpected compiler: ' + version)
manifest_path = project / 'lake-manifest.json'
manifest_bytes = manifest_path.read_bytes()
manifest = json.loads(manifest_bytes)
assert all(re.fullmatch(r'[0-9a-f]{40}', pkg['rev']) for pkg in manifest['packages'])
assert next(pkg['rev'] for pkg in manifest['packages'] if pkg['name'] == 'mathlib') == lock['mathlib_commit']
metrics = {'scope': 'main_statement_and_closed_auxiliary_proofs', 'main_theorem_complete': False, 'result': 'failed',
           'layout':layout,
           'git_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
           'working_tree_status':subprocess.check_output(['git','status','--short'],cwd=ROOT,text=True),
           'host_isolation': 'fresh directory, independent dependencies/cache; existing host and pinned compiler reused',
           'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'compiler': version, 'platform':host_key,
           'compiler_archive_sha256':asset['sha256'] if asset else None,
           'fresh_project_oleans_before_build': len(list(project.rglob('*.olean'))),
           'isolated_dependency_cache': True, 'steps': []}
start = time.monotonic()

def run(command, cwd, log):
    tick = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT)
    step = {'command': command, 'seconds': round(time.monotonic()-tick, 3), 'exit_code': result.returncode}
    metrics['steps'].append(step)
    if result.returncode:
        print(log.read_text()[-15000:])
        raise RuntimeError(f'Failed ({result.returncode}): {command}; log: {log}')
    return step

def fetch(pkg):
    folder = project / '.lake/packages' / pkg['name']
    folder.mkdir(parents=True)
    log = logs / (pkg['name'] + '-fetch.log')
    commands = [['git','init','--quiet'], ['git','remote','add','origin',pkg['url']],
                ['git','fetch','--depth','1','origin',pkg['rev']],
                ['git','checkout','--detach','FETCH_HEAD']]
    tick = time.monotonic()
    with log.open('w') as stream:
        for command in commands:
            subprocess.run(command,cwd=folder,env=env,stdout=stream,stderr=subprocess.STDOUT,check=True)
        tag = pkg.get('inputRev', '')
        if re.fullmatch(r'v[0-9]+(?:\.[0-9]+)+(?:[-.][A-Za-z0-9.]+)?', tag):
            subprocess.run(['git','fetch','--depth','1','origin',f'refs/tags/{tag}:refs/tags/{tag}'],
                           cwd=folder,env=env,stdout=stream,stderr=subprocess.STDOUT,check=True)
            tag_rev = subprocess.check_output(['git','rev-parse',tag+'^{commit}'],cwd=folder,env=env,text=True).strip()
            if tag_rev != pkg['rev']:
                raise RuntimeError(f'Release tag mismatch for {pkg["name"]}')
    actual = subprocess.check_output(['git','rev-parse','HEAD'],cwd=folder,env=env,text=True).strip()
    if actual != pkg['rev']:
        raise RuntimeError(f'Commit mismatch: {pkg["name"]}')
    return {'name':pkg['name'],'rev':actual,'seconds':round(time.monotonic()-tick,3)}

try:
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        metrics['packages'] = list(pool.map(fetch, manifest['packages']))
    print('Exact dependency commits fetched.', flush=True)
    imports = (ROOT / 'scripts/cache-imports.txt').read_text().split()
    run(['lake','exe','cache','get',*imports], project, logs/'cache.log')
    print('Independent official mathlib cache populated.', flush=True)
    run(['lake','build'], project, logs/'build.log')
    run(['lake','env','lean','Audit.lean'], project, logs/'axioms.log')
    release_log = logs/'main-release-gate.log'
    with release_log.open('w') as stream:
        release = subprocess.run(['lake','env','lean','scripts/ReleaseAudit.lean'],cwd=project,env=env,
            stdout=stream,stderr=subprocess.STDOUT)
    release_text = release_log.read_text()
    if release.returncode == 0 and 'MAIN_RELEASE_OK' in release_text:
        metrics['main_theorem_complete'] = True
        metrics['main_status'] = 'dependencies_closed'
        metrics['scope'] = 'complete_original_main_and_all_project_declarations'
    elif release.returncode != 0 and 'MAIN_RELEASE_BLOCKED' in release_text:
        metrics['main_status'] = 'statement_only'
        metrics['release_gate'] = 'correctly_rejected_missing_main_proof'
        if args.require_main_proof:
            raise RuntimeError('Release rejected: main theorem has no proof.')
    else:
        raise RuntimeError('Unexpected main release gate result: '+release_text)
    assert manifest_path.read_bytes() == manifest_bytes, 'Manifest changed during build'
    metrics['manifest_sha256'] = hashlib.sha256(manifest_bytes).hexdigest()
    metrics['project_source_sha256'] = {str(p.relative_to(project)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(project.rglob('*')) if p.is_file() and '.lake' not in p.parts}
    assert check()['source_sha256'] == layout['source_sha256'], 'Inputs changed during reproduction'
    metrics['result']='pass'
finally:
    metrics['total_seconds']=round(time.monotonic()-start,3)
    metrics['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (dest/'reproduction.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
