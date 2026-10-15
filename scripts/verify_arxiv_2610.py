#!/usr/bin/env python3
"""Public, immutable-commit reproduction of the nested arXiv:2610.00266 project.

The frozen research scripts are executed unchanged. All dependency repositories
come from their public manifest URLs. Only dependency caches may be downloaded;
the project always starts with zero compiled Lean modules and runs every gate.
"""
from pathlib import Path, PurePosixPath
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[1]
PROJECT_PREFIX = Path('proofs/arxiv-2610.00266')
SCRIPT_PATH = 'scripts/verify_arxiv_2610.py'
PUBLIC_PACKAGES = {
    'mathlib': 'https://github.com/leanprover-community/mathlib4.git',
    'plausible': 'https://github.com/leanprover-community/plausible',
    'LeanSearchClient': 'https://github.com/leanprover-community/LeanSearchClient',
    'importGraph': 'https://github.com/leanprover-community/import-graph',
    'proofwidgets': 'https://github.com/leanprover-community/ProofWidgets4',
    'aesop': 'https://github.com/leanprover-community/aesop',
    'Qq': 'https://github.com/leanprover-community/quote4',
    'batteries': 'https://github.com/leanprover-community/batteries',
    'Cli': 'https://github.com/leanprover/lean4-cli',
}
GATE_COMMANDS = {
    'build': ['bash', 'scripts/lake.sh', 'build'],
    'axioms': ['bash', 'scripts/lake.sh', 'env', 'lean', 'scripts/ProjectAudit.lean'],
    'pilot_types': ['bash', 'scripts/lake.sh', 'env', 'lean', 'scripts/PilotExpectedTypes.lean'],
    'release': ['bash', 'scripts/lake.sh', 'env', 'lean', 'scripts/ReleaseAudit.lean'],
}
V3_DIRECTORY = Path('docs/validation/2026-10-12/evidence-tools-v3')
V3_HASHES = {
    'audit_call_inventory.py': '1d5a8489c7299ddd1d00024bebfe20ec7d19c74c8a0b0bc364b37e6f09541120',
    'verify_joint_gate_strict.py': '9baafd93a372062b0dda8540c564a03ed0bd4d2a47de835bff9930fc7d23ce8b',
}
REQUIRED_RELEASE_BODIES = {
    'ExactCriticalCurve.finiteSpectrum', 'ExactCriticalCurve.criticalCurve',
    'ExactCriticalCurve.criticalCurveTails',
    'ExactCriticalCurve.Asymptotics.paperStochasticGroup_order',
    'ExactCriticalCurve.Asymptotics.criticalSpectralMass',
    'ExactCriticalCurve.Asymptotics.physicalExceptionalAmplitude_le_inverse_dimension',
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def clean_environment(destination, original=None):
    env = dict(os.environ if original is None else original)
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_PACKAGES_DIR',
                'LAKE_HOME', 'ELAN_TOOLCHAIN', 'LAKE_OVERRIDE_LEAN_TOOLCHAIN',
                'GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_OBJECT_DIRECTORY',
                'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_CONFIG_COUNT', 'GIT_CONFIG_PARAMETERS'):
        env.pop(key, None)
    # Public manifest URLs must not be redirected through author-specific Git
    # configuration. Network proxy environment variables remain available.
    env.update(LC_ALL='C', GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1',
               GIT_OPTIONAL_LOCKS='0', MATHLIB_NO_CACHE_ON_UPDATE='1',
               MATHLIB_CACHE_DIR=str(destination / 'mathlib-cache'),
               XDG_CACHE_HOME=str(destination / 'xdg-cache'), PYTHONDONTWRITEBYTECODE='1')
    env.setdefault('LEAN_NUM_THREADS', '2')
    return env


def validate_manifest(manifest, lock):
    packages = manifest['packages']
    names = [p['name'] for p in packages]
    require(len(names) == len(set(names)) and set(names) == set(PUBLIC_PACKAGES),
            'Expected the nine distinct reviewed public dependencies')
    require(manifest.get('packagesDir') == '.lake/packages', 'Unexpected packages directory')
    for package in packages:
        require(package['url'] == PUBLIC_PACKAGES[package['name']],
                'Dependency URL differs from the reviewed public source: ' + package['name'])
        require(package.get('type') == 'git' and not package.get('subDir'),
                'Only root Git dependencies are supported')
        require(re.fullmatch('[0-9a-f]{40}', package['rev']) is not None,
                'Dependency is not pinned to a full commit: ' + package['name'])
    require(next(p['rev'] for p in packages if p['name'] == 'mathlib') == lock['mathlib_commit'],
            'Mathlib manifest and toolchain lock disagree')
    return packages


def restore_display_assets(project, packages):
    lock = read_json(project / 'locks/proofwidgets-js.json')
    require(lock['proofwidgets_commit'] == next(p['rev'] for p in packages if p['name'] == 'proofwidgets'),
            'ProofWidgets asset lock and dependency revision disagree')
    archive = project / 'vendor/proofwidgets-js.tar.gz'
    require(sha(archive) == lock['archive_sha256'], 'ProofWidgets archive hash mismatch')
    require((project / 'vendor/ProofWidgets-LICENSE').is_file(), 'ProofWidgets license missing')
    for name in lock['files']:
        require(PurePosixPath(name).name == name and name not in {'.', '..'},
                'Invalid display asset filename')
    allowed = {'js/' + name for name in lock['files']}
    target = project / '.lake/packages/proofwidgets/.lake/build'
    # Validate the complete archive before writing any member.
    contents = {}
    with tarfile.open(archive, 'r:gz') as stream:
        members = stream.getmembers()
        require(len(members) == len(allowed), 'Missing or duplicate ProofWidgets archive member')
        for member in members:
            require(member.name in allowed and member.isfile() and member.name not in contents,
                    'Unexpected ProofWidgets archive member: ' + member.name)
            data = stream.extractfile(member).read()
            require(hashlib.sha256(data).hexdigest() == lock['files'][PurePosixPath(member.name).name],
                    'ProofWidgets display asset hash mismatch: ' + member.name)
            contents[member.name] = data
    require(set(contents) == allowed, 'Incomplete ProofWidgets display assets')
    for name, data in contents.items():
        output = target / name
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(data)
    return lock


def project_oleans(project):
    return sorted(str(p.relative_to(project)) for p in (project / '.lake/build').rglob('*.olean'))


def verify_acceptance(acceptance, project):
    result = read_json(acceptance / 'result.json')
    require(result.get('status') == 'pass' and result.get('scope') == 'main_release'
            and result.get('paper_main_complete') is True
            and result.get('inputs_unchanged_through_audit') is True,
            'The complete unchanged-input release gate did not pass')
    commands = result['commands']
    require([c['label'] for c in commands] == ['compiler', *GATE_COMMANDS],
            'Release command inventory changed or a required audit was skipped')
    lock = read_json(project / 'locks/toolchain.json')
    asset = lock['compiler_assets'][platform.system() + '-' + platform.machine()]
    expected = {'compiler': [str(project / '.toolchain' / asset['directory'] / 'bin/lean'), '--version'],
                **GATE_COMMANDS}
    for command in commands:
        label = command['label']
        require(command['command'] == expected[label] and command['exit_code'] == 0,
                'Required command did not execute successfully: ' + label)
        require(command['log'] == label + '.log', 'Unexpected acceptance log path')
        require(sha(acceptance / command['log']) == command['log_sha256'],
                'Acceptance log hash mismatch: ' + label)
    require('PROJECT_AUDIT_OK' in (acceptance / 'axioms.log').read_text(),
            'Whole-project audit completion marker missing')
    for label in ('pilot_types', 'release'):
        log = (acceptance / (label + '.log')).read_text()
        require('KERNEL_EXPECTED_TYPE_OK constant ' in log and 'KERNEL_EXPECTED_TYPE_OK body ' in log,
                'Independent constant/original-body check evidence missing: ' + label)
    return result


def load_v3_helpers(project):
    """Import reviewed, byte-pinned pure helpers, never the historical runner."""
    directory = project / V3_DIRECTORY
    for name, digest in V3_HASHES.items():
        require(sha(directory / name) == digest, 'Preserved V3 helper changed: ' + name)
    previous = sys.modules.get('audit_call_inventory')
    try:
        spec = importlib.util.spec_from_file_location('audit_call_inventory', directory / 'audit_call_inventory.py')
        inventory = importlib.util.module_from_spec(spec)
        sys.modules['audit_call_inventory'] = inventory
        spec.loader.exec_module(inventory)
        spec = importlib.util.spec_from_file_location('_publication_v3_verifier', directory / 'verify_joint_gate_strict.py')
        verifier = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(verifier)
        return verifier
    finally:
        if previous is None:
            sys.modules.pop('audit_call_inventory', None)
        else:
            sys.modules['audit_call_inventory'] = previous


def verify_source_and_coverage(result, acceptance, project, immutable_blob):
    """Bind complete source inventory and source-derived audit calls to execution."""
    verifier = load_v3_helpers(project)
    formal_paths = {p.relative_to(project).as_posix()
                    for p in (project / 'ExactCriticalCurve').rglob('*.lean')}
    formal_paths.add('ExactCriticalCurve.lean')
    scripts = {p.relative_to(project).as_posix() for p in (project / 'scripts').iterdir()
               if p.is_file() and p.suffix in {'.lean', '.py', '.sh'}}
    mandatory = formal_paths | scripts | {
        'docs/pgm-provenance.json', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'locks/toolchain.json', 'locks/proofwidgets-js.json', 'vendor/proofwidgets-js.tar.gz',
        'paper/source.json'}
    layout = result['layout']
    require(set(layout['reachable_formal_modules']) == formal_paths, 'Formal module inventory mismatch')
    require(set(layout['formal_source_sha256']) == mandatory, 'Frozen source/audit inventory mismatch')
    known = set()
    for name, digest in layout['formal_source_sha256'].items():
        blob = immutable_blob(name)
        require(sha(project / name) == digest and hashlib.sha256(blob).hexdigest() == digest,
                'Acceptance input differs from the immutable tree: ' + name)
        if name in formal_paths:
            known.update(verifier.declarations(blob.decode()))
    for name, digest in V3_HASHES.items():
        require(hashlib.sha256(immutable_blob((V3_DIRECTORY / name).as_posix())).hexdigest() == digest,
                'V3 helper differs from the immutable tree: ' + name)
    provenance = read_json(project / 'paper/source.json')
    require(sha(project / 'paper/main.tex') == provenance['main_tex_sha256']
            and hashlib.sha256(immutable_blob('paper/main.tex')).hexdigest() == provenance['main_tex_sha256'],
            'Paper source differs from its immutable provenance')
    require(sha(project / 'paper/arXiv-2610.00266v1.tar.gz') == provenance['archive_sha256'],
            'Paper archive differs from its provenance')
    require(result['toolchain_lock'] == read_json(project / 'locks/toolchain.json'),
            'Recorded compiler lock differs from immutable input')
    axiom_log = (acceptance / 'axioms.log').read_text()
    union = re.findall(r'^PROJECT_AXIOMS_UNION \[(.*?)\]$', axiom_log, re.M)
    require(len(union) == 1 and {x.strip() for x in union[0].split(',')} == verifier.ALLOWED,
            'Unexpected whole-project axiom union')
    markers = re.findall(r'^PROJECT_AUDIT_OK declarations=(\d+) theorems=(\d+)$', axiom_log, re.M)
    require(len(markers) == 1, 'Missing or repeated whole-project completion marker')
    rows = [json.loads(row)['declaration']
            for row in re.findall(r'^DECLARATION_AUDIT (.*)$', axiom_log, re.M)]
    require(len(rows) == len(set(rows)) == int(markers[0][0]) and len(rows) > 0,
            'Whole-project declaration inventory mismatch')
    formal = set(rows)
    stats = {}
    for label, filename in [('pilot_types', 'PilotExpectedTypes.lean'), ('release', 'ReleaseAudit.lean')]:
        source = immutable_blob('scripts/' + filename).decode()
        log = (acceptance / (label + '.log')).read_text()
        stats[label] = verifier.audit_markers(log, source, known, formal, label == 'release')
        expected_exceptions = {name: 1 for name in verifier.STRUCTURES} if label == 'pilot_types' else {}
        require(stats[label]['constant_only_structure_checks'] == expected_exceptions,
                'Only the four original Pilot structure checks may omit proof bodies')
        if label == 'release':
            actual_bodies = set(re.findall(r'^KERNEL_EXPECTED_TYPE_OK body (\S+)$', log, re.M))
            require(REQUIRED_RELEASE_BODIES <= actual_bodies & formal,
                    'A required paper or correspondence-closure original body is absent')
    return {'source_derived_audit_inventory': stats, 'allowed_axioms_union': sorted(verifier.ALLOWED),
            'project_declarations': len(rows), 'project_theorem_kind_declarations': int(markers[0][1]),
            'required_release_original_bodies': sorted(REQUIRED_RELEASE_BODIES),
            'v3_helper_sha256': V3_HASHES,
            'limitations': ['Private audit names are checked by source-derived suffix, kind and multiplicity; '
                           'compiler-generated private prefixes are not independently predicted.',
                           'Recorded semantic reviews are AI reviews; mechanical acceptance does not establish independent human review.']}


class Reproduction:
    def __init__(self, destination, environment, record):
        self.destination = destination
        self.env = environment
        self.record = record
        self.logs = destination / 'logs'
        self.logs.mkdir()

    def save(self):
        (self.destination / 'reproduction.json').write_text(json.dumps(self.record, indent=2) + '\n')

    def run(self, label, command, cwd):
        logfile = self.logs / (label + '.log')
        started = time.monotonic()
        with logfile.open('x') as output:
            completed = subprocess.run(command, cwd=cwd, env=self.env,
                                       stdout=output, stderr=subprocess.STDOUT)
        self.record['commands'].append({'label': label, 'command': [str(x) for x in command],
            'cwd': str(cwd), 'exit_code': completed.returncode,
            'seconds': time.monotonic() - started, 'log': str(logfile.relative_to(self.destination)),
            'log_sha256': sha(logfile)})
        self.save()
        print(label, completed.returncode, flush=True)
        require(completed.returncode == 0, label + ' failed; see ' + str(logfile))
        return logfile.read_text()

    def git(self, cwd, *args):
        return subprocess.check_output(['git', *args], cwd=cwd, env=self.env).decode().strip()


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument('--dest', required=True, type=Path, help='New directory outside this repository')
    result.add_argument('--revision', default='HEAD', help='Immutable repository revision (default: HEAD)')
    result.add_argument('--dependency-mode', choices=('official-cache', 'source'), default='official-cache',
                        help='Explicit official Mathlib cache, or compile required dependencies from source')
    result.add_argument('--compiler-archive', type=Path,
                        help='Optional existing compiler archive; its locked SHA-256 is still required')
    return result


def main(argv=None):
    args = parser().parse_args(argv)
    destination = args.dest.resolve()
    require(not destination.exists(), 'Destination already exists; choose a new directory')
    require(not destination.is_relative_to(ROOT), 'Reproduction destination must be outside this repository')
    env = clean_environment(destination)
    revision = subprocess.check_output(['git', 'rev-parse', '--verify', args.revision + '^{commit}'],
                                       cwd=ROOT, env=env, text=True).strip()
    expected_script = subprocess.check_output(['git', 'show', revision + ':' + SCRIPT_PATH], cwd=ROOT, env=env)
    require(Path(__file__).read_bytes() == expected_script,
            'Run the wrapper from the requested immutable revision; script bytes differ')
    destination.mkdir(parents=True)
    record = {'schema_version': 1, 'result': 'fail', 'source_revision': revision,
              'project_prefix': PROJECT_PREFIX.as_posix(), 'scope': 'main_release',
              'paper_main_complete': False, 'dependency_mode': args.dependency_mode,
              'wrapper_sha256': hashlib.sha256(expected_script).hexdigest(),
              'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'commands': []}
    runner = Reproduction(destination, env, record)
    started = time.monotonic()
    try:
        checkout = destination / 'checkout'
        runner.run('clone', ['git', 'clone', '--no-hardlinks', '--no-checkout', str(ROOT), str(checkout)], ROOT)
        runner.run('checkout', ['git', 'checkout', '--detach', revision], checkout)
        require(not (checkout / '.git/objects/info/alternates').exists(), 'Clone uses Git object alternates')
        require(not runner.git(checkout, 'status', '--porcelain'), 'Fresh checkout is dirty')
        record['source_tree'] = runner.git(checkout, 'rev-parse', 'HEAD^{tree}')
        runner.run('repository-layout', ['python3', 'scripts/check_layout.py'], checkout)
        project = checkout / PROJECT_PREFIX
        require(not (project / '.lake').exists() and not (project / '.toolchain').exists(),
                'Fresh source unexpectedly contains execution caches')
        record['initial_project_oleans'] = project_oleans(project)
        require(not record['initial_project_oleans'], 'Project oleans present before setup')
        lock = read_json(project / 'locks/toolchain.json')
        manifest_bytes = (project / 'lake-manifest.json').read_bytes()
        packages = validate_manifest(json.loads(manifest_bytes), lock)
        asset = lock['compiler_assets'][platform.system() + '-' + platform.machine()]
        require((project / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v' + lock['lean_version'],
                'Compiler lock and lean-toolchain disagree')
        if args.compiler_archive:
            require(sha(args.compiler_archive) == asset['sha256'], 'Supplied compiler archive hash mismatch')
            archive = project / '.toolchain' / (asset['directory'] + '.tar.zst')
            archive.parent.mkdir()
            shutil.copy2(args.compiler_archive, archive)
        runner.run('compiler-bootstrap', ['python3', 'scripts/bootstrap.py'], project)
        archive = project / '.toolchain' / (asset['directory'] + '.tar.zst')
        record['compiler_archive_sha256'] = sha(archive)
        require(record['compiler_archive_sha256'] == asset['sha256'], 'Compiler archive changed')
        compiler = project / '.toolchain' / asset['directory'] / 'bin/lean'
        version = runner.run('compiler-version', [str(compiler), '--version'], project).strip()
        require('version ' + lock['lean_version'] + ',' in version and lock['lean_commit'] in version,
                'Unexpected compiler version or commit')
        record['compiler_version'] = version
        record['compiler_scope'] = 'Locked binary release archive, freshly extracted; not a compiler source rebuild'
        package_root = project / '.lake/packages'
        package_root.mkdir(parents=True)
        record['dependencies'] = []
        for package in packages:
            name = package['name']
            target = package_root / name
            target.mkdir()
            runner.run(name + '-init', ['git', 'init', '--quiet'], target)
            runner.run(name + '-origin', ['git', 'remote', 'add', 'origin', package['url']], target)
            runner.run(name + '-fetch', ['git', 'fetch', '--depth', '1', 'origin', package['rev']], target)
            runner.run(name + '-checkout', ['git', 'checkout', '--detach', 'FETCH_HEAD'], target)
            tag = package.get('inputRev', '')
            if re.fullmatch(r'v[0-9]+(?:\.[0-9]+)+(?:[-.][A-Za-z0-9.]+)?', tag):
                runner.run(name + '-tag', ['git', 'fetch', '--depth', '1', 'origin',
                           'refs/tags/' + tag + ':refs/tags/' + tag], target)
                require(runner.git(target, 'rev-parse', tag + '^{commit}') == package['rev'],
                        'Dependency release tag differs from locked commit: ' + name)
            require(runner.git(target, 'rev-parse', 'HEAD') == package['rev'], 'Dependency commit mismatch: ' + name)
            require(not runner.git(target, 'status', '--porcelain'), 'Fresh dependency is dirty: ' + name)
            require(not (target / '.git/objects/info/alternates').exists(), 'Dependency Git alternates: ' + name)
            require(not list(target.rglob('*.olean')), 'Public source includes a Lean build artifact: ' + name)
            record['dependencies'].append({'name': name, 'url': package['url'], 'rev': package['rev']})
        record['non_lean_display_assets'] = restore_display_assets(project, packages)
        if args.dependency_mode == 'official-cache':
            # Load only the freshly cloned, source-bound parser; do not evaluate
            # paper attachments or any research exploration code.
            sys.path.insert(0, str(checkout / 'scripts'))
            from check_layout import imports
            modules = set()
            for path in (project / 'ExactCriticalCurve').rglob('*.lean'):
                modules.update(name for name in imports(path.read_text())
                               if name == 'Mathlib' or name.startswith('Mathlib.'))
            require(modules, 'No explicit Mathlib import set found')
            record['official_cache_imports'] = sorted(modules)
            runner.run('official-mathlib-cache', ['bash', 'scripts/lake.sh', 'exe', 'cache', 'get',
                                                 *sorted(modules)], project)
        record['project_oleans_before_gate'] = project_oleans(project)
        require(not record['project_oleans_before_gate'], 'Project cache appeared before the fresh build')
        acceptance = destination / 'acceptance'
        runner.run('strict-acceptance', ['python3', 'scripts/check.py', '--require-main-proof',
                                        '--output', str(acceptance)], project)
        result = verify_acceptance(acceptance, project)
        require(result['git_commit'] == revision and not result['git_status'],
                'Acceptance was not run on the clean requested commit')
        require((project / 'lake-manifest.json').read_bytes() == manifest_bytes, 'Manifest changed during build')
        require(runner.git(checkout, 'rev-parse', 'HEAD') == revision
                and not runner.git(checkout, 'status', '--porcelain'), 'Source checkout changed during reproduction')
        def immutable_blob(name):
            return subprocess.check_output(['git', 'show', revision + ':' +
                         (PROJECT_PREFIX / name).as_posix()], cwd=checkout, env=env)
        record['strict_coverage'] = verify_source_and_coverage(result, acceptance, project, immutable_blob)
        record['acceptance_result_sha256'] = sha(acceptance / 'result.json')
        record['formal_source_sha256'] = result['layout']['formal_source_sha256']
        record['paper_main_complete'] = True
        record['inputs_match_immutable_tree'] = True
        record['result'] = 'pass'
    except Exception as error:
        record['error'] = str(error)
    finally:
        record['ended_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        record['elapsed_seconds'] = time.monotonic() - started
        runner.save()
        print(json.dumps({'result': record['result'], 'paper_main_complete': record['paper_main_complete'],
                          'record': str(destination / 'reproduction.json')}))
    return 0 if record['result'] == 'pass' else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
