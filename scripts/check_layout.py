#!/usr/bin/env python3
"""Check both independent project import graphs and the exact repository layout."""
from pathlib import Path
import hashlib
import json
import os
import re

if not __debug__:
    raise SystemExit('Optimized Python disables assertions; layout check refuses to run')

ROOT = Path(__file__).resolve().parents[1]
SECOND = 'proofs/arxiv-2610.00266'
INDEPENDENT_MAIN = ('docs/validation/2026-10-11-direct-integration/'
                    'independent-expected/IndependentAcceptance.lean')
EXTERNAL_ROOTS = {'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop', 'Qq', 'Plausible'}
# Only execution directories are excluded. In particular, proofs/ and arbitrary
# hidden directories remain visible to the repository project inventory.
RUNTIME_ROOTS = {'.git', '.lake', '.toolchain', 'artifacts', 'evidence', 'repro-build'}
RUNTIME_ROOTS |= {SECOND + '/' + name for name in
                 ('.lake', '.toolchain', 'artifacts', 'evidence', 'repro-build')}


def code_only(text):
    clean = []
    i = depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            if depth == 0:
                clean.append(' ')
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                clean.append('\n')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            clean.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    if text[i] == '\n':
                        clean.append('\n')
                    i += 1
        else:
            clean.append(text[i])
            i += 1
    assert depth == 0, 'Unterminated Lean comment'
    return ''.join(clean)


def imports(text):
    result = []
    code = code_only(text)
    assert not re.search(r'^\s*module\s*$', code, re.M), 'Unsupported Lean module syntax'
    for line in code.splitlines():
        if re.search(r'\bimport\b', line):
            assert re.fullmatch(r'\s*import(?: +[A-Za-z_][A-Za-z_0-9.]*)+\s*', line), (
                'Imports must use one complete physical line', line)
            result.extend(line.split()[1:])
    return result


def project_files(root, namespace):
    """Every file in this namespace must be reached through its Main module."""
    formal = root / namespace
    assert formal.is_dir() and not formal.is_symlink(), ('Missing formal directory', formal)
    for path in formal.rglob('*'):
        assert not path.is_symlink(), ('Formal source symlink forbidden', path)
    expected = {p.relative_to(root).as_posix() for p in formal.rglob('*.lean')}
    expected.add(namespace + '.lean')
    seen = set()

    def visit(name):
        if name in seen:
            return
        path = root / name
        assert path.is_file() and not path.is_symlink(), ('Missing formal import', name)
        seen.add(name)
        for imp in imports(path.read_text()):
            if imp == namespace or imp.startswith(namespace + '.'):
                visit(imp.replace('.', '/') + '.lean')
            else:
                assert imp.split('.')[0] in EXTERNAL_ROOTS, (
                    'Cross-project, Scratch, or unapproved import', name, imp)
                assert not (root / (imp.replace('.', '/') + '.lean')).exists(), (
                    'Local file shadows external import', imp)

    entry = root / (namespace + '.lean')
    assert namespace + '.Main' in imports(entry.read_text()), 'Formal root must import Main'
    visit(namespace + '.lean')
    assert seen == expected, ('Formal modules outside root build', sorted(expected - seen))
    return seen


def project_configs(root):
    configs = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [name for name in dirs
                   if (Path(directory) / name).relative_to(root).as_posix() not in RUNTIME_ROOTS]
        for name in dirs:
            assert not (Path(directory) / name).is_symlink(), (
                'Source directory symlink hides layout', Path(directory) / name)
        for name in files:
            if name.startswith('lakefile.'):
                path = Path(directory) / name
                assert not path.is_symlink(), ('Lake configuration symlink', path)
                configs.add(path.relative_to(root).as_posix())
    return configs


def check_pins(root, lock_path):
    lock = json.loads((root / lock_path).read_text())
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    assert (root / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v' + lock['lean_version']
    packages = manifest['packages']
    names = [p['name'] for p in packages]
    assert len(names) == len(set(names)), 'Duplicate dependency name'
    assert next(p['rev'] for p in packages if p['name'] == 'mathlib') == lock['mathlib_commit']
    assert all(re.fullmatch('[0-9a-f]{40}', p['rev']) for p in packages), 'Unpinned dependency'


def check():
    assert not (ROOT / 'pilot').exists(), 'Old second project must not remain'
    allowed_configs = {'lakefile.toml', SECOND + '/lakefile.toml'}
    assert project_configs(ROOT) == allowed_configs, (
        'Expected exactly the two registered Lake projects', sorted(project_configs(ROOT)))
    projects = {}
    frozen = {INDEPENDENT_MAIN}
    for prefix, namespace, lock_path in [
        ('', 'StabilizerLearning', 'toolchain-lock.json'),
        (SECOND, 'ExactCriticalCurve', 'locks/toolchain.json'),
    ]:
        root = ROOT / prefix
        formal = project_files(root, namespace)
        check_pins(root, lock_path)
        inputs = formal | {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', lock_path}
        inputs |= {p.relative_to(root).as_posix() for p in (root / 'scripts').iterdir()
                   if p.is_file() and p.suffix in {'.py', '.sh', '.lean', '.txt'}}
        if prefix:
            inputs |= {'docs/pgm-provenance.json', 'locks/proofwidgets-js.json',
                       'vendor/proofwidgets-js.tar.gz', 'paper/source.json', 'paper/main.tex'}
        else:
            inputs.add('Audit.lean')
        frozen |= {(Path(prefix) / name).as_posix() for name in inputs}
        projects[prefix or '.'] = {'namespace': namespace,
                                   'formal_modules': len(formal),
                                   'root_imports_main': True,
                                   'all_formal_modules_reachable': True}
    return {'result': 'pass', 'root_imports_main': True, 'scratch_excluded': True,
            'one_lake_project': False, 'independent_lake_projects': 2,
            'all_formal_modules_reachable': True, 'cross_project_imports': False,
            'projects': projects,
            'source_sha256': {n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest()
                              for n in sorted(frozen)}}


if __name__ == '__main__':
    print(json.dumps({k: v for k, v in check().items() if k != 'source_sha256'}, indent=2))
