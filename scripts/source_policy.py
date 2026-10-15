"""Explicit source snapshot policy for the two independent proof projects."""
from pathlib import PurePosixPath
import re

EXCLUDED_DIRS = {'.git', '.lake', '.toolchain', '.agents', '.codex', '.aws', '.ssh',
                 'artifacts', 'evidence', '__pycache__', 'node_modules', 'models', 'repro-build'}
SENSITIVE = re.compile(r'(^|[._-])(credentials?|secrets?|passwords?|tokens?|api[-_]?keys?)([._-]|$)', re.I)
KNOWN_ROOT = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'toolchain-lock.json', '.gitignore'}
SOURCE_EXT = {'.lean', '.py', '.sh', '.md', '.json', '.toml', '.yaml', '.yml', '.tex', '.bib', '.bst', '.sty', '.txt'}
SECOND = ('proofs', 'arxiv-2610.00266')
SECOND_EXACT = {
    '.gitignore', 'README.md', 'AGENTS.md', 'ExactCriticalCurve.lean',
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
    'locks/toolchain.json', 'locks/proofwidgets-js.json',
    'paper/arXiv-2610.00266v1.tar.gz', 'paper/main.tex', 'paper/source.json',
    'vendor/proofwidgets-js.tar.gz', 'vendor/ProofWidgets-LICENSE', 'vendor/README.md',
}


def forbidden(name):
    p = PurePosixPath(name)
    n = p.name.lower()
    return (p.is_absolute() or '..' in p.parts or
            any(x in EXCLUDED_DIRS for x in p.parts) or n.startswith('.env') or
            n in {'.netrc', '.git-credentials', 'id_rsa', 'id_ed25519', '.ds_store'} or
            bool(SENSITIVE.search(n)) or
            p.suffix in {'.key', '.pem', '.p12', '.pfx', '.olean', '.ilean', '.trace', '.pyc'})


def approved(name):
    p = PurePosixPath(name)
    if forbidden(name):
        return False
    if p.parts[:2] == SECOND:
        relative = PurePosixPath(*p.parts[2:])
        if relative.as_posix() in SECOND_EXACT:
            return True
        if relative.parts[:1] == ('ExactCriticalCurve',):
            return relative.suffix == '.lean'
        if relative.parts[:1] in {('scripts',), ('tests',)}:
            return relative.suffix in {'.lean', '.py', '.sh', '.txt'}
        if relative.parts[:1] == ('docs',):
            return (relative.suffix in SOURCE_EXT or
                    relative.parts[:2] == ('docs', 'validation') and relative.suffix == '.log')
        return False
    if name == 'paper/arXiv-2609.13923v1.tar.gz':
        return True
    if name == '.github/workflows/lean.yml':
        return True
    if len(p.parts) == 1:
        return (name in KNOWN_ROOT or p.suffix in {'.lean', '.md', '.py'} or
                p.name.startswith('backup-receipt') and p.suffix == '.json')
    if p.parts[0] not in {'StabilizerLearning', 'Scratch', 'docs', 'scripts', 'paper', 'pilot', 'planning', 'proofs', 'tests'}:
        return False
    if p.suffix in SOURCE_EXT or p.name == 'lean-toolchain':
        return True
    return p.parts[:2] == ('docs', 'validation') and p.suffix == '.log'


def content_check(data, name):
    patterns = [rb'-----BEGIN (?:[A-Z]+ )*PRIVATE KEY-----', rb'gh[pousr]_[A-Za-z0-9]{30,}',
                rb'github_pat_[A-Za-z0-9_]{30,}', rb'sk-[A-Za-z0-9_-]{30,}']
    if any(re.search(p, data) for p in patterns):
        raise RuntimeError('Possible credential in approved source; snapshot refused: ' + name)
