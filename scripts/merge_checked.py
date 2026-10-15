#!/usr/bin/env python3
"""Historical single-project fast-forward helper; multi-project targets fail closed."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SECOND_CONFIG = 'proofs/arxiv-2610.00266/lakefile.toml'


def require_single_project_target(root, target):
    """Refuse before any checkout or merge; this helper cannot certify both papers."""
    present_now = (root / SECOND_CONFIG).exists()
    present_at_target = subprocess.run(
        ['git', 'cat-file', '-e', target + ':' + SECOND_CONFIG], cwd=root,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    if present_now or present_at_target:
        raise SystemExit('This historical helper cannot certify a two-project release. '
                         'Require both strict pull-request checks and use the normal reviewed merge procedure.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('branch')
    args = parser.parse_args()

    def git(*parts):
        return subprocess.check_output(['git', *parts], cwd=ROOT, text=True).strip()

    target = git('rev-parse', args.branch + '^{commit}')
    require_single_project_target(ROOT, target)
    if git('status', '--porcelain'):
        raise SystemExit('Commit or snapshot outstanding work before merging.')
    base = git('branch', '--show-current')
    if not base:
        raise SystemExit('Use a named integration branch.')
    subprocess.run(['git', 'merge-base', '--is-ancestor', 'HEAD', target], cwd=ROOT, check=True)
    subprocess.run(['git', 'switch', '--detach', target], cwd=ROOT, check=True)
    try:
        subprocess.run([sys.executable, str(ROOT / 'scripts/check.py')], cwd=ROOT, check=True)
        if git('status', '--porcelain'):
            raise RuntimeError('Checks changed tracked source.')
    finally:
        subprocess.run(['git', 'switch', base], cwd=ROOT, check=True)
    subprocess.run(['git', 'merge', '--ff-only', target], cwd=ROOT, check=True)
    print('Merged checked commit ' + target + ' into ' + base)


if __name__ == '__main__':
    main()
