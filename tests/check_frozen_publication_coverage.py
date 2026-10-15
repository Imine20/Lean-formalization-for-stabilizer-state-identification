#!/usr/bin/env python3
"""Regress the publication sealer against preserved real V3 logs, without Lean.

This tests historical evidence handling; it never certifies the current tree.
The complete nested frozen source and selected V3 evidence must be present.
"""
from pathlib import Path
import argparse
import json
import re
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import verify_arxiv_2610 as verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    project = args.root.resolve() / verify.PROJECT_PREFIX
    historical = project / ('docs/validation/2026-10-12/'
                            'main-release-correspondence-a741ad2-strict-v3/acceptance')
    result = json.loads((historical / 'result.json').read_text())
    verify.require(result['git_commit'] == 'a741ad2633d99a28fb4bbbe86e3a9a0ac5b7970b',
                   'Historical regression fixture has a different source commit')
    # Historical result hashes bind all of these delivered source bytes; the
    # publication wrapper separately uses Git blobs from its actual frozen tree.
    read_source = lambda name: (project / name).read_bytes()
    coverage = verify.verify_source_and_coverage(result, historical, project, read_source)
    rejected = []
    with tempfile.TemporaryDirectory(prefix='publication-coverage-controls-') as directory:
        acceptance = Path(directory)
        for name in ['axioms.log', 'pilot_types.log', 'release.log']:
            shutil.copy2(historical / name, acceptance / name)
        release_log = (acceptance / 'release.log').read_text()
        for name in sorted(verify.REQUIRED_RELEASE_BODIES):
            pattern = '^KERNEL_EXPECTED_TYPE_OK body ' + re.escape(name) + '$'
            verify.require(len(re.findall(pattern, release_log, re.M)) == 1,
                           'Expected one historical original-body marker for ' + name)
            (acceptance / 'release.log').write_text(re.sub(pattern, 'REMOVED_BODY_CONTROL', release_log,
                                                          count=1, flags=re.M))
            try:
                verify.verify_source_and_coverage(result, acceptance, project, read_source)
            except (RuntimeError, ValueError) as error:
                verify.require('body' in str(error), 'Control failed for an unrelated reason: ' + str(error))
                rejected.append(name)
            else:
                raise RuntimeError('Missing original-body marker was accepted: ' + name)
    print(json.dumps({'result': 'pass', 'scope': 'historical evidence regression only; no Lean build',
          'project_declarations': coverage['project_declarations'],
          'rejected_missing_release_bodies': rejected}, indent=2))


if __name__ == '__main__':
    main()
