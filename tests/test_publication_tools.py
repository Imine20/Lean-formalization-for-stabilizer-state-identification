"""Small adversarial checks for publication boundaries; no network or Lean builds."""
from pathlib import Path
import copy
import hashlib
import importlib.util
import io
import json
import platform
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
import check_layout as layout
import source_policy as policy
import verify_arxiv_2610 as verify
import merge_checked


def write(root, path, text):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)


def layout_fixture(root):
    for prefix, namespace, lockname in [('', 'StabilizerLearning', 'toolchain-lock.json'),
            (layout.SECOND, 'ExactCriticalCurve', 'locks/toolchain.json')]:
        project = root / prefix
        files = {namespace + '.lean': 'import ' + namespace + '.Main\n',
                 namespace + '/Main.lean': 'import Mathlib.Data.Nat.Basic\n',
                 'lakefile.toml': '', 'lean-toolchain': 'leanprover/lean4:v4.24.0',
                 lockname: json.dumps({'lean_version': '4.24.0', 'mathlib_commit': 'a' * 40}),
                 'lake-manifest.json': json.dumps({'packages': [{'name': 'mathlib', 'rev': 'a' * 40}]}),
                 'scripts/check.py': ''}
        if prefix:
            files.update({'docs/pgm-provenance.json': '{}', 'locks/proofwidgets-js.json': '{}',
                          'vendor/proofwidgets-js.tar.gz': '', 'paper/source.json': '{}', 'paper/main.tex': ''})
        else:
            files['Audit.lean'] = ''
        for name, text in files.items():
            write(project, name, text)
    write(root, layout.INDEPENDENT_MAIN, '')


class LayoutTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        layout_fixture(self.root)
        self.patcher = patch.object(layout, 'ROOT', self.root)
        self.patcher.start()
        self.addCleanup(self.patcher.stop)

    def test_both_graphs_and_independent_statement_are_bound(self):
        result = layout.check()
        self.assertEqual(result['independent_lake_projects'], 2)
        self.assertIn(layout.INDEPENDENT_MAIN, result['source_sha256'])
        self.assertIn(layout.SECOND + '/ExactCriticalCurve/Main.lean', result['source_sha256'])

    def test_unreachable_child_source_rejected(self):
        write(self.root, layout.SECOND + '/ExactCriticalCurve/Unused.lean', 'theorem unused : True := trivial')
        with self.assertRaisesRegex(AssertionError, 'outside root build'):
            layout.check()

    def test_cross_project_imports_rejected_in_both_directions(self):
        for prefix, namespace, other in [('', 'StabilizerLearning', 'ExactCriticalCurve'),
                (layout.SECOND, 'ExactCriticalCurve', 'StabilizerLearning')]:
            with self.subTest(project=namespace):
                path = self.root / prefix / namespace / 'Main.lean'
                original = path.read_text()
                path.write_text('import ' + other + '.Main\n')
                with self.assertRaisesRegex(AssertionError, 'Cross-project'):
                    layout.check()
                path.write_text(original)

    def test_extra_project_in_proofs_or_hidden_directory_rejected(self):
        for name in ['proofs/third/lakefile.toml', '.hidden/lakefile.lean',
                     'proofs/third/.lake/lakefile.toml']:
            with self.subTest(path=name):
                write(self.root, name, '')
                with self.assertRaisesRegex(AssertionError, 'exactly the two'):
                    layout.check()
                (self.root / name).unlink()

    def test_missing_second_project_rejected(self):
        (self.root / layout.SECOND / 'lakefile.toml').unlink()
        with self.assertRaisesRegex(AssertionError, 'exactly the two'):
            layout.check()

    def test_only_execution_directories_are_ignored(self):
        write(self.root, '.lake/packages/mathlib/lakefile.lean', '')
        self.assertEqual(layout.check()['result'], 'pass')

    def test_child_external_shadow_rejected(self):
        write(self.root, layout.SECOND + '/Mathlib/Data/Nat/Basic.lean', '')
        with self.assertRaisesRegex(AssertionError, 'shadows external'):
            layout.check()

    def test_comment_separated_cross_project_import_is_rejected(self):
        write(self.root, layout.SECOND + '/ExactCriticalCurve/Main.lean',
              'import/- separator -/StabilizerLearning.Main\n')
        with self.assertRaisesRegex(AssertionError, 'Cross-project'):
            layout.check()

    def test_parser_ignores_strings_and_nested_comments_but_rejects_new_syntax(self):
        self.assertEqual(layout.imports('import Mathlib\n/- /- import Scratch.Bad -/ -/\n'
                                        'def s := "import Scratch.Bad"\n'), ['Mathlib'])
        for text in ['public import ExactCriticalCurve.Main', 'import\nExactCriticalCurve.Main',
                     'module\nimport ExactCriticalCurve.Main']:
            with self.subTest(source=text), self.assertRaises(AssertionError):
                layout.imports(text)


class PolicyTests(unittest.TestCase):
    def test_only_reviewed_child_archives_and_license_are_allowed(self):
        prefix = layout.SECOND + '/'
        for name in ['paper/arXiv-2610.00266v1.tar.gz', 'vendor/proofwidgets-js.tar.gz',
                     'vendor/ProofWidgets-LICENSE', '.gitignore']:
            self.assertTrue(policy.approved(prefix + name), name)
        for name in ['paper/other.tar.gz', 'vendor/other.tar.gz', 'vendor/other-license',
                     '.lake/packages/mathlib/Mathlib.lean', 'docs/private-key.pem', '../escape.py']:
            self.assertFalse(policy.approved(prefix + name), name)

    def test_validation_logs_only(self):
        prefix = layout.SECOND + '/'
        self.assertTrue(policy.approved(prefix + 'docs/validation/release/build.log'))
        self.assertFalse(policy.approved(prefix + 'docs/misc/build.log'))
        self.assertFalse(policy.approved(prefix + 'scripts/build.log'))


class HistoricalMergeGuardTests(unittest.TestCase):
    def test_refuses_current_or_target_second_project_without_mutation(self):
        for current, target_code in [(True, 1), (False, 0)]:
            with self.subTest(current=current), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                if current:
                    write(root, merge_checked.SECOND_CONFIG, '')
                with patch.object(merge_checked.subprocess, 'run') as run:
                    run.return_value.returncode = target_code
                    with self.assertRaisesRegex(SystemExit, 'both strict'):
                        merge_checked.require_single_project_target(root, 'a' * 40)
                    self.assertEqual(run.call_count, 1)
                    self.assertEqual(run.call_args.args[0][:3], ['git', 'cat-file', '-e'])


class ReproductionTests(unittest.TestCase):
    def test_ambient_lean_and_git_paths_are_removed(self):
        env = verify.clean_environment(Path('/new'), {'LEAN_PATH': '/bad', 'LEAN_SYSROOT': '/bad',
            'LAKE_PACKAGES_DIR': '/bad', 'GIT_ALTERNATE_OBJECT_DIRECTORIES': '/bad', 'PATH': '/bin',
            'XDG_CACHE_HOME': '/ambient-cache', 'MATHLIB_CACHE_DIR': '/ambient-mathlib',
            'PYTHONDONTWRITEBYTECODE': '0'})
        for key in ['LEAN_PATH', 'LEAN_SYSROOT', 'LAKE_PACKAGES_DIR', 'GIT_ALTERNATE_OBJECT_DIRECTORIES']:
            self.assertNotIn(key, env)
        self.assertEqual(env['MATHLIB_CACHE_DIR'], '/new/mathlib-cache')
        self.assertEqual(env['XDG_CACHE_HOME'], '/new/xdg-cache')
        self.assertEqual(env['PYTHONDONTWRITEBYTECODE'], '1')
        self.assertEqual(env['MATHLIB_NO_CACHE_ON_UPDATE'], '1')

    def test_manifest_rejects_floating_revisions_duplicate_packages_and_private_urls(self):
        manifest = {'packagesDir': '.lake/packages', 'packages': [
            {'name': name, 'url': url, 'type': 'git', 'rev': 'a' * 40}
            for name, url in verify.PUBLIC_PACKAGES.items()]}
        lock = {'mathlib_commit': 'a' * 40}
        self.assertEqual(len(verify.validate_manifest(manifest, lock)), 9)
        for mutation in ['rev', 'url', 'duplicate']:
            invalid = copy.deepcopy(manifest)
            if mutation == 'duplicate':
                invalid['packages'].append(invalid['packages'][0])
            else:
                invalid['packages'][0][mutation] = 'main' if mutation == 'rev' else 'ssh://private/dependency'
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError):
                verify.validate_manifest(invalid, lock)

    def asset_fixture(self, root, members):
        archive = root / 'vendor/proofwidgets-js.tar.gz'
        archive.parent.mkdir(parents=True)
        (archive.parent / 'ProofWidgets-LICENSE').write_text('license')
        with tarfile.open(archive, 'w:gz') as stream:
            for name, data in members:
                member = tarfile.TarInfo(name)
                member.size = len(data)
                stream.addfile(member, io.BytesIO(data))
        write(root, 'locks/proofwidgets-js.json', json.dumps({'proofwidgets_commit': 'a' * 40,
              'archive_sha256': verify.sha(archive), 'files': {'index.js': hashlib.sha256(b'ok').hexdigest()}}))
        return [{'name': 'proofwidgets', 'rev': 'a' * 40}]

    def test_display_assets_verify_complete_archive_before_extraction(self):
        for members, succeeds in [([('js/index.js', b'ok')], True),
                ([('../index.js', b'ok')], False), ([('js/index.js', b'bad')], False),
                ([('js/index.js', b'ok'), ('js/index.js', b'ok')], False)]:
            with self.subTest(members=members), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                packages = self.asset_fixture(root, members)
                if succeeds:
                    verify.restore_display_assets(root, packages)
                    self.assertEqual((root / '.lake/packages/proofwidgets/.lake/build/js/index.js').read_bytes(), b'ok')
                else:
                    with self.assertRaises(RuntimeError):
                        verify.restore_display_assets(root, packages)
                    self.assertFalse((root / '.lake').exists())

    def acceptance_fixture(self, project, acceptance):
        asset = {'directory': 'test-compiler'}
        write(project, 'locks/toolchain.json', json.dumps({'compiler_assets': {
            platform.system() + '-' + platform.machine(): asset}}))
        commands = {'compiler': [str(project / '.toolchain/test-compiler/bin/lean'), '--version'],
                    **verify.GATE_COMMANDS}
        result = {'status': 'pass', 'scope': 'main_release', 'paper_main_complete': True,
                  'inputs_unchanged_through_audit': True, 'commands': []}
        for label, command in commands.items():
            write(acceptance, label + '.log', 'PROJECT_AUDIT_OK\nKERNEL_EXPECTED_TYPE_OK constant target\n'
                                           'KERNEL_EXPECTED_TYPE_OK body target\n')
            result['commands'].append({'label': label, 'command': command, 'exit_code': 0,
                'log': label + '.log', 'log_sha256': verify.sha(acceptance / (label + '.log'))})
        write(acceptance, 'result.json', json.dumps(result))
        return result

    def test_acceptance_rejects_skipped_pilot_and_tampered_logs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            project, acceptance = root / 'project', root / 'acceptance'
            result = self.acceptance_fixture(project, acceptance)
            self.assertEqual(verify.verify_acceptance(acceptance, project)['status'], 'pass')
            invalid = copy.deepcopy(result)
            invalid['commands'] = [c for c in invalid['commands'] if c['label'] != 'pilot_types']
            write(acceptance, 'result.json', json.dumps(invalid))
            with self.assertRaisesRegex(RuntimeError, 'skipped'):
                verify.verify_acceptance(acceptance, project)
            write(acceptance, 'result.json', json.dumps(result))
            write(acceptance, 'release.log', 'tampered')
            with self.assertRaisesRegex(RuntimeError, 'hash mismatch'):
                verify.verify_acceptance(acceptance, project)

    def test_cli_has_no_skip_or_weak_gate_option(self):
        args = verify.parser().parse_args(['--dest', '/new'])
        self.assertEqual(args.dependency_mode, 'official-cache')
        self.assertFalse(hasattr(args, 'require_main_proof'))


if __name__ == '__main__':
    unittest.main()
