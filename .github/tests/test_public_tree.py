"""Keep private assistant state and credential-shaped strings out of releases."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('check_public_tree', ROOT / 'tools/check_public_tree.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class PublicTreeTests(unittest.TestCase):
    def test_private_documents_and_caches_are_rejected(self):
        for path in ('.claude/handover/note.md', 'HANDOVER.md', 'atlas_data/NEXT.md',
                     'deep/REVIEW_EMAIL.md', 'cache/__pycache__/module.pyc', '.env.production'):
            self.assertTrue(checker.inspect(path, b''), path)

    def test_public_research_and_examples_are_allowed(self):
        for path in ('deep/SOURCE_MAP.md', 'atlas_data/audits/ttr_comparison.md',
                     'tool/llm/policy.md', '.env.example'):
            self.assertEqual(checker.inspect(path, b'Public reproducibility instructions.'), [])

    def test_report_never_echoes_credentials(self):
        token = b'sk-' + b'or-v1-' + b'A' * 64
        result = checker.inspect('bad.txt', b'first line\n' + token)
        self.assertEqual(result[0]['lines'], [2])
        self.assertNotIn(token.decode(), repr(result))

    def test_personal_paths_are_reported_but_example_paths_are_not(self):
        private = b'/Users/' + b'private-user/project'
        self.assertTrue(checker.inspect('notes.md', private))
        self.assertFalse(checker.inspect('test.py', b'/Users/example/project'))

    def test_current_public_candidates_are_clean(self):
        count, findings = checker.working_tree(ROOT)
        self.assertGreater(count, 100)
        self.assertEqual(findings, [])


if __name__ == '__main__':
    unittest.main()
