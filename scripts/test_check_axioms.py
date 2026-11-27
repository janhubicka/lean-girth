#!/usr/bin/env python3
"""Regression tests for the axiom-log checker, not mathematical proofs."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CHECKER = Path(__file__).with_name('check_axioms.py')


class AxiomCheckerTests(unittest.TestCase):
    def check(self, source: str, log: str, *, optimized: bool = False) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Check.lean').write_text(source, encoding='utf-8')
            (root / 'Check.log').write_text(log, encoding='utf-8')
            return subprocess.run([sys.executable, *(['-O'] if optimized else []), str(CHECKER),
                                   str(root / 'Check.log'), str(root / 'Check.lean')],
                                  capture_output=True, text=True, check=False)

    def test_standard_axioms(self):
        for optimized in (False, True):
            with self.subTest(optimized=optimized):
                self.assertEqual(self.check('#print axioms T\n',
                    "'T' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
                    optimized=optimized).returncode, 0)

    def test_no_axioms(self):
        for optimized in (False, True):
            with self.subTest(optimized=optimized):
                self.assertEqual(self.check('#print axioms T\n',
                    "'T' does not depend on any axioms\n", optimized=optimized).returncode, 0)

    def assert_rejected(self, source: str, log: str, message: str):
        for optimized in (False, True):
            with self.subTest(optimized=optimized):
                result = self.check(source, log, optimized=optimized)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)
                self.assertNotIn('Checked ', result.stdout)

    def test_empty_audit_rejected(self):
        self.assert_rejected('import Girth\n', '', 'No axiom declarations requested')

    def test_sorry_axiom_rejected(self):
        self.assert_rejected('#print axioms T\n',
            "'T' depends on axioms: [sorryAx]\n", 'Unexpected axioms in T')

    def test_missing_result_rejected(self):
        self.assert_rejected('#print axioms T\n', '', 'Missing or unexpected audit results')

    def test_unexpected_result_rejected(self):
        self.assert_rejected('#print axioms T\n',
            "'T' does not depend on any axioms\n'U' does not depend on any axioms\n",
            'Missing or unexpected audit results')

    def test_conflicting_duplicate_rejected(self):
        unsafe = "'T' depends on axioms: [sorryAx]\n"
        safe_reports = ("'T' does not depend on any axioms\n",
                        "'T' depends on axioms: [propext]\n")
        for safe in safe_reports:
            for log in (unsafe + safe, safe + unsafe):
                with self.subTest(log=log):
                    self.assert_rejected('#print axioms T\n', log, 'Duplicate audit result for T')

    def test_identical_duplicate_rejected(self):
        self.assert_rejected('#print axioms T\n',
            "'T' does not depend on any axioms\n" * 2, 'Duplicate audit result for T')

    def test_wrapped_axioms(self):
        for optimized in (False, True):
            with self.subTest(optimized=optimized):
                self.assertEqual(self.check('#print axioms T\n',
                    "'T' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n",
                    optimized=optimized).returncode, 0)


if __name__ == '__main__':
    unittest.main()
