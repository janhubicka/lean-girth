#!/usr/bin/env python3
"""Regression tests for the axiom-log checker, not mathematical proofs."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CHECKER = Path(__file__).with_name('check_axioms.py')


class AxiomCheckerTests(unittest.TestCase):
    def check(self, source: str, log: str) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Check.lean').write_text(source, encoding='utf-8')
            (root / 'Check.log').write_text(log, encoding='utf-8')
            return subprocess.run([sys.executable, str(CHECKER),
                                   str(root / 'Check.log'), str(root / 'Check.lean')],
                                  capture_output=True, text=True, check=False)

    def test_standard_axioms(self):
        self.assertEqual(self.check('#print axioms T\n',
            "'T' depends on axioms: [propext, Classical.choice, Quot.sound]\n").returncode, 0)

    def test_no_axioms(self):
        self.assertEqual(self.check('#print axioms T\n',
            "'T' does not depend on any axioms\n").returncode, 0)

    def test_empty_audit_rejected(self):
        result = self.check('import Girth\n', '')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('No axiom declarations requested', result.stderr)

    def test_sorry_axiom_rejected(self):
        self.assertNotEqual(self.check('#print axioms T\n',
            "'T' depends on axioms: [sorryAx]\n").returncode, 0)

    def test_missing_result_rejected(self):
        self.assertNotEqual(self.check('#print axioms T\n', '').returncode, 0)

    def test_unexpected_result_rejected(self):
        self.assertNotEqual(self.check('#print axioms T\n',
            "'T' does not depend on any axioms\n'U' does not depend on any axioms\n").returncode, 0)


if __name__ == '__main__':
    unittest.main()
