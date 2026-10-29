#!/usr/bin/env python3
"""Regression tests for source inventory (not for the mathematics)."""
import tempfile
import unittest
from pathlib import Path
from audit_circulation import inventory, reachable, strip_comments_strings


class InventoryTests(unittest.TestCase):
    def test_nested_comments_and_escaped_strings(self):
        source = '/- sorry /- axiom -/ admit -/\n-- unsafe\ndef x := "sorry \\" unsafe"\ntheorem y : True := by trivial\n'
        cleaned = strip_comments_strings(source)
        self.assertEqual(len(source), len(cleaned))
        self.assertEqual(source.count('\n'), cleaned.count('\n'))
        self.assertNotIn('sorry', cleaned)
        self.assertNotIn('unsafe', cleaned)
        self.assertIn('theorem y', cleaned)

    def test_real_risk_retained(self):
        self.assertIn('sorry', strip_comments_strings('theorem x : False := by sorry'))

    def test_unterminated(self):
        with self.assertRaises(ValueError):
            strip_comments_strings('/- unfinished')

    def test_graph(self):
        self.assertEqual(reachable({'A': ['B'], 'B': ['C'], 'C': ['B']}, ['A']),
                         {'A', 'B', 'C'})

    def test_small_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Girth').mkdir()
            (root / 'Girth.lean').write_text('import Girth.A\n')
            (root / 'Girth/A.lean').write_text('theorem a : True := by trivial\n')
            (root / 'Girth/B.lean').write_text('theorem b : True := by trivial\n')
            (root / 'CheckA.lean').write_text('import Girth.A\n#print axioms a\n')
            report = inventory(root)
            self.assertEqual(report['summary']['proof_modules'], 2)
            self.assertEqual(report['summary']['outside_umbrella_import_closure'], ['Girth.B'])
            self.assertEqual(report['summary']['empty_check_files'], [])
            self.assertEqual(report['summary']['risk_tokens_outside_comments_strings'], [])


if __name__ == '__main__':
    unittest.main()
