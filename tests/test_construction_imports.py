import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/construction'))
import compiler


class CompilerImportTests(unittest.TestCase):
    def test_dependency_keys_include_meta_and_multiline_imports(self):
        source = '''/- import Fake.Hidden -/
module
public meta import dep.ToMathlib.Lint.UsesPMF
public import
  dep.FLT.Support
import Mathlib.Data.Nat.Basic Mathlib.Data.Int.Basic
-- import Fake.Comment
def text := "import Fake.String"
'''
        self.assertEqual(compiler.IMPORT.findall(source), [
            'dep.ToMathlib.Lint.UsesPMF', 'dep.FLT.Support',
            'Mathlib.Data.Nat.Basic', 'Mathlib.Data.Int.Basic'])
