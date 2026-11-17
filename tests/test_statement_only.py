"""Recorded statement-context checks remain bound to sources without graph files."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/data'))
from context_validation import verify
from project_cases import formal_digest, input_digest

spec = importlib.util.spec_from_file_location('release_fixtures', ROOT / 'tests/test_release.py')
fixtures = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixtures)


def fixture(base):
    directory = fixtures.fixture(base)
    config_path = base / 'datasets/project-cases.json'
    config = json.loads(config_path.read_text())
    config.update(lean_toolchain='leanprover/lean4:v4.34.1', external_libraries={})
    fixtures.write(config_path, config)
    (directory / 'formal/Main.lean').write_text('theorem sample : True := sorry\n')
    meta = json.loads((directory / 'project.json').read_text())
    meta.update(input_sha256=input_digest(directory),
                formal={'proofs_erased': True, 'declaration_slice': True})
    fixtures.write(directory / 'project.json', meta)
    document = dict(schema_version='leanreviewbench-context-validation-1',
                    lean_toolchain=config['lean_toolchain'], external_libraries={},
                    proofs_erased=True, original_theorem_proofs_certified=False,
                    records=[dict(dataset='example', project_id='sample', roots=['sample'],
                                  input_sha256=meta['input_sha256'],
                                  formal_sha256=formal_digest(directory), compilation='passed',
                                  extraction='passed', statement_preservation='passed',
                                  nonproof_definition_preservation='passed')])
    fixtures.write(base / 'metadata/validation.json', document)
    return directory, document


class StatementOnlyEvidenceTests(unittest.TestCase):
    def test_checks_available_without_graph_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            fixture(base)
            verify(base)
            self.assertFalse((base / 'metadata/derived-graphs').exists())

    def test_stale_checks_cannot_be_rebound_by_only_updating_project_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            directory, _ = fixture(base)
            (directory / 'formal/Main.lean').write_text('theorem sample : False := sorry\n')
            meta = json.loads((directory / 'project.json').read_text())
            meta['input_sha256'] = input_digest(directory)
            fixtures.write(directory / 'project.json', meta)
            with self.assertRaisesRegex(ValueError, 'Stale context'):
                verify(base)

    def test_invalid_claims_and_coverage_rejected(self):
        mutations = [
            lambda d: d.update(original_theorem_proofs_certified=True),
            lambda d: d.update(lean_toolchain='other'),
            lambda d: d['records'].clear(),
            lambda d: d['records'].append(copy.deepcopy(d['records'][0])),
            lambda d: d['records'][0].update(roots=['other']),
            lambda d: d['records'][0].update(extraction='failed'),
            lambda d: d['records'][0].update(formal_sha256='stale')]
        for mutate in mutations:
            with self.subTest(mutation=mutate), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp)
                _, document = fixture(base)
                mutate(document)
                fixtures.write(base / 'metadata/validation.json', document)
                with self.assertRaises(ValueError):
                    verify(base)


if __name__ == '__main__':
    unittest.main()
