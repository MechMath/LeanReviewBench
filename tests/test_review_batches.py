"""Review batches validate from committed inputs without ignored build artifacts."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'review_batch_check', ROOT / 'scripts/construction/review_batches/check_batch.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
refresh_spec = importlib.util.spec_from_file_location(
    'review_batch_refresh', ROOT / 'scripts/construction/review_batches/refresh_batch.py')
refresher = importlib.util.module_from_spec(refresh_spec)
refresh_spec.loader.exec_module(refresher)


class ReviewBatchTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.base = self.root / 'datasets/qinz1yang'
        self.md = self.base / 'metadata'
        self.md.mkdir(parents=True)
        source = ROOT / 'datasets/qinz1yang'
        ids = {'QDG-COMPACT-ISOTOPY-BEFORE', 'QDG-COMPACT-ISOTOPY-AFTER'}
        index = json.loads((source / 'index.json').read_text())
        index['projects'] = [r for r in index['projects'] if r['project_id'] in ids]
        self.write(self.base / 'index.json', index)
        validation = json.loads((source / 'metadata/technical-validation.json').read_text())
        validation['records'] = [r for r in validation['records'] if r['project_id'] in ids]
        self.write(self.md / 'technical-validation.json', validation)
        for r in validation['records']:
            for key in ['technical_receipt', 'preservation_receipt']:
                dst = self.root / r[key]
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / r[key], dst)
        for identity in ids:
            shutil.copytree(source / 'projects' / identity, self.base / 'projects' / identity)
        pending = json.loads((source / 'metadata/pending-scope-reviews.json').read_text())
        self.write(self.md / 'pending-scope-reviews.json',
                   [r for r in pending if r['project_id'] in ids])
        labels = [json.loads(s) for s in
                  (source / 'metadata/provisional-labels.jsonl').read_text().splitlines()]
        (self.md / 'provisional-labels.jsonl').write_text(''.join(
            json.dumps(r) + '\n' for r in labels if r['project_id'] in ids))

    @staticmethod
    def write(path, value):
        path.write_text(json.dumps(value) + '\n')

    def run_check(self, *extra):
        with patch.object(checker, 'ROOT', self.root), patch.object(
                sys, 'argv', ['check_batch.py', '--batch', 'qinz1yang', *extra]):
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                checker.main()
            return json.loads(output.getvalue())

    def test_persisted_receipts_do_not_need_build_graphs(self):
        self.assertFalse((self.root / 'build').exists())
        result = self.run_check()
        self.assertEqual(result['graph_check'], 'persisted_receipt_bindings_only')
        self.assertEqual(result['projects'], 2)

    def test_deep_check_requires_actual_local_graph(self):
        with self.assertRaises(FileNotFoundError):
            self.run_check('--with-build-graphs')

    def test_changed_computational_source_invalidates_receipt(self):
        source = self.base / 'projects/QDG-COMPACT-ISOTOPY-BEFORE/formal/Main.lean'
        source.write_text(source.read_text() + '\n-- changed\n')
        with self.assertRaisesRegex(ValueError, 'Input digest differs'):
            self.run_check()

    def test_unreviewed_label_cannot_claim_human_adjudication(self):
        path = self.md / 'provisional-labels.jsonl'
        record = json.loads(path.read_text())
        record['human_adjudicated'] = True
        path.write_text(json.dumps(record) + '\n')
        with self.assertRaisesRegex(ValueError, 'promoted to gold'):
            self.run_check()

    def test_refresh_preserves_technical_deferral_and_filters_active_queue(self):
        project = self.base / 'projects/QDG-COMPACT-ISOTOPY-BEFORE/project.json'
        meta = json.loads(project.read_text())
        meta['preparation_status'] = 'deferred_technical'
        self.write(project, meta)
        self.write(self.md / 'retained-processing.json', {
            'candidate_count': 1, 'records': [{
                'candidate_id': 'compact-vector-space-isotopy-vacuity',
                'expected_version_count': 2}]})
        (self.md / 'deferred-development-plan.jsonl').write_text('')
        with patch.object(refresher, 'ROOT', self.root), patch.object(
                sys, 'argv', ['refresh_batch.py', '--batch', 'qinz1yang']), \
                contextlib.redirect_stdout(io.StringIO()):
            refresher.main()
        processing = json.loads((self.md / 'retained-processing.json').read_text())
        self.assertEqual(processing['records'][0]['status'], 'deferred_technical')
        self.assertEqual(processing['prepared_family_count'], 0)
        queue = json.loads((self.md / 'human-review-queue.json').read_text())
        self.assertEqual([r['project_id'] for r in queue['records']],
                         ['QDG-COMPACT-ISOTOPY-AFTER'])
        # Deferral changes workflow metadata, not the bound mathematical input.
        self.assertEqual(self.run_check()['projects'], 2)


if __name__ == '__main__':
    unittest.main()
