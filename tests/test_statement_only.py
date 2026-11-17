"""Proof-erased contexts require explicit, input-bound extraction evidence."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts/data'))
from derived_graphs import load_for, sha
from project_cases import formal_files, input_digest


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value) + '\n')


def fixture(base):
    project = base / 'datasets/example/projects/sample'
    (project / 'formal').mkdir(parents=True)
    (project / 'formal/Main.lean').write_text('theorem sample : True := sorry\n')
    write(project / 'informal.jsonl', {'id': 'main', 'text': 'True holds.'})
    meta = {'targets': [{'declaration': 'sample'}]}
    write(project / 'project.json', meta)
    meta['input_sha256'] = input_digest(project)
    write(project / 'project.json', meta)
    graph = base / 'metadata/derived-graphs/graphs/sample.json'
    write(graph, {'schema_version': 1, 'evidence': 'compiled_environment',
                  'roots': ['sample'], 'nodes': [], 'edges': []})
    receipt_path = base / 'metadata/derived-graphs/receipts/sample.json'
    receipt = {'schema_version': 'paperlean-statement-only-receipt-1',
               'status': 'passed', 'input_sha256': meta['input_sha256'],
               'graph_sha256': sha(graph), 'proof_erasure': True,
               'new_sorry_or_axioms': True, 'fresh_compilation': True,
               'original_theorem_proof_certified': False,
               'statement_preservation': 'passed',
               'nonproof_definition_preservation': 'passed',
               'formal_sources': [list(row) for row in formal_files(project)]}
    write(receipt_path, receipt)
    record = {'dataset': 'example', 'project_id': 'sample', 'roots': ['sample'],
              'input_sha256': meta['input_sha256'], 'evidence': 'compiled_environment',
              'graph_path': graph.relative_to(base).as_posix(), 'graph_sha256': sha(graph),
              'receipt_path': receipt_path.relative_to(base).as_posix(),
              'receipt_sha256': sha(receipt_path)}
    index = base / 'metadata/derived-graphs/index.json'
    write(index, {'schema_version': 'paperlean-derived-graphs-1', 'records': [record]})
    return project, receipt_path, receipt, index, record


class StatementOnlyEvidenceTests(unittest.TestCase):
    def change_receipt(self, base, **changes):
        project, path, receipt, index, record = fixture(base)
        receipt.update(changes)
        write(path, receipt)
        record['receipt_sha256'] = sha(path)
        write(index, {'schema_version': 'paperlean-derived-graphs-1', 'records': [record]})
        return project

    def test_explicit_proof_erasure_does_not_certify_original_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            project, *_ = fixture(base)
            _, evidence = load_for(base, project)
            self.assertTrue(evidence['fresh_compilation'])
            self.assertFalse(evidence['original_theorem_proof_certified'])

    def test_legacy_receipt_cannot_silently_accept_new_holes(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            project = self.change_receipt(base, schema_version=1)
            with self.assertRaisesRegex(ValueError, 'hole-free'):
                load_for(base, project)

    def test_statement_only_receipt_cannot_claim_original_proof_certification(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            project = self.change_receipt(base, original_theorem_proof_certified=True)
            with self.assertRaisesRegex(ValueError, 'statement-only'):
                load_for(base, project)

    def test_source_inventory_must_match_compiled_context(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            project = self.change_receipt(base, formal_sources=[])
            with self.assertRaisesRegex(ValueError, 'statement-only'):
                load_for(base, project)
