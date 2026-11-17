import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts.data.analysis_evidence import verify


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value)+'\n')


def fixture(base,alter=None):
    label=dict(dataset='example',project_id='sample',task_id='example:sample',
               input_sha256='a'*64,label='misaligned',reason='A premise is missing.',
               review_scope='The complete source theorem.',
               human_adjudicated=False,reference_ready=False,review_status='provisional')
    analysis=dict(label,schema_version='leanreviewbench-analysis-evidence-1',
                  roots=['sample'],analysis_status='retained_label_reason_only',upstream_evidence=[])
    if alter:alter(analysis)
    path='metadata/evidence/analysis/example/sample.json'
    write(base/path,analysis)
    digest=hashlib.sha256((base/path).read_bytes()).hexdigest()
    write(base/'metadata/labels/example.jsonl',label)
    write(base/'datasets/example/projects/sample/project.json',dict(targets=[dict(declaration='sample')]))
    write(base/'metadata/evidence/analysis/index.json',dict(
        schema_version='leanreviewbench-analysis-index-1',
        records=[dict(dataset='example',project_id='sample',input_sha256='a'*64,
                      path=path,sha256=digest,analysis_status=analysis['analysis_status'],
                      upstream_evidence_records=len(analysis['upstream_evidence']))],
        counts={analysis['analysis_status']:1}))


class AnalysisEvidenceTests(unittest.TestCase):
    def test_reason_only_is_valid_without_claiming_detailed_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base);verify(base)

    def test_self_consistent_hashes_do_not_hide_changed_verdict(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base,lambda row:row.update(label='aligned'))
            with self.assertRaisesRegex(ValueError,'verdict/input'):verify(base)

    def test_missing_upstream_reference_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp)
            fixture(base,lambda row:row.update(upstream_evidence=[dict(path='metadata/evidence/upstream/example.jsonl',id='absent')]))
            with self.assertRaisesRegex(ValueError,'upstream evidence binding'):verify(base)

    def test_scope_mismatch_is_rejected_even_with_valid_evidence_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base,lambda row:row.update(review_scope='A restricted special case.'))
            with self.assertRaisesRegex(ValueError,'verdict/input'):verify(base)

    def test_detailed_review_cannot_be_claimed_from_reason_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base,lambda row:row.update(analysis_status='detailed_review_retained'))
            with self.assertRaisesRegex(ValueError,'Detailed analysis missing'):verify(base)
