import json
from pathlib import Path
import unittest
from unittest.mock import patch
import copy

from scripts.data.publication_readiness import audit, label_blockers, license_review
from scripts.data.publication_readiness import read as real_read

ROOT = Path(__file__).resolve().parents[1]


class PublicationReadinessTests(unittest.TestCase):
    def test_clean_contexts_use_the_native_schema(self):
        result = audit(ROOT)
        self.assertEqual(result['inputs'], 26)
        self.assertEqual(result['unique_input_contexts'], 25)
        self.assertEqual(result['format_errors'], [])
        self.assertEqual(result['human_review_pending'], 0)
        self.assertEqual(result['license_scope_unresolved'], 11)
        self.assertEqual(result['license_notices_accepted'], 11)
        self.assertEqual(result['license_blocking'], 0)
        self.assertTrue(result['merge_ready'])

    def test_completed_labels_allow_explicitly_accepted_evidence_notices(self):
        # Simulate completed binary human review without modifying any real data.
        with patch('scripts.data.publication_readiness.label_blockers', side_effect=lambda _: []):
            result = audit(ROOT)
        self.assertEqual(result['human_review_pending'], 0)
        self.assertEqual(result['license_scope_unresolved'], 11)
        self.assertEqual(result['license_notices_accepted'], 11)
        self.assertTrue(result['merge_ready'])

    def test_provisional_binary_label_is_not_human_review(self):
        self.assertEqual(label_blockers(dict(label='aligned', human_adjudicated=False,
                                            review_status='agent_preliminary')),
                         ['human_review_pending'])
        self.assertEqual(label_blockers(dict(label='undetermined', human_adjudicated=True,
                                            review_status='human_reviewed')),
                         ['binary_label_pending'])
        self.assertEqual(label_blockers(dict(label='aligned', human_adjudicated=True,
                                            review_status='human_reviewed')), [])

    def test_unaccepted_license_gap_still_blocks_after_label_review(self):
        def unaccepted_license_read(path):
            value = real_read(path)
            if path == ROOT / 'licenses/index.json':
                value = copy.deepcopy(value)
                for batch in value['review_datasets'].values():
                    for record in batch['projects']:
                        record.pop('admission', None)
            return value
        # This is a gate regression, not a license or human-review assertion.
        with patch('scripts.data.publication_readiness.label_blockers', side_effect=lambda _: []), \
                patch('scripts.data.publication_readiness.read', side_effect=unaccepted_license_read):
            result = audit(ROOT)
        self.assertEqual(result['format_errors'], [])
        self.assertEqual(result['license_blocking'], 11)
        self.assertFalse(result['merge_ready'])

    def test_admission_is_source_specific_and_does_not_override_a_restriction(self):
        index = real_read(ROOT / 'licenses/index.json')
        record = copy.deepcopy(next(r for r in index['review_datasets']['qinz1yang']['projects']
                                    if r.get('admission')))
        self.assertFalse(license_review(record)[0])
        record['known_explicit_restriction'] = True
        self.assertTrue(license_review(record)[0])
        record.pop('known_explicit_restriction')
        record['admission']['source_commit'] = '0' * 40
        self.assertTrue(license_review(record)[0])

    def test_deferred_and_excluded_sources_are_not_publication_inputs(self):
        removed = {'QDG-SOBOLEV-after', 'QDG-POINTED-MODELS-CONVERGENCE-BEFORE',
                   'QDG-POINTED-MODELS-CONVERGENCE-AFTER', 'FM-model-proxy-before',
                   'FM-model-proxy-after', 'FM-false-repair-before', 'FM-false-repair-after',
                   'FM-injectivity-split-before'}
        current = {r['project_id'] for r in audit(ROOT)['records']}
        self.assertFalse(removed & current)
        for path in (ROOT / 'datasets').glob('*/projects/*/project.json'):
            self.assertNotIn(path.parent.name, removed)

    def test_joint_inputs_have_explicit_informal_mode(self):
        for batch in ['qinz1yang', 'frenzymath']:
            for path in (ROOT / 'datasets' / batch / 'projects').glob('*/project.json'):
                meta = json.loads(path.read_text())
                if meta.get('target_mode') == 'joint':
                    informal = [json.loads(s) for s in
                                (path.parent / 'informal.jsonl').read_text().splitlines()]
                    self.assertEqual(informal[0]['target_mode'], 'joint')
                    self.assertEqual({t['declaration'] for t in informal[0]['targets']},
                                     {t['declaration'] for t in meta['targets']})


if __name__ == '__main__':
    unittest.main()
