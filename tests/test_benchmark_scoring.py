import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

import test_benchmark_protocol as T

P = T.P

SPEC = importlib.util.spec_from_file_location('scoring', P.BASE / 'scripts/evaluation/benchmark_scoring.py')
S = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(S)


def adjudicate(record, label='aligned'):
    record.update(reference_ready=True, status='adjudicated', label=label,
                  reviews=[{'reviewer': name, 'verdict': label, 'evidence': 'Checked quantifiers and scope.'}
                           for name in ('reviewer-a', 'reviewer-b')],
                  adjudication={'reviewer': 'reviewer-c', 'verdict': label,
                                'evidence': 'Resolved against the exact statement and formal closure.'})


class ScoringTests(unittest.TestCase):
    def test_explicit_provisional_scoring_and_stale_label_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            _, tasks, _, reviews = self.fixture(temp)
            record = reviews['records'][0]
            label = {k: record[k] for k in ('task_id', 'mode', 'label', 'input_sha256')}
            label.update(reviewer_type='model', human_adjudicated=False, reference_ready=False)
            labels = temp / 'labels.jsonl'
            labels.write_text(json.dumps(label) + '\n')
            batch = temp / 'batch'
            result = T.ProtocolTests().call('batch', '--tasks', tasks, '--output', batch, '--timeout', '10',
                                          '--', sys.executable, P.BASE / 'scripts/evaluation/mock_system.py')
            self.assertEqual(result.returncode, 0, result.stderr)
            output = temp / 'score.json'
            result = subprocess.run([sys.executable, str(P.BASE / 'scripts/evaluation/benchmark_scoring.py'), 'score',
                '--tasks', str(tasks), '--provisional-labels', str(labels), '--batch', str(batch),
                '--output', str(output)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            score = P.load(output)
            self.assertEqual(score['reference_kind'], 'provisional_model')
            self.assertEqual(score['counts']['eligible'], 1)
            self.assertEqual(score['counts']['abstained'], 1)
            self.assertEqual(score['accuracy'], 0)
            self.assertNotIn('reviews_sha256', score)
            label['input_sha256'] = '0' * 64
            labels.write_text(json.dumps(label) + '\n')
            with self.assertRaisesRegex(ValueError, 'Stale provisional reference'):
                S.score(tasks, labels, batch, provisional=True)

    def fixture(self, temp, count=1):
        helper = T.ProtocolTests()
        path = helper.fixture(temp)
        original = P.load(path)
        packages = []
        for number in range(count):
            package = copy.deepcopy(original)
            name = f'Root{number}'
            package['root_id'] = package['main_theorem']['id'] = name
            package['formal_context']['edges'][0]['source'] = name
            packages.append(package)
        path.write_text(''.join(json.dumps(p) + '\n' for p in packages))
        tasks = temp / 'tasks'
        result = helper.call('export', '--packages', path, '--output', tasks,
                             '--mode', 'theorem_only', '--allow-draft')
        self.assertEqual(result.returncode, 0, result.stderr)
        reviews = S.prepare(tasks)
        for record in reviews['records']:
            adjudicate(record)
        reviews_path = temp / 'reviews.json'
        P.write(reviews_path, reviews)
        return path, tasks, reviews_path, reviews

    def test_mode_specific_gate_and_review_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            packages, tasks, review_path, reviews = self.fixture(temp)
            helper = T.ProtocolTests()
            # A reviewed misalignment is a valid benchmark reference.
            adjudicate(reviews['records'][0], 'misaligned')
            P.write(review_path, reviews)
            args = ['export', '--packages', packages, '--mode', 'theorem_only', '--reviews', review_path]
            result = helper.call(*args, '--output', temp / 'ready')
            self.assertEqual(result.returncode, 0, result.stderr)
            index = P.load(temp / 'ready/index.json')
            self.assertFalse(index['tasks'][0]['development_draft'])
            for entry in index['tasks']:
                task_dir = temp / 'ready' / entry['directory']
                self.assertEqual(P.digest(task_dir / 'task.json'), entry['task_sha256'])
                self.assertNotIn('reviewer', (task_dir / 'input.json').read_text())
                self.assertNotIn('misaligned', (task_dir / 'input.json').read_text())
            result = helper.call('export', '--packages', packages, '--mode', 'full',
                                 '--reviews', review_path, '--output', temp / 'full')
            self.assertNotEqual(result.returncode, 0)
            package = P.load(packages)
            package['definitions'][0]['informal']['text'] = 'Still an unreviewed dependency description'
            packages.write_text(json.dumps(package) + '\n')
            self.assertEqual(helper.call(*args, '--output', temp / 'hidden-change').returncode, 0)
            package['main_theorem']['qualifiers'] = [{'text': 'New scope constraint'}]
            packages.write_text(json.dumps(package) + '\n')
            result = helper.call(*args, '--output', temp / 'stale', '--allow-draft')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Stale review', result.stderr)
            self.assertFalse((temp / 'stale').exists())

    def test_fixed_denominator_abstentions_failures_and_unresolved(self):
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            _, tasks, review_path, reviews = self.fixture(temp, 9)
            reviews['records'][7].update(reference_ready=False, status='pending', label=None,
                                         reviews=[], adjudication=None)
            reviews['records'][8].update(reference_ready=False, status='unresolved', label=None,
                                         adjudication=None)
            P.write(review_path, reviews)
            batch = temp / 'batch'
            batch.mkdir()
            config = {'protocol_version': P.VERSION, 'index_sha256': P.digest(tasks / 'index.json'),
                      'command': ['synthetic-fixture'], 'timeout_seconds': 10}
            P.write(batch / 'batch.json', config)
            entries = P.load(tasks / 'index.json')['tasks']
            statuses = ['completed'] * 3 + ['timeout', 'execution_failed', 'invalid_submission',
                                          'missing', 'completed', 'completed']
            for i, (entry, status) in enumerate(zip(entries, statuses)):
                if status == 'missing':
                    continue
                run_dir = batch / entry['directory']
                run_dir.mkdir()
                P.write(run_dir / 'run.json', {**config, 'task_id': entry['task_id'],
                        'mode': 'theorem_only', 'task_sha256': entry['task_sha256'], 'status': status})
                if status == 'completed':
                    verdict = {1: 'misaligned', 2: 'insufficient_information'}.get(i, 'aligned')
                    issues = [{'declaration_id': entry['task_id'], 'category': 'quantifier',
                               'explanation': 'Synthetic mismatch'}] if verdict == 'misaligned' else []
                    P.write(run_dir / 'prediction.json', {'task_id': entry['task_id'],
                            'verdict': verdict, 'issues': issues, 'summary': 'Synthetic prediction'})
            result = S.score(tasks, review_path, batch)
            self.assertEqual(result['target_count'], 9)
            self.assertEqual(result['counts']['eligible'], 7)
            self.assertEqual(result['counts']['unreviewed_or_unresolved'], 2)
            for outcome in ('correct', 'incorrect', 'abstained', 'timeout', 'execution_failed',
                            'invalid_submission', 'missing'):
                self.assertEqual(result['counts'][outcome], 1)
            self.assertEqual(result['accuracy'], 1 / 7)
            self.assertEqual(result['answer_coverage'], 2 / 7)
            self.assertEqual(result['answered_accuracy'], 1 / 2)
            self.assertEqual(result['target_correct_fraction'], 1 / 9)
            # A completed receipt with no valid prediction remains in the denominator.
            (batch / entries[0]['directory'] / 'prediction.json').unlink()
            result = S.score(tasks, review_path, batch)
            self.assertEqual(result['counts']['invalid_submission'], 2)
            self.assertEqual(result['accuracy'], 0)
            reviews['records'][0]['task_sha256'] = '0' * 64
            P.write(review_path, reviews)
            with self.assertRaisesRegex(ValueError, 'Stale review'):
                S.score(tasks, review_path, batch)

    def test_pilot_selection_and_frozen_review_document(self):
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            packages, tasks, review_path, reviews = self.fixture(temp, 2)
            helper = T.ProtocolTests()
            selection = temp / 'selection.json'
            P.write(selection, {'schema_version': 'paperlean-pilot-1', 'mode': 'theorem_only',
                                'samples': [{'task_id': 'Root1'}]})
            selected = temp / 'selected'
            result = helper.call('export', '--packages', packages, '--mode', 'theorem_only',
                                 '--sample-file', selection, '--reviews', review_path, '--output', selected)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([row['task_id'] for row in P.load(selected / 'index.json')['tasks']], ['Root1'])
            batch = temp / 'batch'
            batch.mkdir()
            P.write(batch / 'batch.json', {'protocol_version': P.VERSION,
                    'index_sha256': P.digest(selected / 'index.json'), 'command': [], 'timeout_seconds': 10})
            self.assertEqual(S.score(selected, review_path, batch)['counts']['missing'], 1)
            reviews['records'][1]['adjudication']['evidence'] += ' Changed.'
            P.write(review_path, reviews)
            with self.assertRaisesRegex(ValueError, 'Frozen review document mismatch'):
                S.score(selected, review_path, batch)
            P.write(selection, {'schema_version': 'paperlean-pilot-1', 'mode': 'full',
                                'samples': [{'task_id': 'Root1'}]})
            result = helper.call('export', '--packages', packages, '--mode', 'theorem_only',
                                 '--sample-file', selection, '--allow-draft', '--output', temp / 'bad-mode')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Pilot selection mode mismatch', result.stderr)

    def test_reviewed_export_runner_and_scoring_cli(self):
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            packages, tasks, review_path, _ = self.fixture(temp)
            helper = T.ProtocolTests()
            prepared = temp / 'prepared.json'
            command = [sys.executable, str(P.BASE / 'scripts/evaluation/benchmark_scoring.py')]
            result = subprocess.run(command + ['prepare', '--tasks', str(tasks), '--output', str(prepared)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(P.load(prepared)['records'][0]['status'], 'pending')
            ready = temp / 'ready'
            result = helper.call('export', '--packages', packages, '--mode', 'theorem_only',
                                 '--reviews', review_path, '--output', ready)
            self.assertEqual(result.returncode, 0, result.stderr)
            batch = temp / 'batch'
            result = helper.call('batch', '--tasks', ready, '--output', batch, '--',
                                 sys.executable, P.BASE / 'scripts/evaluation/mock_system.py')
            self.assertEqual(result.returncode, 0, result.stderr)
            output = temp / 'score.json'
            args = command + ['score', '--tasks', str(ready), '--reviews', str(review_path),
                              '--batch', str(batch), '--output', str(output)]
            result = subprocess.run(args, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            score = P.load(output)
            self.assertEqual(score['target_count'], 1)
            self.assertEqual(score['counts']['eligible'], 1)
            self.assertEqual(score['counts']['abstained'], 1)
            self.assertEqual(score['development_task_count'], 0)
            self.assertEqual(score['accuracy'], 0)
            self.assertEqual(score['answer_coverage'], 0)
            self.assertIsNone(score['answered_accuracy'])
            original = output.read_bytes()
            self.assertNotEqual(subprocess.run(args, capture_output=True).returncode, 0)
            self.assertEqual(output.read_bytes(), original)

    def test_review_validation_and_empty_scoring_denominator(self):
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            _, tasks, review_path, reviews = self.fixture(temp)
            for mutation in ('duplicate', 'one_reviewer', 'pending_ready', 'bad_label'):
                document = copy.deepcopy(reviews)
                record = document['records'][0]
                if mutation == 'duplicate':
                    document['records'].append(copy.deepcopy(record))
                elif mutation == 'one_reviewer':
                    record['reviews'].pop()
                elif mutation == 'pending_ready':
                    record.update(status='pending', label=None, adjudication=None)
                else:
                    record['label'] = 'insufficient_information'
                P.write(review_path, document)
                with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                    P.read_reviews(review_path)
            P.write(review_path, S.prepare(tasks))
            batch = temp / 'batch'
            batch.mkdir()
            P.write(batch / 'batch.json', {'protocol_version': P.VERSION,
                    'index_sha256': P.digest(tasks / 'index.json'), 'command': [], 'timeout_seconds': 10})
            result = S.score(tasks, review_path, batch)
            self.assertIsNone(result['accuracy'])
            self.assertIsNone(result['answered_accuracy'])
            self.assertIsNone(result['answer_coverage'])
            self.assertEqual(result['counts']['execution_missing'], 1)
            self.assertEqual(result['counts']['missing'], 0)


if __name__ == '__main__':
    unittest.main()
