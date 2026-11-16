#!/usr/bin/env python3
"""Prepare private human review records and score a fixed theorem-only task inventory."""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import sys

SPEC = importlib.util.spec_from_file_location('benchmark_protocol', Path(__file__).with_name('benchmark_protocol.py'))
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def inventory(tasks):
    tasks = Path(tasks).resolve()
    index = P.load(tasks / 'index.json')
    P.require(index['protocol_version'] == P.VERSION and index['mode'] == 'theorem_only',
              'Scoring/review v1 requires theorem_only protocol v1 tasks')
    P.require(index['tasks'], 'Empty task inventory')
    seen, directories, result = set(), set(), []
    for entry in index['tasks']:
        P.require(entry['task_id'] not in seen and entry['directory'] not in directories,
                  'Duplicate task ID or directory')
        seen.add(entry['task_id'])
        directories.add(entry['directory'])
        directory = tasks / entry['directory']
        P.require(not directory.is_symlink() and directory.resolve().is_relative_to(tasks),
                  'Unsafe task directory')
        task, payload = P.validate_task(directory)
        P.require(task['task_id'] == entry['task_id'] and task['mode'] == index['mode'] and
                  P.digest(directory / 'task.json') == entry['task_sha256'], 'Task index mismatch')
        result.append((entry, task, payload, P.digest(directory / 'input.json')))
    return result


def prepare(tasks):
    records = []
    for entry, task, _, input_hash in inventory(tasks):
        records.append({'task_id': task['task_id'], 'mode': task['mode'],
                        'task_sha256': entry['task_sha256'], 'input_sha256': input_hash,
                        'reference_ready': False, 'status': 'pending', 'label': None,
                        'reviews': [], 'adjudication': None})
    return {'schema_version': P.REVIEW_VERSION, 'records': records}


def fraction(numerator, denominator):
    return numerator / denominator if denominator else None


def score(tasks, reviews_path, batch, provisional=False):
    tasks, batch = Path(tasks).resolve(), Path(batch).resolve()
    entries = inventory(tasks)
    if provisional:
        labels = [json.loads(line) for line in Path(reviews_path).read_text().splitlines() if line.strip()]
        reviews = {}
        task_map = {task['task_id']: (entry, task, input_hash) for entry, task, _, input_hash in entries}
        seen = set()
        for label in labels:
            key = (label['task_id'], label['mode'])
            P.require(key not in seen, 'Duplicate provisional reference')
            seen.add(key)
            P.require(label['mode'] == 'theorem_only' and label['label'] in ('aligned', 'misaligned')
                      and label['reviewer_type'] == 'model' and label['human_adjudicated'] is False
                      and label['reference_ready'] is False, 'Invalid provisional model reference')
            if label['task_id'] not in task_map:
                continue
            entry, task, input_hash = task_map[label['task_id']]
            P.require(label['input_sha256'] == input_hash, 'Stale provisional reference')
            reviews[key] = dict(task_id=task['task_id'], mode=task['mode'], reference_ready=True,
                                input_sha256=input_hash, task_sha256=entry['task_sha256'], label=label['label'])
    else:
        reviews = P.read_reviews(reviews_path)
    index = P.load(tasks / 'index.json')
    if 'reviews_sha256' in index:
        P.require(not provisional, 'Human-reviewed task index cannot use provisional references')
        P.require(index['reviews_sha256'] == P.digest(reviews_path), 'Frozen review document mismatch')
    config = P.load(batch / 'batch.json')
    P.require(config['protocol_version'] == P.VERSION and
              config['index_sha256'] == P.digest(tasks / 'index.json'), 'Batch index mismatch')
    counts, rows = Counter(), []
    for entry, task, payload, input_hash in entries:
        record = reviews.get((task['task_id'], task['mode']))
        if record is not None:
            P.require(P.review_matches(record, task, input_hash, entry['task_sha256']),
                      f'Stale review: {task["task_id"]}')
        eligible = record is not None and record['reference_ready']
        counts['eligible'] += eligible
        counts['unreviewed_or_unresolved'] += not eligible
        run_dir = batch / entry['directory']
        P.require(not run_dir.is_symlink() and run_dir.resolve().is_relative_to(batch), 'Unsafe run directory')
        verdict = None
        status = 'missing'
        if (run_dir / 'run.json').exists():
            receipt = P.load(P.safe_file(run_dir, 'run.json'))
            P.require(receipt['task_id'] == task['task_id'] and receipt['mode'] == task['mode'] and
                      receipt['task_sha256'] == entry['task_sha256'] and
                      receipt['protocol_version'] == P.VERSION and
                      receipt['command'] == config['command'] and
                      receipt['timeout_seconds'] == config['timeout_seconds'], 'Run identity mismatch')
            status = receipt['status']
            P.require(status in ('completed', 'invalid_submission', 'timeout', 'execution_failed'),
                      'Unknown run status')
            if status == 'completed':
                try:
                    prediction = P.validate_prediction(P.load(P.safe_file(run_dir, 'prediction.json')), task, payload)
                    verdict = prediction['verdict']
                except (ValueError, OSError, KeyError, TypeError):
                    status = 'invalid_submission'
        outcome = status
        if eligible and verdict is not None:
            if verdict == 'insufficient_information':
                outcome = 'abstained'
            else:
                outcome = 'correct' if verdict == record['label'] else 'incorrect'
        counts['execution_' + status] += 1
        if eligible:
            counts[outcome] += 1
            if verdict in ('aligned', 'misaligned'):
                counts['answered'] += 1
                counts[f'confusion_{record["label"]}_{verdict}'] += 1
        rows.append({'task_id': task['task_id'], 'eligible': eligible,
                     'label': record['label'] if eligible else None,
                     'execution_status': status, 'verdict': verdict,
                     'outcome': outcome if eligible else 'unreviewed_or_unresolved'})
    for name in ('eligible', 'unreviewed_or_unresolved', 'correct', 'incorrect', 'answered',
                 'abstained', 'timeout', 'execution_failed', 'invalid_submission', 'missing'):
        counts.setdefault(name, 0)
    return {'schema_version': 'paperlean-score-1', 'mode': 'theorem_only',
            'reference_kind': 'provisional_model' if provisional else 'adjudicated_human',
            'index_sha256': P.digest(tasks / 'index.json'),
            ('provisional_labels_sha256' if provisional else 'reviews_sha256'): P.digest(reviews_path),
            'batch_sha256': P.digest(batch / 'batch.json'),
            'development_task_count': sum(bool(e['development_draft']) for e, _, _, _ in entries),
            'target_count': len(entries), 'counts': dict(counts),
            'accuracy': fraction(counts['correct'], counts['eligible']),
            'answer_coverage': fraction(counts['answered'], counts['eligible']),
            'answered_accuracy': fraction(counts['correct'], counts['answered']),
            'target_correct_fraction': fraction(counts['correct'], len(entries)),
            'tasks': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ('prepare', 'score'):
        command = sub.add_parser(name)
        command.add_argument('--tasks', required=True)
        command.add_argument('--output', required=True)
        if name == 'score':
            references = command.add_mutually_exclusive_group(required=True)
            references.add_argument('--reviews', help='Hash-bound adjudicated human review JSON')
            references.add_argument('--provisional-labels', help='Explicitly score against non-gold model labels (JSONL)')
            command.add_argument('--batch', required=True)
    args = parser.parse_args()
    try:
        P.require(not Path(args.output).exists(), 'Output already exists; choose a fresh path')
        result = prepare(args.tasks) if args.action == 'prepare' else score(
            args.tasks, args.provisional_labels or args.reviews, args.batch, provisional=bool(args.provisional_labels))
        P.write(args.output, result)
        print(f'Wrote {args.action} result to {args.output}')
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
