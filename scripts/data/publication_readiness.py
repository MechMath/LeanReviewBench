#!/usr/bin/env python3
"""Check pending publication batches; --require-reviewed is a strict merge gate.

Native schema, hashes, labels, provenance and recorded context checks are validated
by check_release_candidate.py. This adds cleanup and human/licensing readiness.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]


def read(path):
    return json.loads(path.read_text())


def label_blockers(record):
    reasons = []
    if record.get('human_adjudicated') is not True or record.get('review_status') != 'human_reviewed':
        reasons.append('human_review_pending')
    if record.get('label') not in ('aligned', 'misaligned'):
        reasons.append('binary_label_pending')
    return reasons


def audit(base=BASE):
    config = read(base / 'datasets/project-cases.json')
    license_index = read(base / 'licenses/index.json').get('review_datasets', {})
    validation = {(r['dataset'], r['project_id']): r
                  for r in read(base / 'metadata/validation.json')['records']}
    rows, errors, duplicates = [], [], []
    for batch in config.get('review_datasets', {}):
        directory = base / 'datasets' / batch
        labels = {r['project_id']: r for r in map(
            json.loads, (base / 'metadata/labels' / (batch + '.jsonl')).read_text().splitlines())}
        licenses = {r['project_id']: r for r in license_index.get(batch, {}).get('projects', [])}
        seen = defaultdict(list)
        projects = sorted((directory / 'projects').glob('*/project.json'))
        if {p.name for p in directory.iterdir()} - {'projects', 'index.csv', 'README.md', 'NOTICE', 'metadata'}:
            errors.append(batch + ': unexpected dataset files')
        allowed_metadata = {'deferred-development-plan.jsonl', 'technical-feasibility.json', 'archive.json'}
        if {p.name for p in (directory / 'metadata').iterdir()} - allowed_metadata:
            errors.append(batch + ': intermediate metadata retained')
        if set(labels) != {p.parent.name for p in projects}:
            errors.append(batch + ': label coverage differs')
        for path in projects:
            meta = read(path)
            identity = meta['id']
            if set(p.name for p in path.parent.iterdir()) != {'project.json', 'informal.jsonl', 'CHANGES.md', 'formal'}:
                errors.append(f'{batch}:{identity}: unexpected project files')
            if (not meta['formal'].get('declaration_slice') or
                    not meta['formal'].get('proofs_erased') or
                    meta.get('preparation_status') == 'deferred_technical'):
                errors.append(f'{batch}:{identity}: incomplete/deferred context in publication inputs')
            checks = validation.get((batch, identity), {})
            if any(checks.get(key) != 'passed' for key in (
                    'compilation', 'extraction', 'statement_preservation', 'nonproof_definition_preservation')):
                errors.append(f'{batch}:{identity}: incomplete context checks')
            raw_informal = (path.parent / 'informal.jsonl').read_text()
            if 'build/' in raw_informal or '/home/' in raw_informal or 'binding_review_status' in raw_informal:
                errors.append(f'{batch}:{identity}: acquisition/review process leaked into informal input')
            blockers = label_blockers(labels.get(identity, {}))
            if licenses.get(identity, {}).get('status') != 'license-copy-retained':
                blockers.append('historical_license_scope_unresolved')
            rows.append(dict(dataset=batch, project_id=identity, input_sha256=meta['input_sha256'],
                             blockers=blockers))
            seen[meta['input_sha256']].append(meta)
        for digest, same in seen.items():
            if len(same) < 2:
                continue
            if len({r['split_group'] for r in same}) != 1 or len({r['group_id'] for r in same}) != 1:
                errors.append(batch + ': identical contexts cross split/group boundaries')
            duplicates.append(dict(dataset=batch, input_sha256=digest,
                                   project_ids=[r['id'] for r in same],
                                   policy='Historical versions share one split/group; count once for independent-error/evaluation-context counts.'))
    return dict(schema_version='leanreviewbench-publication-readiness-1',
                inputs=len(rows), unique_input_contexts=len({r['input_sha256'] for r in rows}),
                format_errors=errors, merge_ready=not errors and all(not r['blockers'] for r in rows),
                human_review_pending=sum('human_review_pending' in r['blockers'] for r in rows),
                license_scope_unresolved=sum('historical_license_scope_unresolved' in r['blockers'] for r in rows),
                records=rows, duplicate_contexts=duplicates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-reviewed', action='store_true')
    args = parser.parse_args()
    result = audit()
    print(json.dumps(result, ensure_ascii=False, indent=2))
    raise SystemExit(bool(result['format_errors']) or (args.require_reviewed and not result['merge_ready']))


if __name__ == '__main__':
    main()
