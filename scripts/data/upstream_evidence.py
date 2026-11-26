#!/usr/bin/env python3
"""Validate explicit upstream excerpts and input links, optionally against Git archives."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

BASE = Path(__file__).resolve().parents[2]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pointer(value, path):
    for part in path.lstrip('/').split('/') if path else []:
        part = part.replace('~1', '/').replace('~0', '~')
        value = value[int(part)] if isinstance(value, list) else value[part]
    return value


def read_index(base):
    return json.loads((base / 'metadata/evidence/upstream/index.json').read_text())


def read_records(base, batch, entry):
    if entry['file'] is None:
        return []
    require(entry['file'] == batch + '.jsonl', 'Unexpected evidence filename')
    return [json.loads(line) for line in
            (base / 'metadata/evidence/upstream' / entry['file']).read_text().splitlines()]


def verify_record(base, batch, record, archives=False):
    require(record['schema_version'] == 'paperlean-upstream-evidence-1', 'Unsupported evidence schema')
    require(record['dataset'] == batch and record['origin'] == 'upstream_repository',
            'Evidence must originate in the registered upstream repository')
    require(not ({'label', 'verdict', 'gold_label', 'reason'} & record.keys()),
            'Upstream evidence must not carry a benchmark verdict')
    require(record['truth_status'] == 'unverified_upstream_claim' and
            record['usable_as_scoring_label'] is False, 'Upstream claims are not scoring labels')
    source = record['source']
    require(re.fullmatch(r'https://github.com/[^/]+/[^/]+', source['repository']) is not None,
            'Invalid upstream repository URL')
    require(source['url'].startswith(source['repository'] + '/'), 'Source URL outside upstream')
    kind_paths = {'pr': r'pull/\d+', 'issue': r'issues/\d+', 'commit': r'commit/[0-9a-f]{40}',
                  'repository_document': r'blob/[0-9a-f]{40}/.+'}
    require(source['kind'] in kind_paths and re.fullmatch(
        re.escape(source['repository'] + '/') + kind_paths[source['kind']], source['url']) is not None,
        'Invalid upstream source kind/URL')
    require(record['excerpts'] and all(e['text'].strip() for e in record['excerpts']),
            'Explicit upstream excerpts are required')
    require(record['projects'], 'Evidence requires a registered root binding')
    seen = set()
    for binding in record['projects']:
        identity = binding['project_id']
        require(identity not in seen and '/' not in identity and identity not in ('.', '..'),
                'Duplicate or unsafe evidence project ID')
        seen.add(identity)
        project = json.loads((base / 'datasets' / batch / 'projects' / identity / 'project.json').read_text())
        require(project['source']['repository'] == source['repository'], 'Upstream repository mismatch')
        require(binding['root'] in {t['declaration'] for t in project['targets']} and
                binding['source_commit'] == project['source']['commit'] and
                binding['input_sha256'] == project['input_sha256'], 'Stale evidence input binding')
        require(binding['relationship'] in ('reported_subject', 'dependency_context') and
                binding['statement_applicability'] == 'not_adjudicated',
                'Root association must not assert version-specific correctness')
        require(not ({'label', 'verdict', 'gold_label'} & binding.keys()), 'Binding must not carry a verdict')
    archive = record['archive']
    path = PurePosixPath(archive['path'])
    require(not path.is_absolute() and '..' not in path.parts and path.parts,
            'Unsafe archive locator')
    require(re.fullmatch('[0-9a-f]{40}', archive['commit']) is not None and
            re.fullmatch('[0-9a-f]{64}', archive['sha256']) is not None, 'Invalid archive digest')
    require(archive['path'].startswith(('reports/', 'experiments/real-project-errors/')),
            'Unsupported historical source locator')
    if archives:
        raw = subprocess.check_output(['git', 'show', archive['commit'] + ':' + archive['path']], cwd=base)
        require(hashlib.sha256(raw).hexdigest() == archive['sha256'], 'Archive source hash mismatch')
        if source['kind'] == 'repository_document':
            obj = raw.decode()
        else:
            obj = pointer(json.loads(raw), archive['object_pointer'])
            require(obj['html_url'] == source['url'], 'Archived upstream URL mismatch')
        for excerpt in record['excerpts']:
            original = pointer(obj, excerpt['field'])
            require(isinstance(original, str) and excerpt['text'] in original,
                    'Excerpt differs from archived upstream text')


def verify(base, config, archives=False):
    index = read_index(base)
    require(index['schema_version'] == 'paperlean-upstream-evidence-index-1', 'Unsupported evidence index')
    require(set(index['datasets']) == set(config['datasets']), 'Evidence scope differs from candidate')
    expected_files = {entry['file'] for entry in index['datasets'].values() if entry['file']}
    actual_files = {p.name for p in (base / 'metadata/evidence/upstream').glob('*.jsonl')}
    require(actual_files == expected_files, 'Unindexed or missing evidence files')
    total = covered = 0
    for batch, entry in index['datasets'].items():
        records = read_records(base, batch, entry)
        require(len({r['id'] for r in records}) == len(records), 'Duplicate evidence ID')
        projects = set()
        for record in records:
            verify_record(base, batch, record, archives)
            projects.update(p['project_id'] for p in record['projects'])
        population = len(list((base / 'datasets' / batch / 'projects').glob('*/project.json')))
        require(entry['evidence_records'] == len(records) and entry['inputs_with_evidence'] == len(projects)
                and entry['inputs_without_retained_evidence'] == population - len(projects),
                'Stale evidence coverage counts')
        total += len(records)
        covered += len(projects)
    print(f'PASS: {total} upstream evidence records, {covered} linked inputs; no scoring labels'
          + ('; archived excerpts verified' if archives else ''))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archives', action='store_true', help='Also compare excerpts against the local historical Git objects')
    args = parser.parse_args()
    config = json.loads((BASE / 'datasets/project-cases.json').read_text())
    verify(BASE, config, args.archives)
