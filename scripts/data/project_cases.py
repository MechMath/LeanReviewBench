#!/usr/bin/env python3
"""Maintain the registered text-only project-case batches, without preparation archives."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re

BASE = Path(__file__).resolve().parents[2]
CONFIG = BASE / 'datasets/project-cases.json'
IMPORT = re.compile(r'(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)')
FIELDS = ['id', 'root', 'commit', 'group_id', 'before_ids', 'after_ids', 'status']


def read(path):
    return json.loads(path.read_text())


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def projects(dataset):
    return sorted((BASE / 'datasets' / dataset / 'projects').glob('*/project.json'))


def target_roots(meta):
    roots = [target['declaration'] for target in meta['targets']]
    require(roots and len(roots) == len(set(roots)), 'Missing or duplicate project targets')
    return roots


def input_digest(project):
    meta = read(project / 'project.json')
    informal = [json.loads(line) for line in (project / 'informal.jsonl').read_text().splitlines()]
    payload = {'root': meta['targets'][0]['declaration'],
               'sources': formal_files(project),
               'informal': informal}
    roots = target_roots(meta)
    if len(roots) > 1 and meta.get('target_mode') == 'joint':
        # Preserve refactor's explicit joint-input identity.
        payload.pop('root')
        payload.update(targets=meta['targets'], target_mode='joint')
    elif len(roots) > 1:
        # Preserve research's already reviewed multi-root input identity.
        payload['roots'] = roots
    resources = [(p.relative_to(project).as_posix(), sha(p.read_bytes()))
                 for p in sorted((project / 'formal').rglob('*'))
                 if p.is_file() and p.suffix != '.lean']
    if resources:
        payload['resources'] = resources
    return sha(json.dumps(payload, ensure_ascii=False, sort_keys=True).encode())


def formal_files(project):
    return [(p.relative_to(project).as_posix(), sha(p.read_bytes()))
            for p in sorted((project / 'formal').rglob('*.lean'))]


def formal_digest(project):
    return sha(json.dumps(formal_files(project), ensure_ascii=False).encode())


def index_rows(dataset):
    rows = []
    for path in projects(dataset):
        meta = read(path)
        rows.append(dict(id=meta['id'], root=';'.join(target_roots(meta)),
                         commit=meta['source']['commit'], group_id=meta['group_id'],
                         before_ids=';'.join(meta['before_ids']), after_ids=';'.join(meta['after_ids']),
                         status=meta['status']))
    return rows


def write_index(dataset):
    with (BASE / 'datasets' / dataset / 'index.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(index_rows(dataset))


def check(config):
    total = links = 0
    counts = {}
    for dataset in {**config['datasets'], **config.get('review_datasets', {})}:
        directory = BASE / 'datasets' / dataset
        require(not (directory / 'tasks.jsonl').exists(), f'{dataset}: unexpected task package')
        metas = {p.parent.name: read(p) for p in projects(dataset)}
        with (directory / 'index.csv').open(newline='') as stream:
            reader = csv.DictReader(stream)
            require(reader.fieldnames == FIELDS, f'{dataset}: index columns')
            actual = list(reader)
        require(actual == index_rows(dataset), f'{dataset}: stale index; run index')
        counts[dataset] = dict(cases=len(metas), ready=0, misaligned=0, undetermined=0, blocked=0)
        for identity, meta in metas.items():
            project = directory / 'projects' / identity
            require(meta['id'] == identity and meta['status'] in ('ready','misaligned','undetermined','blocked'), identity)
            counts[dataset][meta['status']] += 1
            require(re.fullmatch('[0-9a-f]{40}', meta['source']['commit']), f'{identity}: revision')
            require((project / 'formal/Main.lean').is_file(), f'{identity}: Main.lean')
            require(not meta['compiled_lean434'] or not meta['missing_modules'], f'{identity}: missing imports')
            if meta['status'] == 'ready':
                require(meta['compiled_lean434'] and meta['leantrace_extracted'], f'{identity}: ready without extraction')
            inventory = formal_files(project)
            require(len(inventory) == meta['formal']['file_count'], f'{identity}: source inventory')
            require(formal_digest(project) == meta['formal']['sha256'], f'{identity}: source tree changed')
            for filename, expected in inventory:
                relative = Path(filename)
                require(relative == Path('formal/Main.lean') or relative.parts[:2] == ('formal','dep'), 'Unsafe formal layout')
                raw = (project / relative).read_bytes()
                for module in IMPORT.findall(raw.decode()):
                    if module.startswith('dep.') or module == 'Main':
                        require((project / 'formal' / Path(*module.split('.')).with_suffix('.lean')).is_file(), f'{identity}: {module}')
                    elif module not in meta['external_imports']:
                        require(module in meta['missing_modules'], f'{identity}: unrecorded external import {module}')
            informal = [json.loads(line) for line in (project / 'informal.jsonl').read_text().splitlines()]
            require(len({i['id'] for i in informal}) == len(informal), f'{identity}: informal IDs')
            roots = target_roots(meta)
            targets = {(t['file'], t['declaration']) for t in meta['targets']}
            if meta.get('target_mode') == 'joint':
                informal_ids = {t['informal_id'] for t in meta['targets']}
                require(len(informal_ids) == 1 and None not in informal_ids,
                        f'{identity}: joint targets must share one informal')
                shared = [entry for entry in informal if entry['id'] in informal_ids]
                require(len(shared) == 1 and shared[0].get('target_mode') == 'joint',
                        f'{identity}: missing joint informal')
                require({(t['file'], t['declaration']) for t in shared[0]['targets']} == targets,
                        f'{identity}: incomplete joint informal binding')
            for entry in informal:
                require(entry['text'].strip(), f'{identity}: empty informal')
                for target in entry['targets']:
                    require((project / target['file']).is_file(), f'{identity}: informal target')
                    require(target['declaration'] in roots, f'{identity}: informal root')
            require(meta['input_sha256'] == input_digest(project), f'{identity}: input digest')
            require(meta['changes'] is None or (project / meta['changes']).is_file(), f'{identity}: changes note')
            for after in meta['after_ids']:
                require(after in metas and identity in metas[after]['before_ids'], f'{identity}: after link')
                require(meta['group_id'] == metas[after]['group_id'] and meta['split_group'] == metas[after]['split_group'], 'Pair group mismatch')
                links += 1
            for before in meta['before_ids']:
                require(before in metas and identity in metas[before]['after_ids'], f'{identity}: before link')
            total += 1
    print(json.dumps(dict(cases=total, before_after_pairs=links, datasets=counts), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['check', 'index'])
    args = parser.parse_args()
    config = read(CONFIG)
    if args.action == 'check':
        check(config)
    else:
        for dataset in {**config['datasets'], **config.get('review_datasets', {})}:
            write_index(dataset)


if __name__ == '__main__':
    main()
