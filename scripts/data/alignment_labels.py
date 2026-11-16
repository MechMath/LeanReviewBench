"""Validate provisional review labels against their exact current project inputs."""
import json
from project_cases import target_roots


def verify(base):
    seen = set()
    for path in sorted((base / 'metadata/labels').glob('*.jsonl')):
        for line in path.read_text().splitlines():
            record = json.loads(line)
            dataset, identity = record['dataset'], record['project_id']
            if path.stem != dataset or any('/' in x or x in ('.', '..') for x in (dataset, identity)):
                raise ValueError('Invalid label project path')
            key = dataset, identity
            if key in seen:
                raise ValueError('Duplicate label binding')
            seen.add(key)
            project = json.loads((base / 'datasets' / dataset / 'projects' / identity / 'project.json').read_text())
            if record['input_sha256'] != project['input_sha256']:
                raise ValueError('Stale label input binding: ' + identity)
            if project.get('target_mode') == 'joint':
                if record.get('roots') != target_roots(project) or record.get('target_mode') != 'joint':
                    raise ValueError('Incomplete joint label binding: ' + identity)
            if record['label'] not in ('aligned', 'misaligned', 'undetermined'):
                raise ValueError('Invalid alignment label')
            if record.get('human_adjudicated') is not False or record.get('reference_ready') is not False:
                raise ValueError('Restored model reviews must remain provisional')
            if record['label'] != 'aligned' and project['status'] != record['label']:
                raise ValueError('Project status differs from review label: ' + identity)
            if project.get('alignment_reference') != str(path.relative_to(base)):
                raise ValueError('Missing project label locator: ' + identity)
    for path in (base / 'datasets').glob('*/projects/*/project.json'):
        project = json.loads(path.read_text())
        if project.get('alignment_reference') or project.get('status') == 'misaligned':
            if (path.parents[2].name, project['id']) not in seen:
                raise ValueError('Project has no review label: ' + project['id'])
    print(f'PASS: {len(seen)} provisional review labels bound to current inputs')
