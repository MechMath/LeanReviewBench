"""Validate concise human-reviewed labels against their exact project inputs."""
import json
from project_cases import target_roots

LABEL_FIELDS = {
    'task_id', 'dataset', 'project_id', 'input_sha256', 'root', 'roots',
    'target_mode', 'label', 'reason', 'review_scope', 'review_status',
    'human_adjudicated', 'reference_ready', 'gold_label',
}


def verify(base):
    seen = set()
    for path in sorted((base / 'metadata/labels').glob('*.jsonl')):
        for line in path.read_text().splitlines():
            record = json.loads(line)
            if set(record) - LABEL_FIELDS:
                raise ValueError('Unexpected label fields: ' + ', '.join(sorted(set(record) - LABEL_FIELDS)))
            if not isinstance(record.get('reason'), str) or not isinstance(record.get('review_scope'), str) or not record['review_scope'].strip():
                raise ValueError('Labels require an English reason and explicit review scope')
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
            if record.get('human_adjudicated') is not True or record.get('review_status') != 'human_reviewed':
                raise ValueError('Release labels must record completed human review')
            if record.get('reference_ready') is not False or record.get('gold_label') is not None:
                raise ValueError('Human review must not silently change export/reference readiness')
            if record['label'] != 'aligned' and project['status'] != record['label']:
                raise ValueError('Project status differs from review label: ' + identity)
            if project.get('alignment_reference') != str(path.relative_to(base)):
                raise ValueError('Missing project label locator: ' + identity)
    for path in (base / 'datasets').glob('*/projects/*/project.json'):
        project = json.loads(path.read_text())
        if project.get('alignment_reference') or project.get('status') == 'misaligned':
            if (path.parents[2].name, project['id']) not in seen:
                raise ValueError('Project has no review label: ' + project['id'])
    print(f'PASS: {len(seen)} human-reviewed labels bound to current inputs')
    from analysis_evidence import verify as verify_analysis
    verify_analysis(base)
