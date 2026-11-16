"""Apply approved batch exclusions to a publication tree, including rebuilds."""
from collections import Counter
import json
import shutil


EXCLUDED_BATCH = 'stat-learning-theory'


def apply_exclusions(root):
    """Remove the excluded SLT batch without modifying retained input records."""
    def update(relative, edit):
        path = root / relative
        if path.exists():
            obj = json.loads(path.read_text())
            edit(obj)
            path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')

    for relative in ['datasets/project-cases.json', 'licenses/index.json',
                     'metadata/upstream-evidence/index.json']:
        update(relative, lambda obj: obj['datasets'].pop(EXCLUDED_BATCH, None))
    update('metadata/provenance.json', lambda obj: obj.update(projects={
        key: value for key, value in obj['projects'].items()
        if not value['project'].startswith('datasets/' + EXCLUDED_BATCH + '/')}))
    for relative in ['metadata/derived-graphs/index.json',
                     'metadata/derived-graphs/retained-index.json']:
        path = root / relative
        if path.exists():
            obj = json.loads(path.read_text())
            removed = [row for row in obj['records'] if row['dataset'] == EXCLUDED_BATCH]
            obj['records'] = [row for row in obj['records'] if row['dataset'] != EXCLUDED_BATCH]
            # Delete only evidence exclusively used by the removed records.
            remaining = {row.get(key) for row in obj['records']
                         for key in ['graph_path', 'receipt_path']}
            for row in removed:
                for key in ['graph_path', 'receipt_path']:
                    name = row.get(key)
                    if name and name not in remaining:
                        target = root / ('metadata/' + name if name.startswith('reports/') else name)
                        target.unlink(missing_ok=True)
            path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')
    def prune_materials(obj):
        obj['entries'] = [row for row in obj['entries'] if row['dataset'] != EXCLUDED_BATCH]
        obj['counts'] = dict(Counter(row['status'] for row in obj['entries']))
    update('metadata/materials/index.json', prune_materials)
    for relative in ['datasets/' + EXCLUDED_BATCH, 'licenses/' + EXCLUDED_BATCH]:
        path = root / relative
        if path.exists():
            shutil.rmtree(path)
    (root / 'metadata/labels' / (EXCLUDED_BATCH + '.jsonl')).unlink(missing_ok=True)
    (root / 'metadata/upstream-evidence' / (EXCLUDED_BATCH + '.jsonl')).unlink(missing_ok=True)
    def refresh_release(obj):
        obj['batches'].pop(EXCLUDED_BATCH, None)
        obj['inputs'] = sum(obj['batches'].values())
        labels = Counter()
        for path in (root / 'metadata/labels').glob('*.jsonl'):
            labels.update(json.loads(line)['label'] for line in path.read_text().splitlines() if line)
        obj['labels'] = dict(labels)
        obj['formal_files'] = sum(path.is_file() for path in (root / 'datasets').glob('*/projects/*/formal/**/*'))
        obj['excluded_batches'] = {EXCLUDED_BATCH: {
            'repository': 'YuanheZ/lean-stat-learning-theory',
            'inputs': 1,
            'reason': 'Excluded by curator decision: full historical migration remains incomplete; statement-only context recovery does not qualify this batch for the retained release.'}}
    update('metadata/release.json', refresh_release)
    # Remove empty directories left by deletion of batch-only graph evidence.
    for tree in ['metadata/reports', 'metadata/derived-graphs']:
        for path in sorted((root / tree).rglob('*'), reverse=True):
            if path.is_dir() and not any(path.iterdir()):
                path.rmdir()
