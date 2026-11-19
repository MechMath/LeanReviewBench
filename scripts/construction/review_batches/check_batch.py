#!/usr/bin/env python3
"""Check review-batch inputs/receipts; optionally recheck local build graphs."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts/data'))
from project_cases import formal_digest, input_digest, target_roots


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch', required=True, choices=['qinz1yang', 'frenzymath'])
    parser.add_argument('--with-build-graphs', action='store_true',
                        help='Also require and validate ignored local extraction graphs')
    args = parser.parse_args()
    batch = ROOT / 'datasets' / args.batch
    index = read(batch / 'index.json')
    validation = read(batch / 'metadata/technical-validation.json')
    receipts = {r['project_id']: r for r in validation['records']}
    labels = [json.loads(line) for line in
              (batch / 'metadata/provisional-labels.jsonl').read_text().splitlines()]
    require(index['source_batch'] == args.batch, 'Source batch differs')
    require(not index['registered_release_inputs'], 'Pending batch marked human-reviewed')
    require(len(receipts) == len(index['projects']), 'Technical evidence coverage differs')
    metas = {}
    informals = {}
    for row in index['projects']:
        project = (ROOT / row['path']).resolve()
        require(project.is_relative_to(batch), 'Project escaped its source batch')
        meta = read(project / 'project.json')
        metas[meta['id']] = meta
        informals[meta['id']] = [json.loads(s) for s in
                                  (project / 'informal.jsonl').read_text().splitlines()]
        receipt = receipts[meta['id']]
        require(meta['source_batch'] == args.batch, 'Mixed source project')
        require(meta['source']['repository'].startswith('https://github.com/' + args.batch + '/'),
                'Mixed source repository')
        require(len(meta['source']['commit']) == 40 and all(c in '0123456789abcdef' for c in meta['source']['commit']), 'Revision is not pinned')
        require(meta['input_sha256'] == input_digest(project) == receipt['input_sha256'],
                'Input digest differs: ' + meta['id'])
        require(formal_digest(project) == meta['formal']['sha256'] == receipt['formal_source_sha256'],
                'Formal digest differs: ' + meta['id'])
        require(receipt['compilation'] == receipt['extraction'] == 'passed', 'Technical check failed')
        for name, digest in [('technical_receipt', 'technical_receipt_sha256'),
                             ('preservation_receipt', 'preservation_receipt_sha256')]:
            require(sha(ROOT / receipt[name]) == receipt[digest], 'Evidence digest differs: ' + name)
        compiled = read(ROOT / receipt['technical_receipt'])
        require(compiled['status'] == 'passed' and compiled['roots'] == target_roots(meta),
                'Compiler receipt root/status differs')
        require(compiled['graph_sha256'] == receipt['graph_sha256'],
                'Compiler receipt graph differs')
        require(set(compiled['sources']) == {
                    str(p.relative_to(project / 'formal'))
                    for p in (project / 'formal').rglob('*.lean')},
                'Compiler receipt source inventory differs')
        for filename, digest in compiled['sources'].items():
            source_path = (project / 'formal' / filename).resolve()
            require(source_path.is_relative_to(project / 'formal'),
                    'Compiler source escaped formal context')
            require(sha(source_path) == digest, 'Compiled source changed: ' + meta['id'])
        require(target_roots(meta) == receipt['roots'], 'Receipt roots differ')
        if args.with_build_graphs:
            require(sha(ROOT / receipt['graph_path']) == receipt['graph_sha256'],
                    'Local graph digest differs')
            graph = read(ROOT / receipt['graph_path'])
            require(graph['roots'] == target_roots(meta), 'Graph roots differ')
            nodes = {node['id'] for node in graph['nodes']}
            require(len(nodes) == len(graph['nodes']) == receipt['nodes'], 'Graph nodes differ')
            require(len(graph['edges']) == receipt['edges'], 'Graph edges differ')
            require(all(e['source'] in nodes and e['target'] in nodes and
                        e['site'] in ('type', 'definition_value', 'constructor_type')
                        for e in graph['edges']), 'Invalid graph dependency')
        require(not meta['human_adjudicated'] and not meta['reference_ready'] and
                meta['gold_label'] is None, 'Unsupported review claim')
    for label in labels:
        require(label['label'] in ('aligned', 'misaligned'), 'Invalid provisional label')
        require(label['review_status'] == 'agent_preliminary' and
                not label['human_adjudicated'] and not label['reference_ready'] and
                label['gold_label'] is None, 'Provisional label promoted to gold')
        require(label['input_sha256'] == receipts[label['project_id']]['input_sha256'],
                'Label input binding differs')
        require(label['roots'] == target_roots(metas[label['project_id']]), 'Label roots differ')
        require(label['formal_source_sha256'] == metas[label['project_id']]['formal']['sha256'],
                'Label formal digest differs')
    labeled = {label['project_id'] for label in labels}
    require(len(labeled) == len(labels), 'Duplicate provisional label')
    pending = {row['project_id'] for row in index['projects']
               if row['label_status'] == 'requires_human_scope_resolution'}
    pending_records = read(batch / 'metadata/pending-scope-reviews.json')
    require({r['project_id'] for r in pending_records} == pending and
            len(pending_records) == len(pending), 'Pending review inventory differs')
    require(all(r['label'] is None and
                r['input_sha256'] == receipts[r['project_id']]['input_sha256']
                for r in pending_records), 'Pending label/input binding differs')
    excluded = {row['project_id'] for row in index['projects']
                if row['label_status'] == 'excluded_partial_development'}
    if excluded:
        held = read(batch / 'metadata/held-development-records.json')['records']
        require({row['project_id'] for row in held} == excluded,
                'Excluded artifacts lack held-development evidence')
        require(all(row['label'] is None for row in held),
                'Excluded development artifacts retain active labels')
        require(all(row.get('benchmark_extraction_eligible') is False
                    for row in index['projects'] if row['project_id'] in excluded),
                'Excluded artifacts marked benchmark eligible')
    require(set(receipts) - labeled == pending | excluded,
            'Unexplained missing preliminary label')
    for identity, meta in metas.items():
        for following in meta['after_ids']:
            require(following in metas and identity in metas[following]['before_ids'],
                    'Non-reciprocal version link')
            require(meta['group_id'] == metas[following]['group_id'] and
                    meta['split_group'] == metas[following]['split_group'],
                    'Version pair lost its source group')
            for old, new in zip(informals[identity], informals[following], strict=True):
                require(old['text'] == new['text'] and old['source'] == new['source'],
                        'Independent target changed across paired versions')
        for previous in meta['before_ids']:
            require(previous in metas and identity in metas[previous]['after_ids'],
                    'Non-reciprocal predecessor link')
    print(json.dumps(dict(source_batch=args.batch, projects=len(receipts),
                          preliminary_labels=len(labels), status='passed',
                          graph_check='local_graphs_verified' if args.with_build_graphs
                          else 'persisted_receipt_bindings_only')))


if __name__ == '__main__':
    main()
