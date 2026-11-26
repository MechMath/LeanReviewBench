#!/usr/bin/env python3
"""Report registered project-case batches; counts are derived without Lean or network."""
import argparse
from collections import Counter
import json
from pathlib import Path

from upstream_evidence import read_index, read_records
from project_cases import target_roots

BASE = Path(__file__).resolve().parents[2]


def collect():
    config = json.loads((BASE / 'datasets/project-cases.json').read_text())
    batches = []
    evidence_index = read_index(BASE)
    for dataset in config['datasets']:
        metas = {p.parent.name: json.loads(p.read_text()) for p in
                 sorted((BASE / 'datasets' / dataset / 'projects').glob('*/project.json'))}
        evidence = read_records(BASE, dataset, evidence_index['datasets'][dataset])
        linked = {p['project_id'] for record in evidence for p in record['projects']}
        compiled = [m for m in metas.values() if m['compiled_lean434'] and m['leantrace_extracted']]
        pairs = [(identity, after) for identity, m in metas.items() for after in m['after_ids']]
        for before, after in pairs:
            assert before in metas[after]['before_ids'], (dataset, before, after)
        status = Counter(m.get('historical_status', m['status']) for m in metas.values())
        batches.append(dict(batch=dataset,
            roots=len({root for m in metas.values() for root in target_roots(m)}),
            compiled_roots=len({root for m in compiled for root in target_roots(m)}),
            inputs=len(metas), compiled_inputs=len(compiled),
            upstream_records=len(evidence), inputs_with_evidence=len(linked),
            inputs_without_evidence=len(metas)-len(linked),
            historical_ready=status['ready'], historical_unresolved=status['undetermined'], blocked=status['blocked'],
            pairs=len(pairs), paired_inputs=len({v for pair in pairs for v in pair}),
            extracted_pairs=sum(metas[a]['compiled_lean434'] and metas[a]['leantrace_extracted'] and
                                metas[b]['compiled_lean434'] and metas[b]['leantrace_extracted'] for a, b in pairs)))
    totals = {key: sum(row[key] for row in batches) for key in batches[0] if key != 'batch'}
    totals['unpaired_inputs'] = totals['inputs'] - totals['paired_inputs']
    labels = Counter(json.loads(line)['label']
                     for path in (BASE / 'metadata/labels').glob('*.jsonl')
                     for line in path.read_text().splitlines())
    added_inputs = sum(1 for batch in config.get('review_datasets', {})
                       for _ in (BASE / 'datasets' / batch / 'projects').glob('*/project.json'))
    return dict(batches=batches, totals=totals, scoring_labels=0,
                total_retained_inputs=totals['inputs'] + added_inputs,
                total_retained_batches=len(config['datasets']) + len(config.get('review_datasets', {})),
                human_reviewed_labels=dict(labels),
                provisional_labels=dict(labels),
                total_task_snapshots=totals['inputs'],
                total_project_directories=totals['inputs'])


def markdown(data):
    lines = ['# Registered project-case batch statistics', '',
        'Generated from `datasets/project-cases.json`, registered project metadata and',
        '`metadata/evidence/upstream/`. The tables below cover the original-release partition.', '',
        f"The original-release partition contains **{data['total_task_snapshots']} versioned inputs**",
        f"in **{data['total_project_directories']} project directories**.", '',
        f"Overall: {data['total_retained_inputs']} retained versions across {data['total_retained_batches']} batches, with {data['human_reviewed_labels'].get('aligned', 0)} aligned and {data['human_reviewed_labels'].get('misaligned', 0)} misaligned labels. The two added batches are human reviewed and are outside the original-release tables below.", '',
        'Reproduce: `python3 scripts/data/project_case_stats.py > docs/STATISTICS.md`.',
        'Machine-readable output: `python3 scripts/data/project_case_stats.py --json`.', '',
        '`Roots` counts distinct declaration names within each repository; renamed',
        'before/after declarations count separately. This is not a deduplicated count',
        'of independent mathematical cases. `group_id` groups related inputs and can',
        'also combine multiple mathematical roots, so it is not a case count either.',
        'Human-reviewed binary annotations are retained in `metadata/labels/`.',
        'Upstream statements are unverified claims,',
        'including scope changes; linked inputs do not automatically inherit a verdict.', '',
        '| Batch | Roots | Extracted roots | Inputs | Upstream records | Linked inputs | No retained evidence | Pairs |',
        '| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |']
    keys = ['roots', 'compiled_roots', 'inputs', 'upstream_records', 'inputs_with_evidence', 'inputs_without_evidence', 'pairs']
    for row in data['batches'] + [dict(batch='Total', **data['totals'])]:
        lines.append('| ' + row['batch'] + ' | ' + ' | '.join(str(row[k]) for k in keys) + ' |')
    lines += ['', '| Batch | Compiled/extracted inputs | Historical ready | Historical unresolved | Historical blocked | Both-extracted pairs |',
              '| --- | ---: | ---: | ---: | ---: | ---: |']
    for row in data['batches'] + [dict(batch='Total', **data['totals'])]:
        lines.append('| ' + row['batch'] + ' | ' + ' | '.join(str(row[k]) for k in
                     ['compiled_inputs', 'historical_ready', 'historical_unresolved', 'blocked', 'extracted_pairs']) + ' |')
    t = data['totals']
    lines += ['', f"The {t['pairs']} explicit reciprocal before/after links cover {t['paired_inputs']} inputs;",
              f"{t['unpaired_inputs']} inputs have no registered pair. Pairs include text-only revisions,",
              'renamed declarations and scope changes; after does not imply a successful repair.', '',
              'Historical status values use `historical_status` where a review updated `status`. In particular,',
              '`ready` formerly included a provisional model decision; it is not a current scoring',
              'or semantic approval. Use the compilation/extraction flags for technical counts.',
              'No retained upstream evidence means this pass kept no sufficiently explicit statement;',
              'it does not establish that none exists anywhere upstream.', '']
    return '\n'.join(lines)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args()
    data = collect()
    print(json.dumps(data, ensure_ascii=False, indent=2) if args.json else markdown(data), end='\n' if args.json else '')
