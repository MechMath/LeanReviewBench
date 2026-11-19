#!/usr/bin/env python3
"""Link a curator-selected historical pair within one source dataset."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def read(path):
    return json.loads(path.read_text())


def write(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch', choices=['qinz1yang', 'frenzymath'], required=True)
    parser.add_argument('--before', required=True)
    parser.add_argument('--after', required=True)
    args = parser.parse_args()
    base = ROOT / 'datasets' / args.batch
    index = {r['project_id']: r for r in read(base / 'index.json')['projects']}
    old, new = index[args.before], index[args.after]
    assert old['candidate_id'] == new['candidate_id'], 'Different candidate families'
    paths = [ROOT / row['path'] for row in (old, new)]
    metas = [read(path / 'project.json') for path in paths]
    assert metas[0]['group_id'] == metas[1]['group_id'], 'Different source groups'
    assert metas[0]['source']['repository'] == metas[1]['source']['repository']
    targets = [[json.loads(line) for line in (p / 'informal.jsonl').read_text().splitlines()]
               for p in paths]
    for a, b in zip(*targets, strict=True):
        assert a['text'] == b['text'] and a['source'] == b['source'], 'Different informal targets'
    for m, field, identity in [(metas[0], 'after_ids', args.after),
                               (metas[1], 'before_ids', args.before)]:
        if identity not in m[field]:
            m[field].append(identity)
    for p, m in zip(paths, metas):
        write(p / 'project.json', m)
    pair_path = base / 'metadata/version-pairs.json'
    pairs = read(pair_path)
    if not any(p['before_id'] == args.before and p['after_id'] == args.after
               for p in pairs['pairs']):
        pairs['pairs'].append(dict(candidate_id=old['candidate_id'], before_id=args.before,
              after_id=args.after, group_id=metas[0]['group_id'],
              independent_informal_target_identical=True,
              independent_informal_bytes_identical=(
                  (paths[0] / 'informal.jsonl').read_bytes() ==
                  (paths[1] / 'informal.jsonl').read_bytes()),
              note='Explicit historical pair; successor is not automatically aligned.'))
        write(pair_path, pairs)
    print(json.dumps(dict(source_batch=args.batch, before=args.before, after=args.after)))


if __name__ == '__main__':
    main()
