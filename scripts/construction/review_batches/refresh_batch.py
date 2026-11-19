#!/usr/bin/env python3
"""Refresh batch review inventories without changing mathematical inputs."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch', required=True, choices=['qinz1yang', 'frenzymath'])
    batch = parser.parse_args().batch
    base = ROOT / 'datasets' / batch
    md = base / 'metadata'
    index = read(base / 'index.json')
    receipts = {r['project_id']: r for r in read(md / 'technical-validation.json')['records']}
    labels = {r['project_id']: r for r in map(json.loads,
              (md / 'provisional-labels.jsonl').read_text().splitlines())}
    records = []
    for row in index['projects']:
        project = ROOT / row['path']
        meta = read(project / 'project.json')
        receipt = receipts[meta['id']]
        records.append(dict(
            project_id=meta['id'], candidate_id=row['candidate_id'],
            source_commit=meta['source']['commit'],
            roots=[t['declaration'] for t in meta['targets']],
            independent_informal=str((project / 'informal.jsonl').relative_to(ROOT)),
            formal_context=str((project / 'formal/Main.lean').relative_to(ROOT)),
            input_sha256=meta['input_sha256'], formal_source_sha256=meta['formal']['sha256'],
            informal_record_sha256=sha(project / 'informal.jsonl'),
            provisional_label=labels.get(meta['id'], {}).get('label'),
            review_state=row['label_status'], declaration_slice=meta['formal']['declaration_slice'],
            preparation_status=meta.get('preparation_status', 'not_deferred'),
            proofs_erased=meta['formal']['proofs_erased'],
            migration_preservation=receipt['migrated_source_preservation'],
            nonproof_preservation=receipt['nonproof_definition_preservation'],
            original_environment_preservation=receipt['original_environment_preservation'],
            version_links=dict(before_ids=meta['before_ids'], after_ids=meta['after_ids'])))
    write(md / 'current-review-snapshot.json', dict(source_batch=batch, records=records,
          review_counts=dict(Counter(r['review_state'] for r in records))))
    write(md / 'human-review-queue.json', dict(source_batch=batch,
          review_status='agent_preliminary_pending_human',
          records=[r for r in records if r['review_state'] != 'excluded_partial_development'
                   and r['preparation_status'] != 'deferred_technical']))
    write(md / 'prepared-input-bindings.json', dict(source_batch=batch, records=[
          {k: r[k] for k in ('project_id', 'candidate_id', 'source_commit', 'roots',
                            'independent_informal', 'informal_record_sha256', 'input_sha256')}
          for r in records]))
    processing_path = md / 'retained-processing.json'
    if processing_path.exists():
        processing = read(processing_path)
        for family in processing['records']:
            versions = [r for r in records if r['candidate_id'] == family['candidate_id']]
            family['project_ids'] = [r['project_id'] for r in versions]
            family['versions'] = versions
            if versions:
                incomplete = any(not r['declaration_slice'] or not r['proofs_erased'] or
                                 'partial' in str(r['migration_preservation']).lower() or
                                 'partial' in str(r['nonproof_preservation']).lower()
                                 for r in versions)
                family['status'] = ('technical_work_remaining' if incomplete
                                    else 'prepared_pending_human_review')
                if len(versions) < family.get('expected_version_count', 1):
                    family['status'] = 'partial_versions_prepared'
                if any(r['preparation_status'] == 'deferred_technical' for r in versions):
                    family['status'] = 'deferred_technical'
        processing['prepared_family_count'] = sum(
            r['status'] == 'prepared_pending_human_review' for r in processing['records'])
        processing['status'] = ('prepared_pending_human_review'
            if processing['prepared_family_count'] == processing['candidate_count']
            else 'deferred_technical' if any(
                r['status'] == 'deferred_technical' for r in processing['records'])
            else 'in_progress')
        write(processing_path, processing)
    write(md / 'preparation-manifest.json', dict(source_batch=batch,
          status='inputs_pending_human_review_with_development_plans',
          files_sha256={str(p.relative_to(base)): sha(p)
                        for p in sorted(base.rglob('*')) if p.is_file()
                        and p != md / 'preparation-manifest.json'},
          deferred_plan_sha256=sha(md / 'deferred-development-plan.jsonl')))
    print(json.dumps(dict(source_batch=batch, projects=len(records),
                         human_review_queue=sum(r['review_state'] != 'excluded_partial_development'
                                                and r['preparation_status'] != 'deferred_technical'
                                                for r in records))))


if __name__ == '__main__':
    main()
