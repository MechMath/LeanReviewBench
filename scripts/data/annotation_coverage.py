#!/usr/bin/env python3
"""Audit current labels and indexed evidence without promoting labels to gold."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
from paths import resolve

BASE = Path(__file__).resolve().parents[2]
NEW_BATCHES = {'arklib', 'imperial-flt', 'equational-theories', 'apap'}


def audit():
    config = json.loads((BASE / 'datasets/project-cases.json').read_text())
    rows, errors, warnings = [], [], []
    index=json.loads((BASE/'metadata/evidence/analysis/index.json').read_text())
    evidence={(r['dataset'],r['project_id']):r for r in index['records']}
    for batch in config['datasets']:
        projects = {p.parent.name: json.loads(p.read_text()) for p in
                    (BASE / 'datasets' / batch / 'projects').glob('*/project.json')}
        path = BASE / 'metadata/labels' / (batch + '.jsonl')
        records = [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []
        labels = {}
        counts = Counter()
        for record in records:
            identity = record['project_id']
            key = f'{batch}:{identity}'
            if identity in labels:
                errors.append(f'{key}: duplicate label')
            labels[identity] = record
            project = projects.get(identity)
            if project is None:
                errors.append(f'{key}: unregistered project')
                continue
            if record.get('dataset') != batch or record.get('input_sha256') != project['input_sha256']:
                errors.append(f'{key}: identity/input binding mismatch')
            if record.get('label') not in ('aligned', 'misaligned'):
                errors.append(f'{key}: binary label missing')
            if not record.get('reason', '').strip():
                (errors if batch in NEW_BATCHES else warnings).append(f'{key}: missing reason; historical source locator retained')
            expected_status = 'ready' if record.get('label') == 'aligned' else record.get('label')
            if project['status'] != expected_status and not (record.get('label') == 'aligned' and project['status'] == 'blocked'):
                errors.append(f'{key}: status mismatch')
            if project.get('alignment_reference') != path.relative_to(BASE).as_posix():
                errors.append(f'{key}: label locator mismatch')
            roots = [t['declaration'] for t in project['targets']]
            if project.get('target_mode') == 'joint':
                if record.get('roots') != roots or record.get('target_mode') != 'joint':
                    errors.append(f'{key}: joint root mismatch')
            elif record.get('root') not in roots:
                errors.append(f'{key}: root mismatch')
            counts[record['label']] += 1
            counts['human_adjudicated'] += record.get('human_adjudicated') is True
            counts['reference_ready'] += record.get('reference_ready') is True
            counts['evaluation_eligible'] += project.get('evaluation_eligible') is True
            binding=evidence.get((batch,identity),{})
            report_path=binding.get('path')
            report_hash=binding.get('sha256')
            if not (report_path and report_hash):
                errors.append(f'{key}: missing indexed analysis evidence')
            if report_path and report_hash:
                report = resolve(BASE,report_path)
                if not report.is_file() or hashlib.sha256(report.read_bytes()).hexdigest() != report_hash:
                    errors.append(f'{key}: review report hash mismatch')
                    continue
                data = json.loads(report.read_text())
                for field in ('dataset', 'project_id', 'input_sha256', 'label'):
                    if data.get(field) != record.get(field):
                        errors.append(f'{key}: review report {field} mismatch')
                roots = [t['declaration'] for t in project['targets']]
                if len(roots) > 1 and data.get('roots') != roots:
                    errors.append(f'{key}: multi-root review scope mismatch')
                counts['verified_review_reports'] += 1
        missing = sorted(set(projects) - set(labels))
        errors.extend(f'{batch}:{identity}: missing label' for identity in missing)
        rows.append(dict(dataset=batch, inputs=len(projects), labels=len(records),
                         missing_labels=missing, **{k: counts[k] for k in (
                             'aligned', 'misaligned', 'human_adjudicated',
                             'reference_ready', 'evaluation_eligible', 'verified_review_reports')}))
    keys = ['inputs', 'labels', 'aligned', 'misaligned',
            'human_adjudicated', 'reference_ready', 'evaluation_eligible', 'verified_review_reports']
    return dict(audited_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=BASE, text=True).strip(),
                meaning='Current human-reviewed label and indexed-evidence coverage; evaluation-export readiness is tracked separately.',
                totals={k: sum(r[k] for r in rows) for k in keys},
                new_batch_totals={k: sum(r[k] for r in rows if r['dataset'] in NEW_BATCHES) for k in keys},
                batches=rows, warnings=warnings, errors=errors)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    result = audit()
    print(json.dumps(result, ensure_ascii=False, indent=2))
    raise SystemExit(bool(result['errors']))
