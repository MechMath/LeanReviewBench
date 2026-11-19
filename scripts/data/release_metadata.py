#!/usr/bin/env python3
"""Freeze or verify publication inputs, upstream evidence and provenance."""
import argparse
import hashlib
import json
from pathlib import Path

from upstream_evidence import verify as verify_evidence

BASE = Path(__file__).resolve().parents[2]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def inventory(base):
    excluded = {'metadata/manifest.json', 'metadata/README.md', 'datasets/README.md'}
    files = [p for tree in ('datasets', 'metadata', 'licenses')
             for p in sorted((base / tree).rglob('*')) if p.is_file()]
    files += [base / name for name in ('LICENSE', 'NOTICE') if (base / name).is_file()]
    # Unreviewed staging packets have an independent, explicit inventory.
    # Their addition must not refreeze the existing candidate's input hashes.
    return {p.relative_to(base).as_posix(): sha(p.read_bytes()) for p in files
            if p.relative_to(base).as_posix() not in excluded
            and p.relative_to(base).parts[:2] != ('datasets', 'staging')}


def verify_licenses(base, config):
    index = json.loads((base / 'licenses/index.json').read_text())
    if index.get('schema_version') != 'paperlean-license-index-1':
        raise ValueError('Unsupported license index')
    if set(index['datasets']) != set(config['datasets']):
        raise ValueError('License index must cover exactly the candidate batches')
    review = index.get('review_datasets', {})
    if set(review) != set(config.get('review_datasets', {})):
        raise ValueError('Review batch license coverage differs')
    expected_dirs = set(index['datasets']) | set(index['additional_sources']) | set(review)
    if {p.name for p in (base / 'licenses').iterdir() if p.is_dir()} != expected_dirs:
        raise ValueError('License directory scope differs from the license index')
    pending = []
    files = set()
    for dataset, record in index['datasets'].items():
        expected = set()
        for path in (base / 'datasets' / dataset / 'projects').glob('*/project.json'):
            source = json.loads(path.read_text())['source']
            expected.add((source['repository'], source['commit']))
        actual = {(r['repository'], r['commit']) for r in record['source_revisions']}
        if actual != expected:
            raise ValueError('License source revision inventory differs: ' + dataset)
        if record['status'] == 'historical-copy-pending':
            if record['license_files']:
                raise ValueError('Pending historical copy must not claim a verified license file')
            pending.append(dataset)
        elif record['status'] != 'license-copy-retained' or not record['license_files']:
            raise ValueError('Missing explicit license-copy status: ' + dataset)
    for batch, record in review.items():
        projects = {p.parent.name: json.loads(p.read_text())
                    for p in (base / 'datasets' / batch / 'projects').glob('*/project.json')}
        rows = record['projects']
        if len(rows) != len(projects) or {r['project_id'] for r in rows} != set(projects):
            raise ValueError('Review license/project coverage differs')
        for row in rows:
            meta = projects[row['project_id']]
            if (row['source_commit'] != meta['source']['commit'] or
                    row['repository'] != meta['source']['repository'] or
                    row['status'] != meta['licensing_status']):
                raise ValueError('Review license/source binding differs')
            if row['status'] == 'license-copy-retained':
                if not row['license_files']:
                    raise ValueError('Licensed input lacks retained copy')
            elif row['status'] != 'historical-license-scope-unresolved':
                raise ValueError('Unsupported pending license state')
        for item in record.get('notice_files', []):
            notice = base / item['file']
            if not notice.is_relative_to(base / 'licenses') or sha(notice.read_bytes()) != item['sha256']:
                raise ValueError('Pinned upstream notice differs')
    for record in [*index['datasets'].values(), *index['additional_sources'].values(),
                   *review.values()]:
        for item in record['license_files']:
            path = Path(item['file'])
            if path.is_absolute() or '..' in path.parts or not path.parts or path.parts[0] != 'licenses':
                raise ValueError('License file must remain inside licenses/')
            if not (base / path).is_file() or sha((base / path).read_bytes()) != item['sha256']:
                raise ValueError('License copy missing or changed: ' + item['file'])
            files.add(item['file'])
    actual_files = {p.relative_to(base).as_posix() for p in (base / 'licenses').rglob('LICENSE*') if p.is_file()}
    if actual_files != files:
        raise ValueError('Unindexed or missing license copies')
    print(f'PASS: {len(index["datasets"])} batch license records; {len(files)} license copies; '
          f'historical-copy gaps remain: {", ".join(sorted(pending)) or "none"}')


def verify(base):
    manifest = json.loads((base / 'metadata/manifest.json').read_text())
    if manifest.get('schema_version') != 'paperlean-candidate-manifest-1':
        raise ValueError('Unsupported candidate manifest')
    actual = inventory(base)
    if actual != manifest['files_sha256']:
        changed = sorted(k for k in actual.keys() | manifest['files_sha256'].keys()
                         if actual.get(k) != manifest['files_sha256'].get(k))
        raise ValueError('Candidate inventory/hash mismatch: ' + ', '.join(changed[:10]))
    provenance = json.loads((base / 'metadata/provenance.json').read_text())
    if provenance.get('schema_version') != 'paperlean-provenance-2':
        raise ValueError('Unsupported project provenance schema')
    config = json.loads((base / 'datasets/project-cases.json').read_text())
    verify_licenses(base, config)
    expected = {p.relative_to(base).as_posix() for dataset in config['datasets']
                for p in (base / 'datasets' / dataset / 'projects').glob('*/project.json')}
    expected.update(p.relative_to(base).as_posix()
                    for dataset in config.get('review_datasets', {})
                    for p in (base / 'datasets' / dataset / 'projects').glob('*/project.json'))
    bound = set()
    for key, binding in provenance['projects'].items():
        path = base / binding['project']
        project = json.loads(path.read_text())
        if sha(path.read_bytes()) != binding['project_sha256']:
            raise ValueError('Project provenance hash mismatch: ' + str(path))
        if {'label', 'reference_sha256'} & binding.keys():
            raise ValueError('Model labels must remain in the historical archive: ' + key)
        if project['input_sha256'] != binding['input_sha256']:
            raise ValueError('Input provenance binding mismatch: ' + key)
        if project.get('preparation', {}) != binding['archived_preparation']:
            raise ValueError('Historical provenance changed: ' + key)
        if binding['project'] in bound:
            raise ValueError('Duplicate project provenance: ' + binding['project'])
        bound.add(binding['project'])
    if bound != expected:
        raise ValueError('Project provenance inventory mismatch')
    verify_evidence(base, config)
    print(f'PASS: {len(bound)} project provenance bindings; '
          f'{len(actual)} frozen candidate files; upstream evidence verified')


def freeze(base):
    manifest = dict(schema_version='paperlean-candidate-manifest-1',
                    purpose='Publication candidate integrity, not a frozen evaluation task export',
                    files_sha256=inventory(base))
    (base / 'metadata/manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    verify(base)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['verify', 'freeze'])
    args = parser.parse_args()
    (verify if args.action == 'verify' else freeze)(BASE)
