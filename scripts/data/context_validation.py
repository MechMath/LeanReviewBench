"""Verify recorded context checks against released Lean inputs, without graphs."""
import json

from project_cases import formal_digest, input_digest, target_roots


def verify(base):
    document = json.loads((base / 'metadata/validation.json').read_text())
    config = json.loads((base / 'datasets/project-cases.json').read_text())
    if document.get('schema_version') != 'leanreviewbench-context-validation-1':
        raise ValueError('Unsupported context validation schema')
    if (document.get('proofs_erased') is not True or
            document.get('original_theorem_proofs_certified') is not False):
        raise ValueError('Invalid proof-erasure validation claim')
    pins = {name: item['commit'] for name, item in config['external_libraries'].items()}
    if (document.get('lean_toolchain') != config['lean_toolchain'] or
            document.get('external_libraries') != pins):
        raise ValueError('Context validation environment differs')
    projects = {(batch, path.parent.name): path.parent
                for batch in {**config['datasets'], **config.get('review_datasets', {})}
                for path in (base / 'datasets' / batch / 'projects').glob('*/project.json')}
    seen = set()
    for row in document['records']:
        identity = (row['dataset'], row['project_id'])
        if identity not in projects or identity in seen:
            raise ValueError('Unknown or duplicate context validation record')
        seen.add(identity)
        directory = projects[identity]
        meta = json.loads((directory / 'project.json').read_text())
        if (row['input_sha256'] != meta['input_sha256'] or
                row['input_sha256'] != input_digest(directory) or
                row['formal_sha256'] != formal_digest(directory)):
            raise ValueError('Stale context validation binding: ' + ':'.join(identity))
        if row['roots'] != target_roots(meta):
            raise ValueError('Context validation roots differ')
        for key in ('compilation', 'extraction', 'statement_preservation',
                    'nonproof_definition_preservation'):
            if row.get(key) != 'passed':
                raise ValueError('Missing successful context check: ' + key)
        if (meta.get('formal', {}).get('proofs_erased') is not True or
                meta.get('formal', {}).get('declaration_slice') is not True):
            raise ValueError('Context packaging flags differ')
        if row.get('evidence_path'):
            from hashlib import sha256
            evidence = base / row['evidence_path']
            raw = evidence.read_bytes()
            if sha256(raw).hexdigest() != row.get('evidence_sha256'):
                raise ValueError('Technical evidence digest differs')
            receipt = json.loads(raw)
            if any(receipt[k] != row[k] for k in
                   ('dataset', 'project_id', 'roots', 'input_sha256', 'formal_sha256')):
                raise ValueError('Technical evidence binding differs')
            if (receipt['lean_toolchain'] != document['lean_toolchain'] or
                    {name: item['commit'] for name, item in receipt['external_libraries'].items()} != pins or
                    receipt['exporter_sha256'] != document['exporter_sha256'] or
                    receipt['graph_reader_sha256'] != document['graph_reader_sha256']):
                raise ValueError('Technical evidence environment differs')
            sources = {str(p.relative_to(directory / 'formal')): sha256(p.read_bytes()).hexdigest()
                       for p in (directory / 'formal').rglob('*.lean')}
            if receipt['compiled_sources'] != sources:
                raise ValueError('Compiled source inventory differs')
    if seen != set(projects):
        raise ValueError('Context validation coverage differs')
    print(f'PASS: {len(seen)} input-bound context validation records; graphs generated on demand')
