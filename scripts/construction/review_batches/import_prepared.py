#!/usr/bin/env python3
"""Import a compiled input into a source-specific dataset awaiting review.

Requires explicit prepared-input metadata, fresh graph and preservation receipts.
Does not register release inputs or infer semantic labels from a repair direction.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts/data'))
from project_cases import formal_digest, formal_files, input_digest


def read(path):
    return json.loads(path.read_text())


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def path(value):
    result = (ROOT / value).resolve()
    if not result.is_relative_to(ROOT):
        raise ValueError('Preparation resource escaped repository')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', type=Path, required=True)
    args = parser.parse_args()
    spec = read(args.spec)
    batch = spec['source_batch']
    if batch not in ('qinz1yang', 'frenzymath'):
        raise ValueError('Unknown source batch')
    base = ROOT / 'datasets' / batch
    identity = spec['id']
    if Path(identity).name != identity:
        raise ValueError('Invalid project identity')
    destination = base / 'projects' / identity
    if destination.exists():
        raise ValueError('Input already exists; update and rebind deliberately: ' + identity)
    formal = path(spec['formal_directory'])
    informal_path = path(spec['informal_record_path'])
    informal = read(informal_path)
    compile_path = path(spec['compile_receipt'])
    preservation_path = path(spec['preservation_receipt'])
    compile_receipt = read(compile_path)
    preservation_receipt = read(preservation_path)
    if 'fail' in preservation_receipt['status'].lower():
        raise ValueError('Preservation receipt reports failure')
    graph_path = path(spec['graph_path'])
    graph = read(graph_path)
    roots = spec['roots']
    if compile_receipt['status'] != 'passed' or compile_receipt['roots'] != roots:
        raise ValueError('Compilation/root check failed')
    if graph['roots'] != roots or sha(graph_path) != compile_receipt['graph_sha256']:
        raise ValueError('Graph/root check failed')
    if compile_receipt['lean_toolchain'] != 'leanprover/lean4:v4.34.1':
        raise ValueError('Wrong toolchain')
    for name, expected in compile_receipt['sources'].items():
        if sha(formal / name) != expected:
            raise ValueError('Source changed after compilation: ' + name)
    if not spec['source']['repository'].startswith('https://github.com/' + batch + '/'):
        raise ValueError('Source repository belongs to another batch')
    if not informal.get('text') or not informal.get('source', {}).get('sha256'):
        raise ValueError('Independent informal text/source digest required')
    if not spec.get('informal_bound_before_slice'):
        raise ValueError('Informal must be bound before slicing')
    # Build all metadata before publishing the input directory.
    targets = [dict(file='formal/Main.lean', declaration=r, informal_id='main') for r in roots]
    informal.update(id='main', targets=[dict(file=t['file'], declaration=t['declaration'],
                                           relation='candidate_correspondence') for t in targets])
    meta = dict(id=identity, schema_version='paperlean-project-case-1', source_batch=batch,
                targets=targets, source=spec['source'], group_id=spec['group_id'],
                split_group=spec['source']['repository'].removeprefix('https://github.com/'),
                before_ids=[], after_ids=[], status='undetermined',
                compiled_lean434=True, leantrace_extracted=True, packaged_compilation='passed',
                missing_modules=[], external_imports=spec.get('external_imports', ['Mathlib']),
                external_boundaries=['Mathlib', 'Lean', 'Std', 'Init'],
                target_mode='joint' if len(roots) > 1 else 'single', changes='CHANGES.md',
                human_adjudicated=False, reference_ready=False, gold_label=None,
                evaluation_eligible=False, registered_release_input=False,
                licensing_status=spec['licensing_status'],
                original_toolchain=spec['original_toolchain'],
                lean_toolchain=compile_receipt['lean_toolchain'],
                technical_status=spec['technical_status'])
    assessment = read(path(spec['assessment_path']))
    label = assessment.get('label', assessment.get('agent_provisional_label'))
    if label not in ('aligned', 'misaligned', None):
        raise ValueError('Invalid preliminary label')
    if assessment.get('human_adjudicated') or assessment.get('reference_ready'):
        raise ValueError('Unsupported human/gold claim')
    shutil.copytree(formal, destination / 'formal')
    (destination / 'informal.jsonl').write_text(json.dumps(informal, ensure_ascii=False) + '\n')
    shutil.copyfile(path(spec['changes_path']), destination / 'CHANGES.md')
    meta['formal'] = dict(file_count=len(formal_files(destination)), sha256=formal_digest(destination),
                          declaration_slice=spec['declaration_slice'],
                          proofs_erased=spec.get('proofs_erased', True))
    if not meta['formal']['proofs_erased']:
        meta['formal']['proof_erasure_status'] = spec.get('proof_erasure_status', 'partial')
    if not spec['declaration_slice']:
        meta['formal']['module_support_closure'] = True
    write(destination / 'project.json', meta)
    meta['input_sha256'] = input_digest(destination)
    write(destination / 'project.json', meta)
    evidence = base / 'metadata/technical-evidence' / identity
    evidence.mkdir(parents=True, exist_ok=True)
    original_compile, original_preservation = compile_path, preservation_path
    for original, filename in [(original_compile, 'compilation.json'),
                                (original_preservation, 'preservation.json')]:
        compact = {k: value for k, value in read(original).items()
                   if k not in {'checked_log', 'stderr', 'stdout', 'axioms_log'}}
        compact.update(original_receipt_locator=str(original.relative_to(ROOT)),
                       original_receipt_sha256=sha(original))
        write(evidence / filename, compact)
    compile_path, preservation_path = evidence / 'compilation.json', evidence / 'preservation.json'
    validation_path = base / 'metadata/technical-validation.json'
    validation = read(validation_path)
    validation['records'].append(dict(project_id=identity, input_sha256=meta['input_sha256'],
        formal_source_sha256=meta['formal']['sha256'], roots=roots, compilation='passed',
        extraction='passed', graph_sha256=sha(graph_path), nodes=len(graph['nodes']),
        edges=len(graph['edges']), local_nodes=sum(not n['external'] for n in graph['nodes']),
        lean_toolchain=compile_receipt['lean_toolchain'],
        exporter_sha256=compile_receipt['exporter_sha256'],
        graph_reader_sha256=compile_receipt['graph_reader_sha256'],
        migrated_source_preservation=spec['migrated_source_preservation'],
        nonproof_definition_preservation=spec['nonproof_definition_preservation'],
        original_environment_preservation='not_checked', original_proofs_certified=False,
        technical_receipt=str(compile_path.relative_to(ROOT)), technical_receipt_sha256=sha(compile_path),
        preservation_receipt=str(preservation_path.relative_to(ROOT)),
        preservation_receipt_sha256=sha(preservation_path), graph_path=str(graph_path.relative_to(ROOT)),
        preservation_receipt_status=preservation_receipt['status']))
    write(validation_path, validation)
    annotation = dict(dataset=batch, project_id=identity, candidate_id=spec['candidate_id'],
        input_sha256=meta['input_sha256'], roots=roots, label=label, reason=assessment['reason'],
        review_scope=assessment.get('scope', assessment.get('review_scope', spec['review_scope'])),
        review_status='agent_preliminary', human_adjudicated=False, reference_ready=False,
        gold_label=None, formal_source_sha256=meta['formal']['sha256'],
        informal_record_sha256=sha(destination / 'informal.jsonl'))
    if label is None:
        pending_path = base / 'metadata/pending-scope-reviews.json'
        pending = read(pending_path) if pending_path.exists() else []
        pending.append(annotation)
        write(pending_path, pending)
        review_state = 'requires_human_scope_resolution'
    else:
        with (base / 'metadata/provisional-labels.jsonl').open('a') as stream:
            stream.write(json.dumps(annotation, ensure_ascii=False) + '\n')
        review_state = 'agent_preliminary_pending_human'
    index_path = base / 'index.json'
    index = read(index_path)
    index['projects'].append(dict(project_id=identity, candidate_id=spec['candidate_id'],
        path=str(destination.relative_to(ROOT)), input_sha256=meta['input_sha256'],
        label_status=review_state))
    write(index_path, index)
    print(json.dumps(dict(project_id=identity, source_batch=batch, label=label,
                          input_sha256=meta['input_sha256'])))


if __name__ == '__main__':
    main()
