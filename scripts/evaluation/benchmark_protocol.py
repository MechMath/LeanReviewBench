#!/usr/bin/env python3
"""Local task-package and process transport for statement-alignment systems."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parents[2]
VERSION = 'paperlean-protocol-1'
TASK_FILES = {'task.json', 'input.json', 'prediction.schema.json'}
INSTRUCTIONS = (
    'Assess whether the formal main theorem expresses the informal main theorem, '
    'interpreting all supplied definitions and structures. Check hypotheses, quantifiers, '
    'conclusions and definition/field constraints. Do not assess proofs. '
    'In full mode also check each supplied definition against its informal description. '
    'In theorem_only mode infer dependency meanings from Formal; hidden dependency '
    'descriptions are not assessment criteria. Report only discrepancies supported by '
    'the provided input. Use insufficient_information when necessary meaning or context '
    'is unavailable. formal_context supplies formal dependencies for interpretation, not '
    'additional informal assessment targets. Attribute issues to the main theorem or a '
    'supplied definition pair; do not assess auxiliary theorem proofs. '
    'Submit a JSON object matching prediction.schema.json.'
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(Path(path).read_text())


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8')


def write(path, value):
    Path(path).write_bytes(json_bytes(value))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strip_comments(text):
    """Remove nested Lean block/line comments while preserving strings and newlines."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(text):
        pair = text[i:i + 2]
        ch = text[i]
        if depth:
            if pair == '/-':
                depth += 1
                out.append('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append('\n' if ch == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(ch)
            i += 1
            if ch == '\\' and i < len(text):
                out.append(text[i])
                i += 1
            elif ch == '"':
                quoted = False
        elif pair == '/-':
            depth = 1
            out.append('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                break
            out.append(' ' * (end - i))
            i = end
        else:
            quoted = ch == '"'
            out.append(ch)
            i += 1
    require(depth == 0 and not quoted, 'Unterminated Lean comment or string')
    return '\n'.join(line.rstrip() for line in ''.join(out).splitlines()).strip()


def model_pair(pair, include_informal):
    formal = pair['formal']
    result = {'id': pair['id'], 'kind': pair['kind'],
              'formal': {k: strip_comments(v) if isinstance(v, str) else v
                         for k, v in formal.items()}}
    if include_informal:
        result['informal'] = pair['informal']['text']
        result['qualifications'] = [n['text'] for n in pair['qualifiers']]
    return result


REVIEW_VERSION = 'paperlean-review-1'


def read_reviews(path):
    if not path:
        return {}
    document = load(path)
    require(document['schema_version'] == REVIEW_VERSION, 'Unsupported review format')
    records = {}
    for record in document['records']:
        require(isinstance(record['task_id'], str) and record['task_id'].strip(), 'Invalid review task ID')
        key = (record['task_id'], record['mode'])
        require(key not in records, 'Duplicate review task/mode')
        require(record['mode'] == 'theorem_only', 'Review v1 supports theorem_only only')
        for field in ('task_sha256', 'input_sha256'):
            value = record[field]
            require(isinstance(value, str) and len(value) == 64 and
                    all(c in '0123456789abcdef' for c in value), 'Invalid review hash')
        require(type(record['reference_ready']) is bool, 'Invalid reference readiness')
        require(record['status'] in ('pending', 'reviewed', 'adjudicated', 'unresolved'),
                'Invalid review status')
        reviewers = record['reviews']
        require(isinstance(reviewers, list), 'Reviews must be a list')
        names = set()
        for review in reviewers:
            validate_judgement(review)
            require(review['reviewer'] not in names, 'Duplicate reviewer')
            names.add(review['reviewer'])
        label = record['label']
        if record['status'] == 'adjudicated':
            require(len(names) >= 2, 'Adjudication requires two independent reviews')
            validate_judgement(record['adjudication'])
            require(label in ('aligned', 'misaligned') and
                    record['adjudication']['verdict'] == label, 'Invalid adjudicated label')
        else:
            require(label is None and record['adjudication'] is None,
                    'Only adjudicated records may have labels')
        require(not record['reference_ready'] or record['status'] == 'adjudicated',
                'Ready references require adjudication')
        records[key] = record
    return records


def validate_judgement(judgement):
    require(isinstance(judgement['reviewer'], str) and judgement['reviewer'].strip(),
            'Missing reviewer identity')
    require(judgement['verdict'] in ('aligned', 'misaligned', 'insufficient_information'),
            'Invalid human verdict')
    require(isinstance(judgement['evidence'], str) and judgement['evidence'].strip(),
            'Missing review evidence')


def review_matches(record, task, input_sha256, task_sha256):
    return (record is not None and record['mode'] == task['mode'] and
            record['task_id'] == task['task_id'] and
            record['input_sha256'] == input_sha256 and record['task_sha256'] == task_sha256)


def task_content(package, mode):
    payload = {'main_theorem': model_pair(package['main_theorem'], True),
               'definitions': [model_pair(d, mode == 'full') for d in package['definitions']],
               'formal_context': model_context(package['formal_context']),
               'context': {'lean_toolchain': package.get('lean_toolchain', 'leanprover/lean4:v4.34.1'),
                           'standalone_lean': False, 'external_boundary': package['external_boundary']}}
    task = {'protocol_version': VERSION, 'task_id': package['root_id'], 'mode': mode,
            'task_type': 'statement_alignment', 'instructions': INSTRUCTIONS,
            'resources': [{'id': 'input', 'path': 'input.json',
                           'sha256': hashlib.sha256(json_bytes(payload)).hexdigest()},
                          {'id': 'output_schema', 'path': 'prediction.schema.json',
                           'sha256': digest(BASE / 'protocol/v1/prediction.schema.json')}],
            'execution': {'transport': 'local_process', 'isolation': 'adapter_managed',
                          'network_policy': 'forbidden', 'allowed_inputs': 'task_package_only'}}
    return task, payload


def export_tasks(args):
    output = Path(args.output)
    require(not output.exists(), 'Output already exists; choose a fresh directory')
    packages = [json.loads(line) for line in Path(args.packages).read_text().splitlines()]
    selected = args.sample
    if getattr(args, 'sample_file', None):
        selection = load(args.sample_file)
        require(selection['schema_version'] == 'paperlean-pilot-1', 'Unsupported pilot selection')
        require(selection['mode'] == args.mode, 'Pilot selection mode mismatch')
        selected = [row['task_id'] for row in selection['samples']]
        require(selected and len(set(selected)) == len(selected), 'Empty or duplicate pilot selection')
    if selected:
        requested = set(selected)
        packages = [p for p in packages if p['root_id'] in requested]
        require({p['root_id'] for p in packages} == requested, 'Unknown sample ID')
    require(packages, 'No tasks selected')
    require(len({p['root_id'] for p in packages}) == len(packages), 'Duplicate sample ID')
    reviews = read_reviews(getattr(args, 'reviews', None))
    prepared = []
    for p in packages:
        require(p['schema_version'] in ('paperlean-evaluation-1', 'paperlean-full-draft-2'),
                'Unsupported evaluation package version')
        validate_context(p['formal_context'], [p['main_theorem']] + p['definitions'])
        task, payload = task_content(p, args.mode)
        task_hash = hashlib.sha256(json_bytes(task)).hexdigest()
        record = reviews.get((p['root_id'], args.mode))
        if record is not None:
            require(review_matches(record, task, task['resources'][0]['sha256'], task_hash),
                    f'Stale review: {p["root_id"]}')
        if args.mode == 'theorem_only':
            ready = record is not None and record['reference_ready']
        else:
            ready = (p['reference_status']['full'] if 'reference_status' in p else
                     p['status']['reference_informal_complete'] and p['status']['informal_review_complete'])
        require(args.allow_draft or ready,
                f'Unreviewed/incomplete reference: {p["root_id"]}; use --allow-draft for development')
        prepared.append((task, payload, ready))
    output.mkdir(parents=True)
    index = []
    for task, payload, ready in prepared:
        sample = task['task_id']
        directory = output / hashlib.sha256(sample.encode()).hexdigest()[:24]
        directory.mkdir()
        write(directory / 'input.json', payload)
        shutil.copyfile(BASE / 'protocol/v1/prediction.schema.json', directory / 'prediction.schema.json')
        write(directory / 'task.json', task)
        index.append({'task_id': sample, 'directory': directory.name,
                      'task_sha256': digest(directory / 'task.json'), 'development_draft': not ready})
    index_document = {'protocol_version': VERSION, 'mode': args.mode,
                      'source_packages_sha256': digest(args.packages), 'tasks': index}
    if getattr(args, 'reviews', None):
        index_document['reviews_sha256'] = digest(args.reviews)
    write(output / 'index.json', index_document)
    print(f'Exported {len(index)} tasks to {output}')


def safe_file(directory, name):
    path = directory / name
    require(not path.is_symlink() and path.resolve().is_relative_to(directory.resolve()), 'Unsafe resource path')
    require(path.is_file(), f'Missing resource: {name}')
    return path


def model_context(context):
    return {'declarations': [
                {'id': d['id'], 'kind': d['kind'], 'module': d['module'],
                 'formal': {k: strip_comments(v) if isinstance(v, str) else v
                            for k, v in d['formal'].items()}}
                for d in context['declarations']],
            'external_nodes': [{k: strip_comments(n[k]) if k == 'type' else n[k]
                                for k in ('id', 'kind', 'module', 'type')}
                               for n in context['external_nodes']],
            'edges': [{k: e[k] for k in ('source', 'target', 'site')} for e in context['edges']]}


def validate_context(context, pairs):
    require(set(context) == {'declarations', 'external_nodes', 'edges'}, 'Invalid formal context fields')
    declarations, external, edges = (context[k] for k in ('declarations', 'external_nodes', 'edges'))
    ids = [d['id'] for d in pairs + declarations + external]
    require(len(set(ids)) == len(ids), 'Duplicate context declaration ID')
    internal = {d['id'] for d in pairs + declarations}
    known = set(ids)
    for d in declarations:
        require(set(d) == {'id', 'kind', 'module', 'formal'}, 'Unexpected context declaration fields')
        formal = d['formal']
        require(isinstance(formal['type'], str) and formal['type'].strip(), 'Missing context type')
        require(set(formal) <= {'type', 'value', 'source_fragment', 'statement_source',
                'standalone_module', 'proof_valued', 'projection', 'private', 'generated_kind'},
                'Unexpected context formal fields')
        if d['kind'] == 'theorem' or formal.get('proof_valued'):
            require(all(formal.get(k) is None for k in ('value', 'source_fragment', 'statement_source')),
                    'Context proof body leaked')
    for n in external:
        require(set(n) == {'id', 'kind', 'module', 'type'}, 'Unexpected boundary fields')
    for e in edges:
        require(set(e) == {'source', 'target', 'site'} and e['source'] in internal
                and e['target'] in known, 'Dangling or invalid context edge')
        require(e['site'] in ('type', 'definition_value', 'constructor_type'), 'Invalid dependency site')
    proof_ids = {d['id'] for d in pairs + declarations
                 if d['kind'] == 'theorem' or d['formal'].get('proof_valued')}
    require(all(e['source'] not in proof_ids or e['site'] != 'definition_value' for e in edges),
            'Proof dependency traversed')
    reachable = {pairs[0]['id']}
    while True:
        expanded = reachable | {e['target'] for e in edges if e['source'] in reachable}
        if expanded == reachable:
            break
        reachable = expanded
    require(reachable == known, 'Formal context closure is disconnected')


def validate_task(directory):
    directory = Path(directory)
    require({p.name for p in directory.iterdir()} == TASK_FILES, 'Unexpected task package files')
    task = load(safe_file(directory, 'task.json'))
    require(task['protocol_version'] == VERSION, 'Unsupported protocol')
    require(task['task_type'] == 'statement_alignment', 'Unsupported task type')
    require(task['mode'] in ('full', 'theorem_only'), 'Unsupported mode')
    require(len(task['resources']) == 2, 'Unexpected resources')
    resources = {r['id']: r for r in task['resources']}
    require(set(resources) == {'input', 'output_schema'}, 'Unexpected resource IDs')
    require(resources['input']['path'] == 'input.json' and
            resources['output_schema']['path'] == 'prediction.schema.json', 'Unexpected resource paths')
    for resource in resources.values():
        require(digest(safe_file(directory, resource['path'])) == resource['sha256'], 'Resource hash mismatch')
    payload = load(directory / 'input.json')
    require(payload['main_theorem']['id'] == task['task_id'], 'Root identity mismatch')
    pairs = [payload['main_theorem']] + payload['definitions']
    validate_context(payload['formal_context'], pairs)
    require(len({p['id'] for p in pairs}) == len(pairs), 'Duplicate declaration ID')
    for p in pairs:
        require('alignment_label' not in p and 'preparation_status' not in p, 'Preparation metadata leaked')
    if task['mode'] == 'theorem_only':
        require(all('informal' not in d and 'qualifications' not in d for d in payload['definitions']),
                'Hidden dependency Informal leaked')
    return task, payload


def validate_prediction(prediction, task, payload):
    require(isinstance(prediction, dict), 'Prediction must be an object')
    require(set(prediction) == {'task_id', 'verdict', 'issues', 'summary'}, 'Unexpected prediction fields')
    require(prediction['task_id'] == task['task_id'], 'Wrong task ID')
    require(isinstance(prediction['verdict'], str), 'Verdict must be a string')
    require(prediction['verdict'] in ('aligned', 'misaligned', 'insufficient_information'), 'Invalid verdict')
    require(isinstance(prediction['summary'], str) and bool(prediction['summary'].strip()), 'Missing summary')
    issues = prediction['issues']
    require(isinstance(issues, list), 'Issues must be an array')
    require(prediction['verdict'] != 'misaligned' or bool(issues), 'Misaligned requires an issue')
    require(prediction['verdict'] != 'aligned' or not issues, 'Aligned must have no issues')
    known = {d['id'] for d in [payload['main_theorem']] + payload['definitions']}
    for issue in issues:
        require(isinstance(issue, dict) and set(issue) == {'declaration_id', 'category', 'explanation'}, 'Invalid issue fields')
        require(isinstance(issue['declaration_id'], str) and issue['declaration_id'] in known, 'Unknown declaration ID')
        require(isinstance(issue['category'], str), 'Issue category must be a string')
        require(issue['category'] in ('hypothesis', 'quantifier', 'definition', 'structure_constraint', 'conclusion', 'other'), 'Invalid issue category')
        require(isinstance(issue['explanation'], str) and bool(issue['explanation'].strip()), 'Empty explanation')
    return prediction


def run_task(args):
    task_dir = Path(args.task).resolve()
    task, payload = validate_task(task_dir)
    task_sha256 = digest(task_dir / 'task.json')
    output = Path(args.output).resolve()
    require(not output.exists(), 'Run directory already exists')
    require(not output.is_relative_to(task_dir), 'Run directory must be outside the task package')
    require(args.timeout > 0, 'Timeout must be positive')
    command = list(args.command)
    if command and command[0] == '--':
        command.pop(0)
    require(command, 'Provide an adapter command after --')
    output.mkdir(parents=True)
    workspace = output / 'task'
    workspace.mkdir()
    for name in sorted(TASK_FILES):
        shutil.copyfile(safe_file(task_dir, name), workspace / name)
    require(digest(workspace / 'task.json') == task_sha256, 'Task changed while copying')
    validate_task(workspace)
    # The process adapter receives paths via environment; stdout is diagnostic only.
    submission = output / 'submission.json'
    env = dict(os.environ, PAPERLEAN_TASK_DIR=str(workspace),
               PAPERLEAN_SUBMISSION_PATH=str(submission), PAPERLEAN_TIMEOUT_SECONDS=str(args.timeout))
    receipt = {'protocol_version': VERSION, 'task_id': task['task_id'], 'mode': task['mode'],
               'command': command, 'task_sha256': task_sha256,
               'timeout_seconds': args.timeout, 'isolation': 'adapter_managed',
               'network_restriction_enforced_by_runner': False,
               'started_at_unix': time.time()}
    start = time.monotonic()
    with (output / 'stdout.log').open('wb') as stdout, (output / 'stderr.log').open('wb') as stderr:
        try:
            process = subprocess.Popen(command, cwd=workspace, env=env, stdout=stdout, stderr=stderr,
                                       start_new_session=True)
            try:
                receipt['exit_code'] = process.wait(timeout=args.timeout)
                receipt['status'] = 'completed' if process.returncode == 0 else 'execution_failed'
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                receipt['status'] = 'timeout'
        except OSError as error:
            receipt['status'] = 'execution_failed'
            receipt['error'] = str(error)
    receipt['elapsed_seconds'] = time.monotonic() - start
    if receipt['status'] == 'completed':
        try:
            require(digest(workspace / 'task.json') == receipt['task_sha256'], 'Task modified during execution')
            validate_task(workspace)
            require(not submission.is_symlink(), 'Submission must not be a symlink')
            prediction = validate_prediction(load(submission), task, payload)
            write(output / 'prediction.json', prediction)
        except (ValueError, OSError, KeyError, TypeError) as error:
            receipt['status'] = 'invalid_submission'
            receipt['error'] = str(error)
    write(output / 'run.json', receipt)
    print(json.dumps(receipt, indent=2))
    return 0 if receipt['status'] == 'completed' else 1


def adapter_identity(command, fingerprint_files=(), adapter_version=None):
    """Fingerprint local launch files and public effective provider settings."""
    executable = shutil.which(command[0])
    require(executable, 'Adapter executable not found')
    require('/' not in command[0] or Path(command[0]).is_absolute(),
            'Adapter executable paths must be absolute')
    paths = {Path(executable).resolve()}
    adapter = (BASE / 'scripts/evaluation/responses_llm.py').resolve()
    adapter_index = next((i for i, arg in enumerate(command)
                          if Path(arg).is_file() and Path(arg).resolve() == adapter), None)
    excluded = set()
    settings = None
    if adapter_index is not None:
        spec = importlib.util.spec_from_file_location('responses_adapter', adapter)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        options = module.argument_parser().parse_args(command[adapter_index + 1:])
        require(all(p.is_absolute() for p in (options.config, options.env_file) if p),
                'Adapter configuration paths must be absolute')
        _, endpoint, model, effort = module.settings(options)
        settings = {'endpoint': endpoint, 'model': model, 'reasoning_effort': effort,
                    'max_output_tokens': options.max_output_tokens, 'store': False,
                    'max_input_bytes': options.max_input_bytes}
        excluded = {p.expanduser().resolve() for p in (options.config, options.env_file) if p}
    for arg in command[1:]:
        path = Path(arg)
        if path.is_file() and path.resolve() not in excluded:
            require(path.is_absolute(), 'Adapter file arguments must use absolute paths')
            paths.add(path.resolve())
    for path in fingerprint_files:
        path = Path(path).expanduser().resolve()
        require(path.is_file() and path not in excluded, 'Invalid extra fingerprint file')
        paths.add(path)
    return {'files': [{'path': str(p), 'sha256': digest(p)} for p in sorted(paths)],
            'settings': settings, 'declared_version': adapter_version}


def run_batch(args):
    tasks_dir = Path(args.tasks).resolve()
    index_path = tasks_dir / 'index.json'
    index = load(index_path)
    require(index['protocol_version'] == VERSION, 'Unsupported task index')
    command = list(args.command)
    if command and command[0] == '--':
        command.pop(0)
    require(command and args.timeout > 0, 'Command and positive timeout required')
    identity = adapter_identity(command, args.fingerprint_file, args.adapter_version)
    entries = index['tasks']
    require(entries and len({e['task_id'] for e in entries}) == len(entries), 'Empty or duplicate task inventory')
    require(len({e['directory'] for e in entries}) == len(entries), 'Duplicate task directory')
    validated = []
    for entry in entries:
        directory = tasks_dir / entry['directory']
        require(not directory.is_symlink() and directory.resolve().is_relative_to(tasks_dir), 'Unsafe task directory')
        task, payload = validate_task(directory)
        require(task['task_id'] == entry['task_id'] and task['mode'] == index['mode'], 'Index task identity mismatch')
        require(digest(directory / 'task.json') == entry['task_sha256'], 'Index task hash mismatch')
        validated.append((entry, directory, task, payload))
    output = Path(args.output).resolve()
    require(not output.is_relative_to(tasks_dir), 'Batch output must be outside task export')
    config = {'protocol_version': VERSION, 'index_sha256': digest(index_path),
              'command': command, 'timeout_seconds': args.timeout,
              'runner_sha256': digest(__file__), 'adapter_identity': identity}
    if output.exists():
        require(args.resume, 'Batch already exists; use --resume')
        require(load(output / 'batch.json') == config, 'Resume configuration differs')
    else:
        require(not args.resume, 'No batch exists to resume')
        output.mkdir(parents=True)
        write(output / 'batch.json', config)
    # A lock prevents concurrent writers; a crash may require manual lock removal.
    lock = output / '.running'
    descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    os.close(descriptor)
    try:
        from collections import Counter
        statuses, verdicts = Counter(), Counter()
        predictions = []
        elapsed = 0.0
        for entry, directory, task, payload in validated:
            require(adapter_identity(command, args.fingerprint_file, args.adapter_version) == identity,
                    'Adapter or configuration changed during batch')
            run_dir = output / entry['directory']
            if run_dir.exists():
                require(args.resume and (run_dir / 'run.json').is_file(),
                        f'Incomplete run requires inspection: {run_dir}')
            else:
                run_task(argparse.Namespace(task=str(directory), output=str(run_dir),
                                           command=command, timeout=args.timeout))
            receipt = load(run_dir / 'run.json')
            require(receipt['task_sha256'] == entry['task_sha256'] and
                    receipt['task_id'] == task['task_id'] and receipt['command'] == command and
                    receipt['timeout_seconds'] == args.timeout, 'Stored run configuration differs')
            statuses[receipt['status']] += 1
            elapsed += receipt['elapsed_seconds']
            if receipt['status'] == 'completed':
                prediction = validate_prediction(load(run_dir / 'prediction.json'), task, payload)
                predictions.append(prediction)
                verdicts[prediction['verdict']] += 1
        with (output / 'predictions.jsonl').open('w') as stream:
            for prediction in predictions:
                stream.write(json.dumps(prediction, ensure_ascii=False) + '\n')
        summary = {'tasks': len(entries), 'execution_statuses': dict(statuses),
                   'verdict_counts': dict(verdicts), 'execution_seconds': elapsed,
                   'completed_fraction': statuses['completed'] / len(entries),
                   'development_tasks': sum(bool(e['development_draft']) for e in entries),
                   'semantic_scoring_performed': False}
        write(output / 'summary.json', summary)
        print(json.dumps(summary, indent=2))
        return 0 if statuses['completed'] == len(entries) else 1
    finally:
        lock.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    export = sub.add_parser('export')
    export.add_argument('--packages', required=True, help='Explicit evaluation JSONL with complete formal context')
    export.add_argument('--output', required=True)
    export.add_argument('--mode', choices=('full', 'theorem_only'), default='full')
    selection = export.add_mutually_exclusive_group()
    selection.add_argument('--sample', action='append')
    selection.add_argument('--sample-file', help='Versioned pilot selection JSON')
    export.add_argument('--allow-draft', action='store_true')
    export.add_argument('--reviews', help='Private, hash-bound human review document')
    run = sub.add_parser('run')
    run.add_argument('--task', required=True)
    run.add_argument('--output', required=True)
    run.add_argument('--timeout', type=float, default=300)
    run.add_argument('command', nargs=argparse.REMAINDER)
    batch = sub.add_parser('batch')
    batch.add_argument('--tasks', required=True)
    batch.add_argument('--output', required=True)
    batch.add_argument('--timeout', type=float, default=300)
    batch.add_argument('--resume', action='store_true')
    batch.add_argument('--fingerprint-file', action='append', default=[],
                       help='Additional adapter dependency to hash; repeat as needed')
    batch.add_argument('--adapter-version', help='Declared version of external adapter dependencies')
    batch.add_argument('command', nargs=argparse.REMAINDER)
    validate = sub.add_parser('validate')
    validate.add_argument('--task', required=True)
    validate.add_argument('--submission')
    args = parser.parse_args()
    try:
        if args.action == 'export':
            export_tasks(args)
        elif args.action == 'batch':
            return run_batch(args)
        elif args.action == 'run':
            return run_task(args)
        else:
            task, payload = validate_task(args.task)
            if args.submission:
                validate_prediction(load(args.submission), task, payload)
            print('Valid')
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
