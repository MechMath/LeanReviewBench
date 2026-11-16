#!/usr/bin/env python3
"""Shared compiler for selected project-case closures and target declarations.

Requires the pinned Lean toolchain and a built Mathlib checkout. All build
artifacts and logs go to --output; dataset source directories stay untouched.
Identical modules with identical transitive imports share compilation artifacts.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import threading
import time
from lean_imports import IMPORT

BASE = Path(__file__).resolve().parents[2]


def digest(value):
    return hashlib.sha256(value).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)


def mathlib_provenance(mathlib, expected_commit):
    """Accept a pinned Git checkout or the archived source acquisition receipt."""
    git_root = subprocess.run(['git', '-C', str(mathlib), 'rev-parse', '--show-toplevel'],
                              capture_output=True, text=True)
    if git_root.returncode == 0 and Path(git_root.stdout.strip()).resolve() == mathlib:
        commit = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
        provenance = dict(commit=commit, source_acquisition='Git checkout')
    else:
        receipt = mathlib.with_name(mathlib.name + '-source.json')
        if not receipt.is_file():
            raise ValueError('Mathlib needs a pinned Git checkout or a sibling <directory>-source.json receipt')
        provenance = json.loads(receipt.read_text())
    if provenance.get('commit') != expected_commit:
        raise ValueError('Mathlib revision differs from the release manifest')
    return provenance


class Compiler:
    def __init__(self, lean, libraries, output, timeout, environment):
        self.lean, self.libraries, self.output = lean, libraries, output
        self.timeout, self.environment = timeout, environment
        self.guard = threading.Lock()
        self.locks = {}
        self.built = 0
        self.reused = 0

    def run(self, source, cwd, library, output, log):
        output.parent.mkdir(parents=True, exist_ok=True)
        log.parent.mkdir(parents=True, exist_ok=True)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [library, *self.libraries])))
        command = [str(self.lean), '-j', '1', '-o', str(output), str(source)]
        started = time.monotonic()
        with log.open('w') as stream:
            try:
                result = subprocess.run(command, cwd=cwd, env=env, stdout=stream,
                                        stderr=subprocess.STDOUT, timeout=self.timeout)
            except subprocess.TimeoutExpired as error:
                raise RuntimeError(f'Compilation timed out after {self.timeout}s; log: {log}') from error
        if result.returncode:
            raise RuntimeError(f'Lean exited {result.returncode}; log: {log}')
        return time.monotonic() - started

    def project(self, dataset, project):
        started = time.monotonic()
        formal = project / 'formal'
        meta = json.loads((project / 'project.json').read_text())
        workspace = self.output / 'projects' / dataset / project.name
        workspace.mkdir(parents=True, exist_ok=True)
        sources = {'.'.join(p.relative_to(formal).with_suffix('').parts): p
                   for p in formal.rglob('*.lean')}
        content = {m: p.read_bytes() for m, p in sources.items()}
        imports = {m: IMPORT.findall(raw.decode()) for m, raw in content.items()}
        dependencies = {m: [dep for dep in deps if dep in sources] for m, deps in imports.items()}
        keys, active = {}, set()

        def key(module):
            if module in active:
                raise ValueError(f'Import cycle at {module}')
            if module not in keys:
                active.add(module)
                payload = [self.environment, module, digest(content[module]),
                           [(dep, key(dep)) for dep in dependencies[module]]]
                keys[module] = digest(json.dumps(payload, ensure_ascii=False).encode())
                active.remove(module)
            return keys[module]

        done = set()
        result = dict(dataset=dataset, project_id=project.name, status='failed',
                      modules=len(sources), targets=[t['declaration'] for t in meta['targets']])
        current = None
        try:
            for module in sources:
                for dep in imports[module]:
                    if dep.startswith('dep.') and dep not in sources:
                        raise ValueError(f'Missing local module {dep}')
                key(module)

            def compile_module(module):
                nonlocal current
                if module in done:
                    return
                for dep in dependencies[module]:
                    compile_module(dep)
                current = module
                identity = keys[module]
                cache = self.output / 'cache' / identity
                relative = Path(*module.split('.')).with_suffix('.olean')
                artifact = cache / relative
                with self.guard:
                    lock = self.locks.setdefault(identity, threading.Lock())
                with lock:
                    # Only artifacts with a success receipt may be reused.
                    receipt = cache / 'success.json'
                    if not receipt.exists():
                        seconds = self.run(sources[module].relative_to(formal), formal, workspace,
                                           artifact, cache / 'compile.log')
                        write_json(receipt, dict(key=identity, module=module,
                                                source_sha256=digest(content[module]), seconds=seconds))
                        with self.guard:
                            self.built += 1
                    else:
                        with self.guard:
                            self.reused += 1
                destination = workspace / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                # Lean 4 also emits private/server companions needed by imports.
                for compiled in artifact.parent.glob(artifact.name + '*'):
                    link = destination.parent / compiled.name
                    if link.is_symlink() or link.exists():
                        link.unlink()
                    link.symlink_to(compiled)
                done.add(module)

            for module in sorted(sources, key=lambda m: (m == 'Main', m)):
                compile_module(module)
            current = 'target_check'
            probe = workspace / 'BenchmarkTargetCheck.lean'
            probe.write_text('import Main\n\n' + ''.join(
                '#check @' + t['declaration'] + '\n' for t in meta['targets']))
            self.run(probe.name, workspace, workspace, workspace / 'BenchmarkTargetCheck.olean',
                     workspace / 'target-check.log')
            result.update(status='passed', compiled_modules=len(done),
                          source_sha256=digest(json.dumps(sorted(keys.items())).encode()))
        except Exception as error:
            result.update(error=str(error), failed_module=current, compiled_modules=len(done))
        result['seconds'] = round(time.monotonic() - started, 3)
        write_json(workspace / 'result.json', result)
        return result
