#!/usr/bin/env python3
"""Optional project compilation and external tool resolution, separate from evaluation."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(BASE / 'scripts/data'))
from project_cases import IMPORT, projects, read, require, sha
import compiler as mod
from environment import resolve_lean, resolve_leantrace


def environment(config):
    """Resolve only explicitly configured external dependency locations."""
    libraries = []
    for name, spec in config['external_libraries'].items():
        value = os.environ.get(spec['path_env'])
        if not value:
            if name == 'cslib':
                continue
            raise ValueError('Set ' + spec['path_env'] + ' to the pinned ' + name + ' directory')
        path = Path(value).expanduser().resolve()
        require(path.is_dir(), f'{spec["path_env"]}: directory does not exist')
        if name == 'mathlib':
            try:
                mod.mathlib_provenance(path, spec['commit'])
            except ValueError:
                if (path/'.git').exists():
                    raise
                # A source/cache archive may have no .git or acquisition receipt.
                # Verify it against the pinned Mathlib checkout resolved by Cslib.
                cslib = os.environ.get(config['external_libraries']['cslib']['path_env'])
                require(cslib, 'Mathlib archive needs a source receipt or PAPERLEAN_CSLIB for byte verification')
                reference = Path(cslib).expanduser().resolve()/'.lake/packages/mathlib'
                revision = subprocess.check_output(['git','-C',str(reference),'rev-parse','HEAD'],text=True).strip()
                require(revision == spec['commit'], 'Reference Mathlib pin mismatch')
                require(subprocess.run(['git','-C',str(reference),'diff','--quiet','HEAD']).returncode == 0,
                        'Reference Mathlib has tracked modifications')
                files = subprocess.check_output(['git','-C',str(reference),'ls-files'],text=True).splitlines()
                for relative in files:
                    if relative.endswith('.lean') or relative in ('lean-toolchain','lake-manifest.json'):
                        require((path/relative).is_file() and sha((path/relative).read_bytes()) == sha((reference/relative).read_bytes()),
                                'Mathlib archive differs at '+relative)
        else:
            top = subprocess.check_output(['git','-C',str(path),'rev-parse','--show-toplevel'],text=True).strip()
            require(Path(top).resolve() == path, 'Cslib must be its own Git checkout')
            rev = subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
            require(rev == spec['commit'], 'Cslib revision differs from the pinned environment')
            require(subprocess.run(['git','-C',str(path),'diff','--quiet','HEAD']).returncode == 0,
                    'Cslib has tracked source modifications')
            lock = read(path/'lake-manifest.json')
            mathlib = next(p for p in lock['packages'] if p['name'] == 'mathlib')
            require(mathlib['rev'] == config['external_libraries']['mathlib']['commit'], 'Cslib Mathlib pin mismatch')
        require((path/'lean-toolchain').read_text().strip() == config['lean_toolchain'], f'{name}: toolchain mismatch')
        packages = path/'.lake/packages'
        candidates = [path, *sorted(packages.iterdir())] if packages.is_dir() else [path]
        for p in candidates:
            lib = p/'.lake/build/lib/lean'
            if lib.is_dir() and lib.resolve() not in libraries:
                libraries.append(lib.resolve())
    return libraries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['env', 'tools', 'compile'])
    parser.add_argument('--dataset')
    parser.add_argument('--ids', nargs='+')
    parser.add_argument('--output', type=Path, default=BASE / 'build/project-cases')
    args = parser.parse_args()
    config = read(BASE / 'datasets/project-cases.json')
    if args.action == 'env':
        print(os.pathsep.join(map(str, environment(config))))
    elif args.action == 'tools':
        print(json.dumps(dict(lean=str(resolve_lean(config)),
                              leantrace=str(resolve_leantrace(config))), indent=2))
    else:
        require(args.dataset in config['datasets'], 'Choose one of the registered project-case datasets')
        libraries = environment(config)
        selected = [p for p in projects(args.dataset) if not args.ids or p.parent.name in args.ids]
        require(selected and (not args.ids or set(args.ids) == {p.parent.name for p in selected}), 'Unknown or empty case selection')
        for p in selected:
            require(read(p)['compiled_lean434'], p.parent.name + ': historical compilation is blocked; not selected automatically')
            if 'Cslib' in read(p)['external_boundaries']:
                require(os.environ.get(config['external_libraries']['cslib']['path_env']), 'Set PAPERLEAN_CSLIB for this case')
        lean = resolve_lean(config)
        mod.IMPORT = IMPORT
        compiler = mod.Compiler(lean, libraries, args.output.resolve(), 180, config)
        results = [compiler.project(args.dataset, p.parent) for p in selected]
        mod.write_json(args.output / 'summary.json', results)
        print(json.dumps(results, indent=2))
        require(all(r['status'] == 'passed' for r in results), 'Compilation failed; inspect output logs')


if __name__ == '__main__':
    main()
