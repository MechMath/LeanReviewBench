#!/usr/bin/env python3
"""Compile selected native inputs and extract fresh statement graphs with LeanTrace."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(BASE / 'scripts/data'))
from project_cases import input_digest, projects, read, require, sha, target_roots
from compile_projects import environment
from compiler import Compiler, write_json
from environment import resolve_lean, resolve_leantrace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dataset', required=True)
    parser.add_argument('--ids', nargs='+', required=True)
    parser.add_argument('--output', type=Path, default=BASE / 'build/extracted-projects')
    args = parser.parse_args()
    config = read(BASE / 'datasets/project-cases.json')
    require(args.dataset in config['datasets'], 'Unknown dataset')
    selected = [p for p in projects(args.dataset) if p.parent.name in args.ids]
    require(set(args.ids) == {p.parent.name for p in selected}, 'Unknown input ID')
    lean, bundle = resolve_lean(config), resolve_leantrace(config)
    libraries = environment(config)
    output = args.output.resolve()
    compiler = Compiler(lean, libraries, output / 'compile', 180, config)
    spec = importlib.util.spec_from_file_location('statement_graph_reader', bundle / 'graph.py')
    reader = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reader)
    exporter = (bundle / 'Export.lean').read_text()
    reports = []
    for path in selected:
        project = path.parent
        meta = read(path)
        require(input_digest(project) == meta['input_sha256'], 'Stale input digest: ' + project.name)
        compiled = compiler.project(args.dataset, project)
        require(compiled['status'] == 'passed', 'Compilation failed: ' + project.name)
        workspace = output / 'compile/projects' / args.dataset / project.name
        dest = output / 'graphs' / args.dataset / project.name
        dest.mkdir(parents=True, exist_ok=True)
        graph_path = dest / 'graph.json'
        roots = target_roots(meta)
        source = dest / 'Extract.lean'
        # Keep the exporter's imports in its header, then load the compiled input.
        source.write_text(exporter.replace('import Lean', 'import Lean\nimport Main', 1)
                          + '\n' + '\n'.join('#print axioms ' + root for root in roots)
                          + '\n#statement_graph [' + ', '.join(roots)
                          + '] modules ["Main", "dep"] to ' + json.dumps(str(graph_path)) + '\n')
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [workspace, *libraries])))
        proc = subprocess.run([str(lean), '-j', '1', str(source)], cwd=dest, env=env,
                              capture_output=True, text=True, timeout=300)
        (dest / 'extract.log').write_text(proc.stdout + proc.stderr)
        require(proc.returncode == 0, 'Extraction failed: ' + str(dest / 'extract.log'))
        graph = reader.read_graph(graph_path)
        require(graph['roots'] == roots, 'Extracted roots differ')
        report = dict(dataset=args.dataset, project_id=project.name, status='passed',
                      input_sha256=meta['input_sha256'], roots=roots,
                      lean_toolchain=config['lean_toolchain'],
                      exporter_sha256=sha((bundle / 'Export.lean').read_bytes()),
                      graph_reader_sha256=sha((bundle / 'graph.py').read_bytes()),
                      graph_sha256=sha(graph_path.read_bytes()),
                      nodes=len(graph['nodes']), edges=len(graph['edges']),
                      compilation=compiled, axioms_log=proc.stdout)
        write_json(dest / 'receipt.json', report)
        reports.append(report)
        print(json.dumps(report), flush=True)
    write_json(output / 'summary.json', reports)


if __name__ == '__main__':
    main()
