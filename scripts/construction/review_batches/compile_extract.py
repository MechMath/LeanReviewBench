#!/usr/bin/env python3
"""Compile an already prepared statement context and freshly extract its graph.
Does not acquire informal targets, erase proofs, or certify preservation.
All outputs are caller-selected build artifacts; no dataset metadata is mutated.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

RELEASE = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(RELEASE / "scripts/construction"))
from compile_projects import environment
from environment import resolve_lean, resolve_leantrace
from compiler import Compiler, write_json

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--formal", type=Path, required=True)
    p.add_argument("--root", action="append", required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=300)
    a = p.parse_args()
    for root in a.root:
        if not re.fullmatch(r"[A-Za-z_][\w'.]*", root):
            p.error("Unsupported root identifier")
    formal, output = a.formal.resolve(), a.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    config = json.loads((RELEASE / "datasets/project-cases.json").read_text())
    receipt = dict(status="started", roots=a.root, original_proofs_certified=False,
                   statement_preservation="not_checked", nonproof_definition_preservation="not_checked")
    try:
        lean, bundle = resolve_lean(config), resolve_leantrace(config)
        libraries = environment(config)
        validation = json.loads((RELEASE / "metadata/validation.json").read_text())
        assert sha(bundle / "Export.lean") == validation["exporter_sha256"], "Exporter mismatch"
        assert sha(bundle / "graph.py") == validation["graph_reader_sha256"], "Graph reader mismatch"
        workspace = output / "compiled"
        workspace.mkdir(exist_ok=True)
        compiler = Compiler(lean, libraries, output, a.timeout, config)
        modules = {str(p.relative_to(formal).with_suffix("")).replace("/", "."): p
                   for p in formal.rglob("*.lean")}
        from lean_imports import IMPORT
        active, done = set(), set()
        def compile_module(module):
            if module in done:
                return
            if module in active:
                raise ValueError("Import cycle: " + module)
            active.add(module)
            for dep in IMPORT.findall(modules[module].read_text()):
                if dep in modules:
                    compile_module(dep)
                elif dep.startswith("dep."):
                    raise ValueError("Missing local dependency: " + dep)
            compiler.run(modules[module].relative_to(formal), formal, workspace,
                         workspace / Path(*module.split(".")).with_suffix(".olean"),
                         output / "logs" / (module + ".log"))
            active.remove(module)
            done.add(module)
        for module in sorted(modules, key=lambda m: (m == "Main", m)):
            compile_module(module)
        assert "Main" in done, "Missing Main.lean"
        graph_path = output / "graph.json"
        extract = output / "Extract.lean"
        extract.write_text((bundle / "Export.lean").read_text().replace(
            "import Lean", "import Lean\nimport Main", 1)
            + "\n" + "\n".join("#print axioms " + root for root in a.root)
            + "\n#statement_graph [" + ", ".join(a.root)
            + '] modules ["Main", "dep"] to ' + json.dumps(str(graph_path)) + "\n")
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [workspace, *libraries])))
        proc = subprocess.run([str(lean), "-j", "1", str(extract)], cwd=output, env=env,
                              text=True, capture_output=True, timeout=a.timeout)
        (output / "extract.log").write_text(proc.stdout + proc.stderr)
        assert proc.returncode == 0, "Extraction failed; see extract.log"
        spec = importlib.util.spec_from_file_location("statement_graph_reader", bundle / "graph.py")
        reader = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(reader)
        graph = reader.read_graph(graph_path)
        assert graph["roots"] == a.root, "Root mismatch"
        receipt.update(status="passed", compilation="passed", extraction="passed",
                       lean_toolchain=config["lean_toolchain"],
                       libraries=config["external_libraries"],
                       exporter_sha256=sha(bundle / "Export.lean"),
                       graph_reader_sha256=sha(bundle / "graph.py"),
                       graph_sha256=sha(graph_path), nodes=len(graph["nodes"]),
                       edges=len(graph["edges"]), local_nodes=sum(not n["external"] for n in graph["nodes"]),
                       sources={str(p.relative_to(formal)): sha(p) for p in formal.rglob("*.lean")},
                       axioms_log=proc.stdout)
    except Exception as exc:
        receipt.update(status="failed", error=str(exc))
    write_json(output / "receipt.json", receipt)
    print(json.dumps(receipt, ensure_ascii=False, indent=2))
    return 0 if receipt["status"] == "passed" else 1

if __name__ == "__main__":
    raise SystemExit(main())
