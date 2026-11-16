#!/usr/bin/env python3
"""Audit publication docs, configs, tools and runtime evidence without research access."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib
import urllib.parse

ROOT=Path(__file__).resolve().parents[1]
INVENTORY=Path('docs/support-inventory.json')
TREES=('docs','scripts','protocol','tests','tools','leanreviewbench')
FILES=('README.md','LICENSE','NOTICE','.gitignore','.gitattributes','.env.example','pyproject.toml','references/README.md','datasets/README.md','metadata/README.md')


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def support_files(root):
    files={root/name for name in FILES}
    for tree in TREES:
        files.update(p for p in (root/tree).rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc')
    files.discard(root/INVENTORY)
    return {p.relative_to(root).as_posix():sha(p) for p in sorted(files)}


def audit(root):
    errors=[]
    inventory=json.loads((root/INVENTORY).read_text())
    current=support_files(root)
    if current!=inventory['files_sha256']:
        changed=[k for k in current.keys()|inventory['files_sha256'].keys() if current.get(k)!=inventory['files_sha256'].get(k)]
        errors.append('Support inventory mismatch: '+', '.join(sorted(changed)[:12]))
    # These are publication guides, not hash-bound historical report documents.
    docs=[root/'README.md',root/'datasets/README.md',root/'references/README.md']
    for tree in ['docs','scripts','protocol','metadata','licenses']:
        docs.extend((root/tree).rglob('*.md'))
    docs.extend((root/'datasets').glob('*/README.md'))
    for path in docs:
        for target in re.findall(r'(?<!!)\[[^\]]*\]\(([^)]+)\)',path.read_text()):
            url=urllib.parse.urlsplit(target.strip('<>'))
            if url.scheme or not url.path:continue
            destination=(path.parent/urllib.parse.unquote(url.path)).resolve()
            if not destination.is_relative_to(root) or not destination.exists():
                errors.append(f'Broken local doc link: {path.relative_to(root)} -> {target}')
    python=[root/f for f in current if f.endswith('.py')]
    local={p.stem for p in python}|{'leanreviewbench'}
    for path in python:
        for node in ast.walk(ast.parse(path.read_text(),filename=str(path))):
            names=[]
            if isinstance(node,ast.Import):names=[a.name.split('.')[0] for a in node.names]
            elif isinstance(node,ast.ImportFrom) and not node.level and node.module:names=[node.module.split('.')[0]]
            for name in names:
                if name not in sys.stdlib_module_names and name not in local:
                    errors.append(f'Undeclared Python dependency: {path.relative_to(root)} -> {name}')
    tomllib.loads((root/'pyproject.toml').read_text())
    cfg=json.loads((root/'datasets/project-cases.json').read_text())
    expected=('leanprover/lean4:v4.34.1','d13f23b723b8a846827a245b89c10fc7d3f11612','7c8f6c0f67015df29b152fdcffaf7850db2e9185')
    pins=(cfg['lean_toolchain'],cfg['external_libraries']['mathlib']['commit'],cfg['external_libraries']['cslib']['commit'])
    if pins!=expected:errors.append('Shared environment pins differ from the reviewed publication')
    for name in ['.env.example','scripts/evaluation/.env.example','protocol/testing/.env.example']:
        for line in (root/name).read_text().splitlines():
            if '=' in line and not line.lstrip().startswith('#'):
                key,value=line.split('=',1)
                if any(word in key for word in ['KEY','TOKEN','SECRET']) and value.strip():errors.append('Nonempty secret template field: '+name)
    # All locally consumed reports are needed for current checks; omitted history
    # is represented by archive locators, never a hidden runtime dependency.
    required={}
    for path in (root/'metadata/labels').glob('*.jsonl'):
        for line in path.read_text().splitlines():
            row=json.loads(line)
            if row.get('review_report_sha256'):required[row['review_report']]=row['review_report_sha256']
    derived=json.loads((root/'metadata/derived-graphs/index.json').read_text())
    for row in derived['records']:
        required[row['graph_path']]=row['graph_sha256'];required[row['receipt_path']]=row['receipt_sha256']
    for name,expected in required.items():
        path=root/name
        if not path.is_file() or sha(path)!=expected:errors.append('Missing/changed runtime evidence: '+name)
    # Material paths are source provenance, not files required for evaluation.
    materials=json.loads((root/'metadata/materials/index.json').read_text())
    for row in materials['entries']:
        if row['status']=='archive_only':
            if not row.get('archive_url','').startswith('https://github.com/MechMath/PaperLeanBench/blob/'):errors.append('Unpinned archive material')
        elif row['status']=='local':
            path=root/row['path']
            if not path.is_file() or sha(path)!=row['sha256']:errors.append('Missing declared local source material: '+row['path'])
        else:errors.append('Undisclosed material status')
    return dict(support_files=len(current),local_doc_links_checked=True,python_imports_checked=True,
                required_evidence_files=len(required),source_material_locators=len(materials['entries']),errors=errors)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--freeze',action='store_true');a=p.parse_args()
    if a.freeze:
        document=dict(schema_version='paperlean-support-inventory-1',source_commit=json.loads((ROOT/'metadata/release.json').read_text())['source_commit'],
                      purpose='Required publication docs/configs/tools; generated after deliberate review, not an annotation approval.',files_sha256=support_files(ROOT))
        (ROOT/INVENTORY).write_text(json.dumps(document,ensure_ascii=False,indent=2)+'\n')
    result=audit(ROOT);print(json.dumps(result,ensure_ascii=False,indent=2));raise SystemExit(bool(result['errors']))
