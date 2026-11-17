#!/usr/bin/env python3
"""Restore the native project-case publication layout from a clean research snapshot."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
from research_source import Research
from release_scope import EXCLUDED_BATCH, apply_exclusions

ROOT=Path(__file__).resolve().parents[2]


def sha(raw):return hashlib.sha256(raw).hexdigest()

def write_json(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')


def migrate(source,output,research_revision):
    research=Research(source)
    if research.git('status','--porcelain').strip():raise ValueError('Research checkout must be clean')
    template=json.loads((ROOT/'metadata/release.json').read_text())
    if research.commit!=template['source_commit']:raise ValueError('Use the pinned source commit; publication updates require a deliberate new baseline')
    if output.exists():raise ValueError('Migration destination must be fresh')
    output.mkdir(parents=True)
    def copy(relative):
        target=output/('metadata/'+relative if relative.startswith('reports/') else relative);target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(source/relative,target)
    def tree(relative):
        shutil.copytree(source/relative,output/('metadata/'+relative if relative.startswith('reports/') else relative),ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
    cfg=json.loads((source/'datasets/project-cases.json').read_text())
    derived=json.loads((source/'metadata/derived-graphs/index.json').read_text())
    lookup={(r['dataset'],r['project_id']):r for r in derived['records']}
    for relative in ['datasets/project-cases.json','datasets/README.md','metadata/README.md','metadata/provenance.json','LICENSE','NOTICE']:
        copy(relative)
    for relative in ['metadata/labels','metadata/upstream-evidence','metadata/derived-graphs','licenses']:
        tree(relative)
    for name in ['project_cases.py','alignment_labels.py','derived_graphs.py','release_metadata.py','upstream_evidence.py','annotation_coverage.py','project_case_stats.py','provenance.py','check_release_candidate.py']:
        copy('scripts/data/'+name)
    for name in ['compile_projects.py','compiler.py','environment.py','lean_imports.py']:
        copy('scripts/construction/'+name)
    for relative in research.git('ls-files','-z','--','scripts/evaluation').decode().split('\0'):
        if relative:copy(relative)
    # Native derived graph validation needs the original receipts and, for joint
    # Stacks, archived component inputs/graphs. These remain outside active data.
    for record in derived['records']:
        copy(record['graph_path'])
        copy(record['receipt_path'])
        receipt=json.loads((source/record['receipt_path']).read_text())
        if receipt.get('schema_version')=='paperlean-composed-graph-receipt-1':
            copy(receipt['explicit_graph_path'])
            for component in receipt['components']:
                relative=str(Path(component['project_path']).parent)
                copy(relative+'/project.json')
                copy(relative+'/informal.jsonl')
                tree(relative+'/formal')
                copy(component['receipt_path'])
                for mode in ['default','explicit']:copy(component[mode]['path'])
    existing={r['graph_sha256']:r['graph_path'] for r in derived['records']}
    graph_records=[];counts=Counter();labels=Counter();formal_count=0
    for batch in cfg['datasets']:
        for name in ['README.md','index.csv']:copy('datasets/'+batch+'/'+name)
        label_rows=[json.loads(x) for x in (source/'metadata/labels'/f'{batch}.jsonl').read_text().splitlines()]
        labels.update(r['label'] for r in label_rows)
        for original in sorted((source/'datasets'/batch/'projects').glob('*/project.json')):
            relative=original.parent.relative_to(source)
            meta=json.loads(original.read_text())
            # Exact native files and resources, with directly readable Lean paths.
            # Graph formats are represented once through the retained graph index.
            keep={'project.json','informal.jsonl','formal'}
            if meta.get('changes'):keep.add(Path(meta['changes']).parts[0])
            for child in original.parent.iterdir():
                if child.name not in keep:continue
                dest=output/relative/child.name;dest.parent.mkdir(parents=True,exist_ok=True)
                if child.is_dir():shutil.copytree(child,dest)
                else:shutil.copy2(child,dest)
            formal_count+=sum(f.is_file() for f in (original.parent/'formal').rglob('*'))
            graph,binding=research.graph(original.parent,meta,lookup)
            raw=research.git('show',binding['commit']+':'+binding['path'])
            assert sha(raw)==binding['sha256'] and json.loads(raw)==graph
            h=sha(raw)
            if h not in existing:
                existing[h]='metadata/derived-graphs/retained/'+h+'.json'
                target=output/existing[h];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
            record=dict(dataset=batch,project_id=meta['id'],input_sha256=meta['input_sha256'],
                        roots=[t['declaration'] for t in meta['targets']],graph_path=existing[h],graph_sha256=h,
                        graph_source=binding,fresh_compilation=False)
            graph_records.append(record);counts[batch]+=1
        for label in label_rows:
            report=label.get('review_report');expected=label.get('review_report_sha256')
            if report and expected:
                try:raw=research.read(report,expected)
                except (FileNotFoundError,subprocess.CalledProcessError):
                    if expected:raise
                    continue
                target=output/'metadata'/report;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
    write_json(output/'metadata/derived-graphs/retained-index.json',dict(
        schema_version='paperlean-retained-graphs-1',purpose='Local access to exact historical graphs; no fresh compilation or semantic re-annotation.',records=graph_records))
    write_json(output/'metadata/release.json',dict(schema_version='paperlean-local-release-1',
        source_commit=research.commit,research_docs_commit=research.git('rev-parse',research_revision).decode().strip(),
        dataset_schema='paperlean-project-case-1',inputs=sum(counts.values()),batches=dict(counts),labels=dict(labels),
        formal_files=formal_count,reference_ready=0,
        model_export_status='Native project-case data; no frozen model task export is asserted.',
        packaging_policy='Test/runtime dependencies only; optional construction materials use immutable archive links.',
        omitted=['staging and excluded candidates','qwen experiment runs','per-declaration and duplicate graph encodings','build caches','optional original/ copies, source caches, patches and construction logs']))
    # Carry the reviewed release support files and configuration, not local settings.
    support=json.loads((ROOT/'metadata/support-inventory.json').read_text())
    for relative in [*support['files_sha256'],'metadata/support-inventory.json']:
        destination=output/relative;destination.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(ROOT/relative,destination)
    for relative in ['metadata/materials/index.json','metadata/README.md','metadata/labels/README.md','metadata/release.json','metadata/layout.json','licenses/README.md']:
        destination=output/relative;destination.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/relative,destination)
    # Diagnostic classifications are curated release metadata, independent of the
    # pinned construction snapshot. Preserve their standards and provenance.
    # Preserve the curated publication metadata layout and exact current evidence.
    # The pinned construction metadata above is used for source/input verification.
    shutil.rmtree(output/'metadata')
    shutil.copytree(ROOT/'metadata', output/'metadata')
    for batch in cfg['datasets']:
        if batch == EXCLUDED_BATCH:
            continue
        shutil.copy2(ROOT/'datasets'/batch/'README.md',output/'datasets'/batch/'README.md')
    # Keep deliberate release exclusions when rebuilding the pinned archive.
    apply_exclusions(output)
    # Reuse the original inventory contract and checks rather than a new schema.
    subprocess.run([sys.executable,'scripts/data/release_metadata.py','freeze'],cwd=output,check=True)
    subprocess.run([sys.executable,'scripts/data/check_release_candidate.py'],cwd=output,check=True,stdout=subprocess.DEVNULL)
    retained=json.loads((output/'metadata/release.json').read_text())
    print(json.dumps(dict(inputs=retained['inputs'],formal_files=retained['formal_files'],
                          labels=retained['labels'],graphs=retained['inputs']),indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--research-revision',default='origin/research/pending-repo-extraction-resume-2026-11-13')
    args=parser.parse_args();migrate(args.source.resolve(),args.output.resolve(),args.research_revision)
