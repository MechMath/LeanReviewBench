#!/usr/bin/env python3
"""Build local, deterministic release directories from a pinned research checkout."""
import argparse
import csv
from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def encoded(obj):
    return (json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode()

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

class Research:
    def __init__(self, path):
        self.path = path
        self.commit = self.git('rev-parse', 'HEAD').decode().strip()
        self.archive = json.loads((path / 'metadata/provenance.json').read_text())['archive_commit']
        self.locations = {}
        self.cache = {}
    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.path), *args], stderr=subprocess.DEVNULL)
    def read(self, path, expected=None):
        path = str(path)
        if path in self.cache:
            raw, location = self.cache[path]
        elif (self.path / path).is_file():
            raw = (self.path / path).read_bytes()
            location = {'commit': self.commit, 'path': path}
        else:
            raw = self.git('show', self.archive + ':' + path)
            location = {'commit': self.archive, 'path': path}
        if expected and sha(raw) != expected:
            raise ValueError('Source hash mismatch: ' + path)
        self.locations[path] = dict(location, sha256=sha(raw))
        return raw
    def graph(self, directory, meta, derived):
        record = derived.get((directory.parents[1].name, meta['id']))
        if record:
            raw = self.read(record['graph_path'], record['graph_sha256'])
            return json.loads(raw), dict(self.locations[record['graph_path']], binding='verified_derived_graph')
        for relative in ['graph/default/graph.json', 'context/default/graph.json']:
            p = directory / relative
            if p.is_file():
                raw = self.read(p.relative_to(self.path))
                return json.loads(raw), dict(self.locations[str(p.relative_to(self.path))], binding='retained_project_graph')
        prep = meta.get('preparation', {})
        direct = prep.get('graph')
        if isinstance(direct, dict) and direct.get('url'):
            url = direct['url']; prefix='https://github.com/MechMath/PaperLeanBench/blob/'
            if not url.startswith(prefix):
                raise ValueError('Unexpected archive URL: '+url)
            commit, path = url[len(prefix):].split('/', 1)
            raw = self.git('show', commit + ':' + path)
            if direct.get('sha256') and sha(raw) != direct['sha256']:
                raise ValueError('Archived graph hash mismatch')
            return json.loads(raw), dict(commit=commit,path=path,sha256=sha(raw),binding='historical_graph')
        if isinstance(direct,str):
            raw = self.read(direct)
            return json.loads(raw), dict(self.locations[direct],binding='retained_preparation_graph')
        for key in ['packaged_receipt', 'receipt']:
            receipt = prep.get(key)
            if not isinstance(receipt,str):
                continue
            parent = str(Path(receipt).parent)
            for name in ['default-graph.json', 'default/graph.json']:
                candidate = parent+'/'+name
                try:
                    raw = self.read(candidate)
                except (subprocess.CalledProcessError,FileNotFoundError):
                    continue
                return json.loads(raw), dict(self.locations[candidate],binding='historical_packaged_graph' if key=='packaged_receipt' else 'historical_graph')
        raise ValueError('No actual exported context for '+str(directory))

class DirectoryWriter:
    def __init__(self, path):
        self.path = path
        path.mkdir(parents=True,exist_ok=False)
        self.members = []
    def add(self,name,raw):
        target=self.path/name
        target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():raise ValueError('Duplicate data file: '+name)
        target.write_bytes(raw)
        self.members.append(dict(path=name,size=len(raw),sha256=sha(raw)))
    def close(self):
        pass

# Types and definition values are already exporter-produced Lean expressions.
# Retain those bytes; exclude docstrings, source paths/ranges and all proofs.
def context(graph, roots):
    by = {n['id']:n for n in graph['nodes']}
    if len(by)!=len(graph['nodes']) or not set(roots)<=set(by):
        raise ValueError('Missing/duplicate graph declaration')
    nodes=[]
    for n in graph['nodes']:
        value=n.get('value')
        if n.get('proof_valued') or n.get('kind') in ['theorem','theorem_statement','axiom']:
            if value is not None:
                raise ValueError('Exporter included a proof body: '+n['id'])
        nodes.append({k:n[k] for k in ['id','kind','type','value','external','proof_valued','projection','internal','generated_kind'] if k in n})
    edges=graph['edges']
    for e in edges:
        if e['source'] not in by or e['target'] not in by:
            raise ValueError('Dangling graph edge')
        if e.get('site')=='definition_value' and by[e['source']].get('proof_valued'):
            raise ValueError('Proof dependency traversal')
    return dict(schema_version='leanreviewbench-context-1',roots=roots,
                nodes=sorted(nodes,key=lambda x:x['id']),edges=sorted(edges,key=lambda x:(x['source'],x['target'],x.get('site',''))),
                external_boundary=graph.get('policy','external library declarations are boundary nodes'))

def migrate(source,version):
    research=Research(source)
    if research.git('status','--porcelain').strip():
        raise ValueError('Research checkout must be clean; commit provenance would otherwise be misleading')
    sys.path.insert(0,str(source/'scripts/data'))
    import project_cases
    cfg=json.loads((source/'datasets/project-cases.json').read_text())
    derived={(r['dataset'],r['project_id']):r for r in json.loads((source/'metadata/derived-graphs/index.json').read_text())['records']}
    out=ROOT/'data'/version
    out.mkdir(parents=True,exist_ok=False)
    inputs=DirectoryWriter(out/'inputs');references=DirectoryWriter(out/'references');reproduction=DirectoryWriter(out/'reproduction')
    tasks=[];labels=[];provenance=[];contexts={};blobs=set();repro_projects=[];counts=Counter();graph_kinds=Counter()
    for batch in cfg['datasets']:
        records=[json.loads(l) for l in (source/'metadata/labels'/f'{batch}.jsonl').read_text().splitlines()]
        label_by={r['project_id']:r for r in records}
        for p in sorted((source/'datasets'/batch/'projects').glob('*/project.json')):
            d=p.parent;m=json.loads(p.read_text());identity=batch+':'+m['id'];label=label_by[m['id']]
            if project_cases.input_digest(d)!=m['input_sha256'] or label['input_sha256']!=m['input_sha256']:
                raise ValueError('Stale original binding: '+identity)
            task_id='lrb-'+sha((identity+'\0'+m['input_sha256']).encode())[:24]
            roots=[t['declaration'] for t in m['targets']]
            graph,binding=research.graph(d,m,derived);g=context(graph,roots);cid=sha(encoded(g))
            if cid not in contexts:
                inputs.add('contexts/'+cid+'.json',encoded(g));contexts[cid]=True
            informal=[json.loads(l) for l in (d/'informal.jsonl').read_text().splitlines()]
            main_ids={t.get('informal_id') for t in m['targets']}
            selected=[dict(id=r['id'],text=r['text']) for r in informal if r['id'] in main_ids]
            if not selected:
                raise ValueError('No selected independent target: '+identity)
            payload=dict(schema_version='leanreviewbench-input-1',task_id=task_id,roots=roots,informal=selected,context_id=cid,
                         environment=dict(lean_toolchain=cfg['lean_toolchain'],mathlib_commit=cfg['external_libraries']['mathlib']['commit'],cslib_commit=cfg['external_libraries']['cslib']['commit']))
            task_digest=sha(encoded(payload));tasks.append(payload)
            # The reference artifact is evaluator-only and retains original review state.
            labels.append(dict(task_id=task_id,payload_sha256=task_digest,original_input_sha256=m['input_sha256'],label=label['label'],original_record=label))
            provenance.append(dict(task_id=task_id,payload_sha256=task_digest,original_id=identity,original_input_sha256=m['input_sha256'],
                context_id=cid,graph_source=binding,source=m['source'],group_id=m['group_id'],split_group=m['split_group'],
                before_ids=m['before_ids'],after_ids=m['after_ids'],compiled_lean434=m.get('compiled_lean434',False),
                context_available=True,reference_ready=label.get('reference_ready',False),
                original_informal=informal,material_complete=m.get('material_complete'),source_revision_status=m.get('source_revision_status')))
            source_materials=[]
            for record in informal:
                source_info=record.get('source',{})
                for key in ['retained_path','evidence','text_evidence','excerpt_evidence']:
                    name=source_info.get(key)
                    if not isinstance(name,str):continue
                    relative=str((d/name).relative_to(source)) if key=='retained_path' else name
                    try:raw=research.read(relative)
                    except (subprocess.CalledProcessError,FileNotFoundError):continue
                    h=sha(raw)
                    if h not in blobs:
                        reproduction.add('blobs/'+h,raw);blobs.add(h)
                    source_materials.append(dict(informal_id=record['id'],source_field=key,original_locator=relative,blob_sha256=h))
            provenance[-1]['source_materials']=source_materials
            snapshot={}
            for f in sorted((d/'formal').rglob('*')):
                if not f.is_file():continue
                raw=f.read_bytes();h=sha(raw);snapshot[f.relative_to(d).as_posix()]=h
                if h not in blobs:
                    reproduction.add('blobs/'+h,raw);blobs.add(h)
            repro_projects.append(dict(task_id=task_id,original_id=identity,files=snapshot,project=m,informal=informal))
            # Preserve independent source copies/patches and compact receipts without graph duplicates.
            for folder in ['informal','informal-source','target','technical','compilation']:
                for f in sorted((d/folder).rglob('*')) if (d/folder).is_dir() else []:
                    if f.is_file() and not any(k in f.parts for k in ['graph','context','default','explicit','source']):
                        reproduction.add('evidence/'+task_id+'/'+f.relative_to(d).as_posix(),f.read_bytes())
            for f in d.glob('*.patch'):
                reproduction.add('evidence/'+task_id+'/'+f.name,f.read_bytes())
            for report_key in ['review_report']:
                rel=label.get(report_key)
                if rel:
                    try:raw=research.read(rel,label.get('review_report_sha256'))
                    except (subprocess.CalledProcessError,FileNotFoundError):continue
                    references.add('reviews/'+task_id+'.json',raw)
            counts[batch]+=1;graph_kinds[binding['binding']]+=1
    inputs.add('tasks.jsonl',b''.join(encoded(x) for x in tasks));inputs.close()
    references.add('labels.jsonl',b''.join(encoded(x) for x in labels));references.add('provenance.jsonl',b''.join(encoded(x) for x in provenance));references.close()
    reproduction.add('projects.jsonl',b''.join(encoded(x) for x in repro_projects));reproduction.add('environment.json',encoded(cfg));reproduction.close()
    manifest=dict(schema_version='leanreviewbench-release-2',version=version,stage='local-preview',source_repository='https://github.com/MechMath/PaperLeanBench',source_commit=research.commit,
                  inputs=len(tasks),contexts=len(contexts),labels=dict(Counter(r['label'] for r in labels)),batches=dict(counts),
                  reference_ready=sum(bool(r['original_record'].get('reference_ready')) for r in labels),graph_sources=dict(graph_kinds),
                  directories=[])
    for role,pack in [('inputs',inputs),('references',references),('reproduction',reproduction)]:
        manifest['directories'].append(dict(role=role,path=role,size=sum(m['size'] for m in pack.members),files=pack.members))
    release=ROOT/'releases'/version;release.mkdir(parents=True,exist_ok=False)
    (release/'manifest.json').write_bytes(encoded(manifest))
    with (release/'catalog.csv').open('w',encoding='utf-8',newline='') as stream:
        writer=csv.DictWriter(stream,lineterminator='\n',fieldnames=['task_id','original_id','original_input_sha256','payload_sha256','context_id','split_group'])
        writer.writeheader()
        for row in provenance:writer.writerow({key:row[key] for key in writer.fieldnames})
    migration=dict(source_commit=research.commit,input_count=len(tasks),formal_files=sum(len(p['files']) for p in repro_projects),unique_formal_blobs=len(blobs),
                   graph_contexts=len(contexts),omitted=['staging','excluded candidates','qwen experiment runs','duplicate graph formats','per-declaration graph files','old research history'],
                   source_locations=research.locations)
    (release/'migration-audit.json').write_bytes(encoded(migration))
    for name in ['LICENSE','NOTICE']:
        shutil.copy2(source/name,ROOT/name)
    shutil.copytree(source/'licenses',ROOT/'licenses',dirs_exist_ok=True)
    print(json.dumps({k:v for k,v in manifest.items() if k!='directories'},ensure_ascii=False,indent=2))
    for a in manifest['directories']:print(a['role'],round(a['size']/2**20,2),'MiB',len(a['files']),'files')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--source',type=Path,required=True);parser.add_argument('--version',required=True)
    args=parser.parse_args();migrate(args.source.resolve(),args.version)
