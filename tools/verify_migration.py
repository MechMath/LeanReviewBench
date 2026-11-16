#!/usr/bin/env python3
"""Compare a local release with its exact research inputs, labels and source bytes."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from leanreviewbench import Dataset
from leanreviewbench.dataset import records,digest,encoded
from leanreviewbench.integrity import file_hash
from migrate import Research,context


def verify(source,data,manifest_path):
    research=Research(source);manifest=json.loads(manifest_path.read_text())
    assert manifest['source_commit']==research.commit,'Wrong source revision'
    dataset=Dataset(data);dataset.validate()
    provenance={r['original_id']:r for r in records(data/'references/provenance.jsonl')}
    labels={r['task_id']:r for r in records(data/'references/labels.jsonl')}
    reproduction={r['task_id']:r for r in records(data/'reproduction/projects.jsonl')}
    cfg=json.loads((source/'datasets/project-cases.json').read_text())
    derived={(r['dataset'],r['project_id']):r for r in json.loads((source/'metadata/derived-graphs/index.json').read_text())['records']}
    count=files=compiled=0;states=Counter()
    for batch in cfg['datasets']:
        original_labels={r['project_id']:r for r in records(source/'metadata/labels'/f'{batch}.jsonl')}
        for path in sorted((source/'datasets'/batch/'projects').glob('*/project.json')):
            meta=json.loads(path.read_text());identity=batch+':'+meta['id'];p=provenance[identity];task=dataset.task(p['task_id']);ref=labels[task['task_id']]
            assert ref['original_record']==original_labels[meta['id']],identity+' label changed'
            assert ref['original_input_sha256']==meta['input_sha256']
            assert ref['payload_sha256']==dataset.payload_hash(task['task_id'])
            roots=[t['declaration'] for t in meta['targets']];assert task['roots']==roots
            original_informal=list(records(path.parent/'informal.jsonl'));selected={t.get('informal_id') for t in meta['targets']}
            assert task['informal']==[dict(id=r['id'],text=r['text']) for r in original_informal if r['id'] in selected]
            graph,binding=research.graph(path.parent,meta,derived)
            assert task['formal_context']==context(graph,roots),identity+' graph normalization differs'
            restored=reproduction[task['task_id']];assert restored['project']==meta
            actual={f.relative_to(path.parent).as_posix():file_hash(f) for f in (path.parent/'formal').rglob('*') if f.is_file()}
            assert actual==restored['files'],identity+' source inventory differs'
            for h in actual.values():assert file_hash(data/'reproduction/blobs'/h)==h
            count+=1;files+=len(actual);compiled+=bool(meta.get('compiled_lean434'));states[ref['label']]+=1
    assert len(dataset)==count==len(labels)==len(provenance)==len(reproduction)==manifest['inputs']
    return dict(source_commit=research.commit,inputs=count,formal_files=files,compiled_in_original_source=compiled,
                labels_unchanged=True,informal_text_unchanged=True,normalized_contexts_match=True,all_source_bytes_match=True,
                labels=dict(states),contexts=dataset.validate()['contexts'])

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--source',type=Path,required=True);parser.add_argument('--data',type=Path,required=True);parser.add_argument('--manifest',type=Path,required=True)
    args=parser.parse_args();print(json.dumps(verify(args.source.resolve(),args.data.resolve(),args.manifest.resolve()),ensure_ascii=False,indent=2))
