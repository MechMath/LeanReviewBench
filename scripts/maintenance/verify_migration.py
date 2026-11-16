#!/usr/bin/env python3
"""Compare native release input, label, source and graph bytes against research."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
from research_source import Research,sha
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.data.dataset import Dataset
from scripts.data.dataset import file_hash,records
from scripts.data.paths import resolve


def verify(source,release):
    research=Research(source);dataset=Dataset(release);dataset.validate()
    graphs=json.loads((release/'metadata/derived-graphs/retained-index.json').read_text())['records']
    count=compiled=0;labels=Counter()
    for batch in dataset.config['datasets']:
        relative=Path('metadata/labels')/(batch+'.jsonl')
        assert (release/relative).read_bytes()==(source/relative).read_bytes(),'Label bytes changed: '+batch
        labels.update(r['label'] for r in records(release/relative))
    for identity in dataset.ids():
        directory=dataset.directory(identity);relative=directory.relative_to(release);original=source/relative
        for name in ['project.json','informal.jsonl']:
            assert (directory/name).read_bytes()==(original/name).read_bytes(),identity+' '+name+' changed'
        expected={p.relative_to(original/'formal').as_posix():file_hash(p) for p in (original/'formal').rglob('*') if p.is_file()}
        actual={p.relative_to(directory/'formal').as_posix():file_hash(p) for p in (directory/'formal').rglob('*') if p.is_file()}
        assert actual==expected,identity+' formal sources/resources changed'
        count+=len(actual);compiled+=bool(dataset.project(identity)['project']['compiled_lean434'])
    for row in graphs:
        source_binding=row['graph_source'];raw=research.git('show',source_binding['commit']+':'+source_binding['path'])
        assert sha(raw)==row['graph_sha256']==file_hash(resolve(release,row['graph_path']))
    return dict(source_commit=research.commit,inputs=len(dataset),formal_files=count,compiled_in_original_source=compiled,
                project_metadata_bytes_unchanged=True,informal_records_bytes_unchanged=True,labels_bytes_unchanged=True,
                all_source_bytes_match=True,all_original_graph_bytes_match=True,graph_bindings=len(graphs),labels=dict(labels))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--source',type=Path,required=True);parser.add_argument('--release',type=Path,default=ROOT)
    args=parser.parse_args();print(json.dumps(verify(args.source.resolve(),args.release.resolve()),indent=2))
