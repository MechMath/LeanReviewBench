"""Binary development scoring against explicitly loaded provisional references."""
from collections import Counter
import json
from pathlib import Path
from .dataset import records, require


def score(dataset,predictions_path,reference_path,allow_provisional=False,allow_partial=False):
    refs={}
    for r in records(reference_path):
        require(r['task_id'] not in refs,'Duplicate reference')
        require(r['task_id'] in dataset.ids(),'Reference outside input inventory')
        require(r['payload_sha256']==dataset.payload_hash(r['task_id']),'Stale reference payload binding')
        require(r['label'] in ('aligned','misaligned'),'Invalid reference label')
        require(r['original_record']['input_sha256']==r['original_input_sha256'],'Original reference binding mismatch')
        if not allow_provisional:
            require(r['original_record'].get('reference_ready') is True,'Reference is provisional; use explicit development scoring')
        refs[r['task_id']]=r
    require(set(refs)==set(dataset.ids()),'Incomplete reference coverage')
    seen=set();correct=0;confusion=Counter()
    for p in records(predictions_path):
        require(set(p)=={'task_id','verdict','reason','declarations'},'Unexpected prediction fields')
        identity=p['task_id'];require(identity in refs and identity not in seen,'Unknown/duplicate prediction')
        require(p['verdict'] in ('aligned','misaligned'),'Verdict must be binary')
        require(isinstance(p['reason'],str) and p['reason'].strip(),'Empty mathematical reason')
        require(isinstance(p['declarations'],list) and all(isinstance(x,str) for x in p['declarations']),'Invalid evidence declarations')
        if p['verdict']=='misaligned':require(p['declarations'],'Misaligned prediction requires declaration evidence')
        graph=dataset.task(identity)['formal_context'];known={n['id'] for n in graph['nodes']}
        require(set(p['declarations'])<=known,'Unknown evidence declaration')
        actual=refs[identity]['label'];correct+=p['verdict']==actual;confusion[actual+'->'+p['verdict']]+=1;seen.add(identity)
    require(seen,'No predictions')
    require(allow_partial or seen==set(refs),'Incomplete predictions; partial scoring requires explicit opt-in')
    return dict(mode='development-provisional' if allow_provisional else 'reference-ready',scored=len(seen),total=len(refs),
                coverage=len(seen)/len(refs),correct=correct,accuracy=correct/len(seen),confusion=dict(confusion))


def restore_sources(root,task_id,destination):
    """Restore exact formal source/resource bytes from the content-addressed source directory."""
    from .integrity import file_hash
    base=Path(root)/'reproduction'
    selected=[r for r in records(base/'projects.jsonl') if r['task_id']==task_id]
    require(len(selected)==1,'Unknown reproduction snapshot')
    destination=Path(destination);require(not destination.exists(),'Source destination must be fresh')
    # Validate the complete snapshot before creating any output.
    from pathlib import PurePosixPath
    for name,h in selected[0]['files'].items():
        parts=PurePosixPath(name)
        require(not parts.is_absolute() and '..' not in parts.parts and parts.parts[0]=='formal','Unsafe source path')
        require(len(h)==64 and all(c in '0123456789abcdef' for c in h),'Unsafe blob digest')
        require(file_hash(base/'blobs'/h)==h,'Reproduction source hash mismatch')
    import shutil
    for name,h in selected[0]['files'].items():
        p=destination/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(base/'blobs'/h,p)
    return dict(task_id=task_id,files=len(selected[0]['files']))
