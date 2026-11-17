"""Validate current per-input analysis evidence and its declared coverage."""
from collections import Counter
import hashlib
import json
from pathlib import Path


def verify(base):
    base=Path(base)
    document=json.loads((base/'metadata/evidence/analysis/index.json').read_text())
    if document.get('schema_version')!='leanreviewbench-analysis-index-1':
        raise ValueError('Unsupported analysis evidence index')
    labels={}
    for path in (base/'metadata/labels').glob('*.jsonl'):
        for line in path.read_text().splitlines():
            row=json.loads(line);labels[row['dataset'],row['project_id']]=row
    upstream={}
    for path in (base/'metadata/evidence/upstream').glob('*.jsonl'):
        upstream[path.relative_to(base).as_posix()]={r['id']:r for r in map(json.loads,path.read_text().splitlines())}
    seen=set();files=set();counts=Counter()
    for row in document['records']:
        key=row['dataset'],row['project_id']
        expected=f'metadata/evidence/analysis/{key[0]}/{key[1]}.json'
        if key in seen or key not in labels or row['path']!=expected:
            raise ValueError('Invalid/duplicate analysis evidence binding')
        label=labels[key];path=base/expected;raw=path.read_bytes();item=json.loads(raw)
        digest=hashlib.sha256(raw).hexdigest()
        if digest!=row['sha256'] or label.get('review_report')!=expected or label.get('review_report_sha256')!=digest:
            raise ValueError('Analysis evidence hash/label reference differs')
        project=json.loads((base/'datasets'/key[0]/'projects'/key[1]/'project.json').read_text())
        if item.get('schema_version')!='leanreviewbench-analysis-evidence-1' or any(item.get(k)!=label[k] for k in ['dataset','project_id','task_id','input_sha256','label','reason','human_adjudicated','reference_ready','review_status']):
            raise ValueError('Analysis evidence verdict/input binding differs')
        if item['roots']!=[t['declaration'] for t in project['targets']] or row['input_sha256']!=label['input_sha256']:
            raise ValueError('Analysis evidence roots/input differ')
        status=item['analysis_status']
        if row['analysis_status']!=status or status not in ('detailed_review_retained','retained_label_reason_only','reason_missing'):
            raise ValueError('Invalid analysis evidence coverage state')
        if status=='detailed_review_retained' and not item.get('analysis'):
            raise ValueError('Detailed analysis missing')
        if (status=='reason_missing')!= (not bool(item['reason'].strip())):
            raise ValueError('Analysis reason coverage differs')
        if len(item['upstream_evidence'])!=row['upstream_evidence_records']:
            raise ValueError('Analysis upstream count differs')
        for ref in item['upstream_evidence']:
            evidence=upstream.get(ref['path'],{}).get(ref['id'])
            if not evidence or evidence['dataset']!=key[0] or not any(b['project_id']==key[1] and b['input_sha256']==item['input_sha256'] for b in evidence['projects']):
                raise ValueError('Analysis upstream evidence binding differs')
        seen.add(key);files.add(path.relative_to(base).as_posix());counts[status]+=1
    actual={p.relative_to(base).as_posix() for p in (base/'metadata/evidence/analysis').glob('*/*.json')}
    if seen!=set(labels) or actual!=files or dict(counts)!=document['counts']:
        raise ValueError('Analysis evidence coverage differs')
    print(f'PASS: {len(seen)} input-bound analysis records; {counts["detailed_review_retained"]} detailed reviews; {counts["reason_missing"]} missing reasons explicitly recorded')
