import hashlib
import json
from pathlib import Path

TASK_FIELDS = {'schema_version','task_id','roots','informal','context_id','environment'}
NODE_FIELDS = {'id','kind','type','value','external','proof_valued','projection','internal','generated_kind'}
CONTEXT_FIELDS = {'schema_version','roots','nodes','edges','external_boundary'}


def require(condition,message):
    if not condition:raise ValueError(message)


def encoded(obj):
    return (json.dumps(obj,ensure_ascii=False,sort_keys=True,separators=(',',':'))+'\n').encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def records(path):
    with Path(path).open(encoding='utf-8') as stream:
        for line in stream:
            if line.strip():yield json.loads(line)


def validate_context(graph,roots):
    require(set(graph)==CONTEXT_FIELDS,'Unexpected context fields')
    require(graph['schema_version']=='leanreviewbench-context-1','Unknown context schema')
    require(graph['roots']==roots,'Context roots differ')
    nodes={}
    for n in graph['nodes']:
        require(set(n)<=NODE_FIELDS,'Unexpected declaration fields')
        require(n['id'] not in nodes,'Duplicate declaration')
        require(isinstance(n.get('type'),str),'Missing declaration type')
        require(n.get('value') is None or isinstance(n['value'],str),'Invalid declaration value')
        if n.get('proof_valued') or n.get('kind') in ('theorem','theorem_statement','axiom'):
            require(n.get('value') is None,'Proof body exposed')
        for value in [n.get('type'),n.get('value')]:
            require(not value or 'failed to pretty print expression' not in value,'Failed expression print')
        nodes[n['id']]=n
    require(set(roots)<=set(nodes),'Missing root declaration')
    for edge in graph['edges']:
        require(set(edge)=={'source','target','site'},'Unexpected edge fields')
        require(edge['source'] in nodes and edge['target'] in nodes,'Dangling dependency edge')
        require(edge['site'] in ('type','definition_value','constructor_type'),'Unknown dependency site')
        require(not (edge['site']=='definition_value' and nodes[edge['source']].get('proof_valued')),'Proof traversal')


class Dataset:
    """Loads only input files. It does not open reference or provenance artifacts."""
    def __init__(self,root):
        self.directory=Path(root)/'inputs'
        self._tasks={}
        for task in records(self.directory/'tasks.jsonl'):
            require(set(task)==TASK_FIELDS,'Unexpected model-input fields')
            require(task['schema_version']=='leanreviewbench-input-1','Unknown input schema')
            require(task['task_id'] not in self._tasks,'Duplicate task')
            require(len(task['context_id'])==64 and all(c in '0123456789abcdef' for c in task['context_id']),'Unsafe context ID')
            require(task['roots'] and len(set(task['roots']))==len(task['roots']),'Missing/duplicate roots')
            require(task['informal'] and all(set(x)=={'id','text'} and x['text'].strip() for x in task['informal']),'Missing independent target')
            self._tasks[task['task_id']]=task
    def __len__(self):return len(self._tasks)
    def ids(self):return list(self._tasks)
    def __iter__(self):
        for identity in self.ids():yield self.task(identity)
    def task(self,identity):
        stored=self._tasks[identity]
        raw=(self.directory/'contexts'/(stored['context_id']+'.json')).read_bytes()
        require(digest(raw)==stored['context_id'],'Context hash mismatch')
        graph=json.loads(raw);validate_context(graph,stored['roots'])
        return dict(schema_version='leanreviewbench-task-1',task_id=identity,roots=list(stored['roots']),
                    informal=stored['informal'],formal_context=graph,environment=stored['environment'])
    def validate(self):
        for identity in self.ids():self.task(identity)
        return dict(inputs=len(self),contexts=len({t['context_id'] for t in self._tasks.values()}))
    def payload_hash(self,identity):return digest(encoded(self._tasks[identity]))
