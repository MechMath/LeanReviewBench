import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from leanreviewbench import Dataset
from leanreviewbench.artifacts import install
from leanreviewbench.dataset import encoded,digest,validate_context
from leanreviewbench.evaluate import score,restore_sources

ROOT=Path(__file__).resolve().parents[1]


def fixture(base):
    graph=dict(schema_version='leanreviewbench-context-1',roots=['root'],nodes=[dict(id='root',kind='theorem',type='True',value=None,proof_valued=True,external=False)],edges=[],external_boundary='Mathlib')
    cid=digest(encoded(graph));directory=base/'inputs';(directory/'contexts').mkdir(parents=True)
    (directory/'contexts'/(cid+'.json')).write_bytes(encoded(graph))
    task=dict(schema_version='leanreviewbench-input-1',task_id='lrb-example',roots=['root'],informal=[dict(id='main',text='True holds.')],context_id=cid,environment={})
    (directory/'tasks.jsonl').write_bytes(encoded(task))
    ref=dict(task_id=task['task_id'],payload_sha256=digest(encoded(task)),original_input_sha256='original',label='aligned',original_record=dict(input_sha256='original',reference_ready=False))
    (base/'labels.jsonl').write_bytes(encoded(ref))
    prediction=dict(task_id=task['task_id'],verdict='aligned',reason='The selected types agree.',declarations=[])
    (base/'predictions.jsonl').write_bytes(encoded(prediction))
    return task,graph,cid


class ContractTests(unittest.TestCase):
    def test_task_reads_only_inputs_and_has_no_reference_fields(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base);(base/'labels.jsonl').unlink()
            task=Dataset(base).task('lrb-example')
            self.assertEqual(set(task),{'schema_version','task_id','roots','informal','formal_context','environment'})
            self.assertNotIn('label',task)
    def test_tampered_context_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);_,_,cid=fixture(base);(base/'inputs/contexts'/(cid+'.json')).write_text('{}')
            with self.assertRaisesRegex(ValueError,'Context hash'):Dataset(base).validate()
    def test_injected_input_metadata_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);task,_,_=fixture(base);task['label']='aligned';(base/'inputs/tasks.jsonl').write_bytes(encoded(task))
            with self.assertRaisesRegex(ValueError,'Unexpected model-input'):Dataset(base)
    def test_proof_values_and_dangling_edges_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            _,graph,_=fixture(Path(tmp));graph['nodes'][0]['value']='True.intro'
            with self.assertRaisesRegex(ValueError,'Proof body'):validate_context(graph,['root'])
            graph['nodes'][0]['value']=None;graph['edges']=[dict(source='root',target='missing',site='type')]
            with self.assertRaisesRegex(ValueError,'Dangling'):validate_context(graph,['root'])
    def test_provisional_scoring_requires_explicit_opt_in(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base)
            with self.assertRaisesRegex(ValueError,'provisional'):score(Dataset(base),base/'predictions.jsonl',base/'labels.jsonl')
            result=score(Dataset(base),base/'predictions.jsonl',base/'labels.jsonl',True)
            self.assertEqual(result['accuracy'],1)
    def test_negative_prediction_requires_known_declaration(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base);p=dict(task_id='lrb-example',verdict='misaligned',reason='Wrong domain.',declarations=['missing']);(base/'predictions.jsonl').write_bytes(encoded(p))
            with self.assertRaisesRegex(ValueError,'Unknown evidence'):score(Dataset(base),base/'predictions.jsonl',base/'labels.jsonl',True)
    def test_stale_reference_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base);p=json.loads((base/'labels.jsonl').read_text());p['payload_sha256']='stale';(base/'labels.jsonl').write_bytes(encoded(p))
            with self.assertRaisesRegex(ValueError,'Stale reference'):score(Dataset(base),base/'predictions.jsonl',base/'labels.jsonl',True)
    def test_unsafe_archive_member_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);p=base/'bad.tar.gz'
            with tarfile.open(p,'w:gz') as archive:
                member=tarfile.TarInfo('../escape');member.size=1;archive.addfile(member,io.BytesIO(b'x'))
            m=dict(schema_version='leanreviewbench-release-1',inputs=1,version='test',artifacts=[dict(role='inputs',path=p.name,size=p.stat().st_size,sha256=digest(p.read_bytes()),members=[dict(path='../escape',size=1,sha256=digest(b'x'))])]);(base/'manifest.json').write_bytes(encoded(m))
            with self.assertRaisesRegex(ValueError,'Unsafe archive'):install(base/'manifest.json',base,base/'installed')
            self.assertFalse((base/'escape').exists())
    def test_archive_digest_and_missing_members_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);p=base/'empty.tar.gz'
            with tarfile.open(p,'w:gz'):pass
            a=dict(role='inputs',path=p.name,size=p.stat().st_size,sha256='0'*64,members=[])
            m=dict(schema_version='leanreviewbench-release-1',inputs=0,version='test',artifacts=[a]);mp=base/'manifest.json';mp.write_bytes(encoded(m))
            with self.assertRaisesRegex(ValueError,'Artifact hash'):install(mp,base,base/'out')
            a['sha256']=digest(p.read_bytes());a['members']=[dict(path='missing',size=1,sha256=digest(b'x'))];mp.write_bytes(encoded(m))
            with self.assertRaisesRegex(ValueError,'Missing archive'):install(mp,base,base/'out')


class LocalDataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base=ROOT/'data/0.1.0-preview'
        if not cls.base.exists():raise unittest.SkipTest('Install local preview artifacts to run full-data tests')
        cls.dataset=Dataset(cls.base)
    def test_all_inputs_validate_and_labels_bind(self):
        self.assertEqual(self.dataset.validate(),dict(inputs=172,contexts=159))
        from leanreviewbench.dataset import records
        labels=list(records(self.base/'references/labels.jsonl'))
        self.assertEqual(len(labels),172)
        self.assertEqual({r['task_id'] for r in labels},set(self.dataset.ids()))
        self.assertEqual(sum(r['label']=='misaligned' for r in labels),90)
        for r in labels:self.assertEqual(r['payload_sha256'],self.dataset.payload_hash(r['task_id']))
    def test_joint_stacks_and_multi_root_sheffer_remain_one_input_each(self):
        from leanreviewbench.dataset import records
        mapping={r['original_id']:r['task_id'] for r in records(self.base/'references/provenance.jsonl')}
        self.assertNotIn('stacks:STK-0B34-left',mapping)
        self.assertEqual(len(self.dataset.task(mapping['stacks:STK-0B34'])['roots']),2)
        self.assertEqual(len(self.dataset.task(mapping['equational-theories:etp-sheffer'])['roots']),2)
    def test_formal_snapshot_restores_exact_bytes(self):
        from leanreviewbench.dataset import records
        records_=list(records(self.base/'reproduction/projects.jsonl'))
        selected=next(r for r in records_ if r['original_id']=='equational-theories:etp-endtoend')
        with tempfile.TemporaryDirectory() as tmp:
            dst=Path(tmp)/'restored';restore_sources(self.base,selected['task_id'],dst)
            actual={p.relative_to(dst).as_posix():digest(p.read_bytes()) for p in dst.rglob('*') if p.is_file()}
            self.assertEqual(actual,selected['files'])
            self.assertTrue(any(p.endswith('.json') for p in actual),'Runtime certificates must be retained')

if __name__=='__main__':unittest.main()
