import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from scripts.data.dataset import Dataset
from scripts.data.dataset import records,file_hash

ROOT=Path(__file__).resolve().parents[1]


def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,ensure_ascii=False)+'\n')


def fixture(base):
    write(base/'datasets/project-cases.json',dict(schema_version='paperlean-project-cases-1',datasets={'example':'owner/repo'}))
    directory=base/'datasets/example/projects/sample'
    (directory/'formal').mkdir(parents=True)
    (directory/'formal/Main.lean').write_text('theorem sample : True := True.intro\n')
    (directory/'formal/certificate.json').write_text('{"bound": 2}\n')
    informal=dict(id='main',text='True holds.',scope='Complete supplied statement.',source={'locator':'Section 1'},targets=[dict(file='formal/Main.lean',declaration='sample',relation='describes')])
    write(directory/'informal.jsonl',informal)
    meta=dict(schema_version='paperlean-project-case-1',id='sample',targets=[dict(file='formal/Main.lean',declaration='sample',informal_id='main')])
    write(directory/'project.json',meta)
    script=base/'scripts/data/project_cases.py';script.parent.mkdir(parents=True)
    shutil.copy2(ROOT/'scripts/data/project_cases.py',script)
    spec=importlib.util.spec_from_file_location('_fixture_native',script);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    meta['input_sha256']=module.input_digest(directory);write(directory/'project.json',meta)
    graph=base/'metadata/derived-graphs/retained/example.json';write(graph,dict(roots=['sample'],nodes=[],edges=[]))
    write(base/'metadata/derived-graphs/retained-index.json',dict(records=[dict(dataset='example',project_id='sample',input_sha256=meta['input_sha256'],roots=['sample'],graph_path=graph.relative_to(base).as_posix(),graph_sha256=file_hash(graph))]))
    return directory,graph


class NativeContractTests(unittest.TestCase):
    def test_complete_native_records_preserved(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base);data=Dataset(base)
            self.assertEqual(data.ids(),['example:sample'])
            row=data.project('example:sample')['informal'][0]
            self.assertEqual(row['scope'],'Complete supplied statement.')
            self.assertEqual(row['source']['locator'],'Section 1')
            self.assertEqual(row['targets'][0]['declaration'],'sample')
            self.assertEqual(data.validate(),dict(inputs=1,graphs=1))
    def test_source_changes_invalidate_original_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);directory,_=fixture(base)
            (directory/'formal/Main.lean').write_text('axiom sample : False\n')
            with self.assertRaisesRegex(ValueError,'Input digest mismatch'):Dataset(base).validate()
    def test_resource_changes_invalidate_original_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);directory,_=fixture(base)
            (directory/'formal/certificate.json').write_text('{"bound": 3}\n')
            with self.assertRaisesRegex(ValueError,'Input digest mismatch'):Dataset(base).validate()
    def test_changed_graph_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);_,graph=fixture(base);graph.write_text('{}\n')
            with self.assertRaisesRegex(ValueError,'graph hash'):Dataset(base).graph('example:sample')
    def test_stale_graph_binding_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base);p=base/'metadata/derived-graphs/retained-index.json';obj=json.loads(p.read_text());obj['records'][0]['input_sha256']='stale';write(p,obj)
            with self.assertRaisesRegex(ValueError,'Stale retained'):Dataset(base).graph('example:sample')
    def test_unsafe_graph_path_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);fixture(base);p=base/'metadata/derived-graphs/retained-index.json';obj=json.loads(p.read_text());obj['records'][0]['graph_path']='../escape';write(p,obj)
            with self.assertRaisesRegex(ValueError,'Unsafe graph'):Dataset(base).graph('example:sample')
    def test_no_implicit_model_export(self):
        self.assertFalse(hasattr(Dataset,'task'))
        self.assertFalse((ROOT/'scripts/data/evaluate.py').exists())


class PublicationTests(unittest.TestCase):
    def test_consolidated_evidence_paths(self):
        from scripts.data.paths import resolve
        self.assertFalse((ROOT/'reports').exists())
        index=json.loads((ROOT/'metadata/evidence/analysis/index.json').read_text())
        for row in index['records']:
            path=resolve(ROOT,row['path'])
            self.assertTrue(path.is_relative_to(ROOT/'metadata/evidence/analysis'))
            self.assertEqual(file_hash(path),row['sha256'])
        self.assertFalse((ROOT/'metadata/reports').exists())
        self.assertFalse((ROOT/'metadata/upstream-evidence').exists())
        with self.assertRaises(ValueError):resolve(ROOT,'../outside')

    def test_required_support_files(self):
        result=subprocess.run([sys.executable,"scripts/maintenance/check_support_files.py"],cwd=ROOT,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_original_release_candidate_checks(self):
        result=subprocess.run([sys.executable,'scripts/data/check_release_candidate.py'],cwd=ROOT,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
    def test_annotation_coverage(self):
        result=subprocess.run([sys.executable,'scripts/data/annotation_coverage.py'],cwd=ROOT,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        obj=json.loads(result.stdout)
        self.assertEqual(obj['totals']['inputs'],171)
        self.assertEqual(obj['totals']['reference_ready'],0)
    def test_all_original_graph_bindings_available(self):
        self.assertEqual(Dataset(ROOT).validate(),dict(inputs=171,graphs=171))
    def test_binary_labels_and_joint_roots(self):
        data=Dataset(ROOT);labels=[r for path in (ROOT/'metadata/labels').glob('*.jsonl') for r in records(path)]
        self.assertEqual(len(labels),171)
        self.assertEqual(sum(r['label']=='aligned' for r in labels),81)
        self.assertEqual(sum(r['label']=='misaligned' for r in labels),90)
        self.assertTrue(all(r['reference_ready'] is False for r in labels))
        self.assertNotIn('stat-learning-theory:slt-master',data.ids())
        self.assertNotIn('stacks:STK-0B34-left',data.ids())
        self.assertEqual(len(data.project('stacks:STK-0B34')['project']['targets']),2)
        self.assertEqual(len(data.project('equational-theories:etp-sheffer')['project']['targets']),2)
    def test_sources_directly_readable(self):
        data=Dataset(ROOT)
        for identity in data.ids():self.assertTrue((data.directory(identity)/'formal/Main.lean').is_file())
        self.assertFalse((ROOT/'data').exists())
        self.assertFalse((ROOT/'artifacts').exists())

if __name__=='__main__':unittest.main()
