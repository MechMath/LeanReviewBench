"""Read native project-case packages. These are curator data, not model prompts."""
import hashlib
import importlib.util
import json
from pathlib import Path


def file_hash(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def records(path):
    with Path(path).open(encoding='utf-8') as stream:
        for line in stream:
            if line.strip():yield json.loads(line)


class Dataset:
    """Uses the original batch:project identity and preserves all native records.

    project() includes source and historical metadata. Do not send its output to
    a model. A filtered, reviewed model export is a separate benchmark artifact.
    """
    def __init__(self,root='.'):
        self.root=Path(root)
        self.config=json.loads((self.root/'datasets/project-cases.json').read_text())
        if self.config['schema_version']!='paperlean-project-cases-1':raise ValueError('Unknown project-case configuration')
        self._projects={}
        for batch in {**self.config['datasets'], **self.config.get('review_datasets', {})}:
            for path in sorted((self.root/'datasets'/batch/'projects').glob('*/project.json')):
                self._projects[batch+':'+path.parent.name]=path.parent
    def __len__(self):return len(self._projects)
    def ids(self):return list(self._projects)
    def directory(self,identity):return self._projects[identity]
    def project(self,identity):
        directory=self.directory(identity)
        return dict(project=json.loads((directory/'project.json').read_text()),
                    informal=list(records(directory/'informal.jsonl')))
    def validate(self):
        script=self.root/'scripts/data/project_cases.py'
        spec=importlib.util.spec_from_file_location('_native_project_cases',script)
        native=importlib.util.module_from_spec(spec);spec.loader.exec_module(native)
        for identity,directory in self._projects.items():
            meta=self.project(identity)['project']
            if meta['schema_version']!='paperlean-project-case-1':raise ValueError('Unknown project schema')
            if native.input_digest(directory)!=meta['input_sha256']:raise ValueError('Input digest mismatch: '+identity)
        return dict(inputs=len(self))
