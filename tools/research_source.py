"""Read pinned research artifacts, including historical exported graphs."""
import json
from pathlib import Path
import hashlib
import subprocess

def sha(raw):return hashlib.sha256(raw).hexdigest()

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
