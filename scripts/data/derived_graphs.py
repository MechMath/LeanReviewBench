"""Verify newly recovered statement graphs against immutable benchmark inputs."""
import hashlib
import json
from pathlib import Path

from paths import resolve
from project_cases import formal_files, input_digest, target_roots


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def retained_file(base, relative, expected):
    path = Path(relative)
    if not path.parts or path.is_absolute() or '..' in path.parts or path.parts[0] not in ('metadata', 'reports'):
        raise ValueError('Unsafe derived-graph evidence path')
    path = resolve(base,path)
    if not path.is_file() or sha(path) != expected:
        raise ValueError('Derived-graph evidence hash mismatch: ' + relative)
    return path


def combine_graphs(graphs):
    """Union retained root graphs without changing any declaration or dependency."""
    if not graphs:
        raise ValueError('No component graphs')
    header = {k: v for k, v in graphs[0].items() if k not in ('roots', 'nodes', 'edges')}
    roots, nodes, edges = [], {}, {}
    for graph in graphs:
        if {k: v for k, v in graph.items() if k not in ('roots', 'nodes', 'edges')} != header:
            raise ValueError('Incompatible component graph metadata')
        for root in graph['roots']:
            if root in roots:
                raise ValueError('Duplicate component root')
            roots.append(root)
        for node in graph['nodes']:
            if node['id'] in nodes and nodes[node['id']] != node:
                raise ValueError('Conflicting component declaration: ' + node['id'])
            nodes[node['id']] = node
        for edge in graph['edges']:
            edges[json.dumps(edge, sort_keys=True)] = edge
    return dict(header, roots=roots, nodes=[nodes[k] for k in sorted(nodes)],
                edges=[edges[k] for k in sorted(edges)])


def verify_composition(base, directory, receipt, graph):
    """Verify a new input binding against archived inputs and extraction receipts."""
    if receipt.get('fresh_compilation') is not False:
        raise ValueError('Graph composition must not claim fresh compilation')
    if receipt.get('formal_sources') != [list(item) for item in formal_files(directory)]:
        raise ValueError('Composed graph formal sources differ')
    components = receipt.get('components', [])
    if len(components) < 2:
        raise ValueError('Missing graph composition components')
    graphs = {'default': [], 'explicit': []}
    for component in components:
        old_path = retained_file(base, component['project_path'], component['project_sha256'])
        old = json.loads(old_path.read_text())
        if (old['input_sha256'] != component['input_sha256'] or
                input_digest(old_path.parent) != old['input_sha256'] or
                formal_files(old_path.parent) != formal_files(directory) or
                target_roots(old) != [component['root']]):
            raise ValueError('Composed graph archived input differs')
        old_receipt = json.loads(retained_file(
            base, component['receipt_path'], component['receipt_sha256']).read_text())
        if (old_receipt.get('input_sha256') != old['input_sha256'] or
                old_receipt.get('root') != component['root'] or
                old_receipt.get('status') != 'passed' or
                old_receipt.get('new_sorry_or_axioms') is not False):
            raise ValueError('Invalid component extraction receipt')
        for mode, key in [('default', 'graph_sha256'), ('explicit', 'explicit_graph_sha256')]:
            binding = component[mode]
            part = json.loads(retained_file(base, binding['path'], binding['sha256']).read_text())
            if (old_receipt.get(key) != binding['sha256'] or
                    part.get('roots') != [component['root']] or
                    part.get('evidence') != graph['evidence']):
                raise ValueError('Component graph binding differs')
            graphs[mode].append(part)
    if combine_graphs(graphs['default']) != graph:
        raise ValueError('Composed graph differs from retained components')
    explicit = json.loads(retained_file(
        base, receipt['explicit_graph_path'], receipt['explicit_graph_sha256']).read_text())
    if combine_graphs(graphs['explicit']) != explicit:
        raise ValueError('Explicit composed graph differs from retained components')


def load_for(base, project_directory):
    index = base / 'metadata/derived-graphs/index.json'
    if not index.exists():
        return None
    document = json.loads(index.read_text())
    if document.get('schema_version') != 'paperlean-derived-graphs-1':
        raise ValueError('Unsupported derived-graph index')
    identity = project_directory.name
    dataset = project_directory.parents[1].name
    records = [r for r in document['records'] if (r['dataset'], r['project_id']) == (dataset, identity)]
    if not records:
        return None
    if len(records) != 1:
        raise ValueError('Duplicate derived-graph binding')
    record = records[0]
    project = json.loads((project_directory / 'project.json').read_text())
    if record['input_sha256'] != project['input_sha256'] or input_digest(project_directory) != record['input_sha256']:
        raise ValueError('Stale derived-graph input binding: ' + identity)
    roots = target_roots(project)
    bound_roots = record.get('roots', [record.get('root')])
    if bound_roots != roots:
        raise ValueError('Derived-graph root binding differs')
    graph_file = retained_file(base, record['graph_path'], record['graph_sha256'])
    receipt_file = retained_file(base, record['receipt_path'], record['receipt_sha256'])
    graph = json.loads(graph_file.read_text())
    receipt = json.loads(receipt_file.read_text())
    if record['evidence'] not in ('compiled_environment', 'elaborated_statement_type'):
        raise ValueError('Derived graph lacks Lean elaboration evidence')
    if (graph.get('schema_version') != 1 or graph.get('evidence') != record['evidence'] or
            not set(roots) <= set(graph['roots'])):
        raise ValueError('Derived graph evidence/root differs')
    if receipt.get('input_sha256') != record['input_sha256'] or receipt.get('graph_sha256') != record['graph_sha256']:
        raise ValueError('Derived graph receipt binding differs')
    if receipt.get('status') != 'passed':
        raise ValueError('Derived graph lacks a successful extraction receipt')
    if receipt.get('schema_version') == 'paperlean-statement-only-receipt-1':
        if (receipt.get('proof_erasure') is not True or
                receipt.get('fresh_compilation') is not True or
                receipt.get('original_theorem_proof_certified') is not False or
                receipt.get('statement_preservation') != 'passed' or
                receipt.get('nonproof_definition_preservation') != 'passed' or
                receipt.get('formal_sources') != [list(item) for item in formal_files(project_directory)]):
            raise ValueError('Invalid statement-only extraction receipt')
    elif receipt.get('new_sorry_or_axioms') is not False:
        raise ValueError('Derived graph lacks a successful hole-free extraction receipt')
    if receipt.get('schema_version') == 'paperlean-composed-graph-receipt-1':
        if receipt.get('roots') != roots or graph['roots'] != roots:
            raise ValueError('Composed graph roots differ')
        verify_composition(base, project_directory, receipt, graph)
    return graph, {'graph_path': record['graph_path'], 'sha256': record['graph_sha256'],
                   'receipt_path': record['receipt_path'], 'receipt_sha256': record['receipt_sha256'],
                   'binding_method': 'verified derived statement graph', 'evidence': record['evidence'],
                   'fresh_compilation': receipt.get('fresh_compilation', record['evidence'] == 'compiled_environment'),
                   'original_theorem_proof_certified': receipt.get('original_theorem_proof_certified', False)}


def verify(base):
    path = base / 'metadata/derived-graphs/index.json'
    if not path.exists():
        return
    document = json.loads(path.read_text())
    for record in document['records']:
        if any('/' in record[k] or record[k] in ('.', '..', '') for k in ('dataset', 'project_id')):
            raise ValueError('Unsafe derived-graph project path')
        load_for(base, base / 'datasets' / record['dataset'] / 'projects' / record['project_id'])
    print(f'PASS: {len(document["records"])} derived statement graph bindings')
