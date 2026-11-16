"""Resolve explicit external construction tools; never install or configure them."""
import os
from pathlib import Path
import subprocess


def resolve_lean(config):
    tools = config['construction_tools']
    direct = os.environ.get(tools['lean']['path_env'])
    if direct:
        lean = Path(direct).expanduser().resolve()
        if not lean.is_file():
            raise ValueError('PAPERLEAN_LEAN must name a Lean executable')
    else:
        elan = os.environ.get(tools['elan']['path_env'], 'elan')
        lean = Path(subprocess.check_output(
            [elan, 'which', 'lean'], text=True,
            env=dict(os.environ, ELAN_TOOLCHAIN=config['lean_toolchain'])).strip())
    version = config['lean_toolchain'].rsplit(':v', 1)[-1]
    if 'version ' + version + ',' not in subprocess.check_output([str(lean), '--version'], text=True):
        raise ValueError('Lean version differs from the pinned project environment')
    return lean


def resolve_leantrace(config):
    """Resolve the compatible Export.lean/graph.py bundle used for construction."""
    spec = config['construction_tools']['leantrace']
    value = os.environ.get(spec['path_env'])
    if not value:
        raise ValueError('Set ' + spec['path_env'] + ' to a compatible exporter bundle directory')
    directory = Path(value).expanduser().resolve()
    for entry in spec['required_files']:
        if not (directory / entry).is_file():
            raise ValueError('Missing exporter bundle entry: ' + entry)
    return directory
