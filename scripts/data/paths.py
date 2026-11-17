"""Resolve retained evidence paths while preserving original hash-bound records."""
from pathlib import Path
import json


def resolve(base,relative):
    base=Path(base);path=Path(relative)
    if not path.parts or path.is_absolute() or '..' in path.parts:
        raise ValueError('Unsafe evidence path')
    layout=base/'metadata/layout.json'
    aliases=json.loads(layout.read_text()).get('path_aliases',{}) if layout.exists() else {}
    path=base/aliases.get(path.as_posix(),path.as_posix())
    if not path.resolve().is_relative_to(base.resolve()):
        raise ValueError('Evidence path escapes repository')
    return path
