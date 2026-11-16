"""Resolve retained evidence paths while preserving original hash-bound records."""
from pathlib import Path


def resolve(base,relative):
    base=Path(base);path=Path(relative)
    if not path.parts or path.is_absolute() or '..' in path.parts:
        raise ValueError('Unsafe evidence path')
    if path.parts[0]=='reports':
        relocated=base/'metadata'/path
        path=relocated if relocated.exists() else base/path
    else:path=base/path
    if not path.resolve().is_relative_to(base.resolve()):
        raise ValueError('Evidence path escapes repository')
    return path
