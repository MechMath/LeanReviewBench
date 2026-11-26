#!/usr/bin/env python3
"""Resolve a historical provenance path to its immutable archive URL."""
import argparse
import json
from pathlib import Path, PurePosixPath

BASE = Path(__file__).resolve().parents[2]


def locate(original, base=BASE):
    path = PurePosixPath(original)
    if path.is_absolute() or '..' in path.parts or not path.parts:
        raise ValueError('Use an original repository-relative provenance path')
    provenance = json.loads((base / 'metadata/provenance.json').read_text())
    commit = provenance['archive_commit']
    if path.parts[0] == 'experiments':
        commit = provenance['earlier_archive']['commit']
    elif path.parts[:2] in (('metadata', 'labels'), ('metadata', 'reviews')):
        commit = provenance['excluded_model_annotations']['commit']
    return 'https://github.com/MechMath/PaperLeanBench/blob/' + commit + '/' + original


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--path', required=True)
    args = parser.parse_args()
    print(locate(args.path))
