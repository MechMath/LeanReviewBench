#!/usr/bin/env python3
"""Validate registered project-case publication inputs, without archived release data."""
import json
from pathlib import Path

import project_cases
from release_metadata import verify
from alignment_labels import verify as verify_labels
from context_validation import verify as verify_contexts


BASE = Path(__file__).resolve().parents[2]
EXPECTED = {
    'applied-modeling-lib', 'carleson', 'coarse-degiorgi', 'sphere-packing',
    'formalslt', 'vaught', 'statsmllib',
    'brownian-motion', 'pfr', 'sphere-eversion', 'pnt', 'stacks',
}
EXTRACTION_BATCHES = {
    'arklib', 'imperial-flt', 'equational-theories', 'apap',
}


def check_scope(base, config):
    registered = set(config['datasets'])
    project_cases.require(EXPECTED <= registered and registered <= EXPECTED | EXTRACTION_BATCHES,
                          'Candidate configuration must contain the twelve retained original batches plus explicitly approved extraction batches')
    actual = {p.name for p in (base / 'datasets').iterdir() if p.is_dir()}
    review = set(config.get('review_datasets', {}))
    project_cases.require(not registered & review, 'Overlapping review/released batches')
    project_cases.require(actual == registered | review,
                          f'Dataset directories differ: {sorted(actual ^ (registered | review))}')
    project_cases.require(not (base / 'datasets/manifest.json').exists(),
                          'Archived frozen-release manifest must not be included')
    for dataset in ('openai', 'flt', 'kakeya'):
        project_cases.require(not (base / 'references' / (dataset + '.jsonl')).exists(),
                              f'Archived frozen-release references must not be included: {dataset}')


def main():
    config = json.loads((BASE / 'datasets/project-cases.json').read_text())
    check_scope(BASE, config)
    project_cases.check(config)
    verify_labels(BASE)
    verify_contexts(BASE)
    verify(BASE)
    import subprocess
    import sys
    for batch in config.get('review_datasets', {}):
        subprocess.run([sys.executable, str(BASE / 'scripts/construction/review_batches/check_batch.py'),
                        '--batch', batch], check=True)
    print(f'PASS: {len(config["datasets"])} released batches; '
          f'{len(config.get("review_datasets", {}))} batches awaiting review')


if __name__ == '__main__':
    main()
