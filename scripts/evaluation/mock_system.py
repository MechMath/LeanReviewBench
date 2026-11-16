#!/usr/bin/env python3
"""Protocol plumbing example; deliberately makes no alignment judgement."""
import json
import os
from pathlib import Path

task = json.loads((Path(os.environ['PAPERLEAN_TASK_DIR']) / 'task.json').read_text())
Path(os.environ['PAPERLEAN_SUBMISSION_PATH']).write_text(json.dumps({
    'task_id': task['task_id'], 'verdict': 'insufficient_information', 'issues': [],
    'summary': 'Mock system: no semantic assessment was performed.'
}) + '\n')
