#!/usr/bin/env python3
"""Compatibility entry point for relocated project-case maintenance commands."""
from pathlib import Path
import subprocess
import sys

if __name__ == '__main__':
    directory = 'construction' if len(sys.argv) > 1 and sys.argv[1] in ('env', 'compile') else 'data'
    name = 'compile_projects.py' if directory == 'construction' else 'project_cases.py'
    target = Path(__file__).resolve().parent / directory / name
    raise SystemExit(subprocess.call([sys.executable, str(target), *sys.argv[1:]]))
