#!/usr/bin/env python3
"""Compatibility entry point for the retained evaluation protocol implementation."""
from pathlib import Path
import runpy
if __name__=='__main__':
    runpy.run_path(str(Path(__file__).resolve().parent/'evaluation/benchmark_protocol.py'),run_name='__main__')
