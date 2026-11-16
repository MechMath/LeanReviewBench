# Benchmark tools

| Directory | Responsibility | Entries |
| --- | --- | --- |
| `data/` | Native project indexes, hashes, labels, graph receipts and provenance | `check_release_candidate.py`, `annotation_coverage.py`, `project_cases.py`, `project_case_stats.py`, `release_metadata.py` |
| `construction/` | Optional Lean compilation and external dependency resolution | `compile_projects.py`, `compiler.py`, `environment.py`, `lean_imports.py` |
| `evaluation/` | Export, task runner, scoring, adapters and mock system | `benchmark_protocol.py`, `benchmark_scoring.py`, `responses_llm.py`, `mock_system.py` |

Python 3.11+; ordinary checks use the standard library and need no external tool setup. See [testing](../docs/testing.md), [configuration](../docs/CONFIGURATION.md) and the [evaluation guide](evaluation/README.md).

Use the canonical entries directly: `python3 scripts/data/project_cases.py check`, `python3 scripts/data/inspect_dataset.py inspect --id stacks:STK-0B34`, and `python3 scripts/evaluation/benchmark_protocol.py --help`. Redundant top-level compatibility wrappers have been removed.

`scripts/maintenance/` contains publication migration, byte comparison and support-file checks. These are separate from normal model execution and optional Lean compilation.

A native project package is not a filtered prompt. Model task export and export-bound reference review remain separate steps. Local provider settings stay outside task directories; templates contain no credentials.
