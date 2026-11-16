# Benchmark tools

| Directory | Responsibility | Entries |
| --- | --- | --- |
| `data/` | Native project indexes, hashes, labels, graph receipts and provenance | `check_release_candidate.py`, `annotation_coverage.py`, `project_cases.py`, `project_case_stats.py`, `release_metadata.py` |
| `construction/` | Optional Lean compilation and external dependency resolution | `compile_projects.py`, `compiler.py`, `environment.py`, `lean_imports.py` |
| `evaluation/` | Export, task runner, scoring, adapters and mock system | `benchmark_protocol.py`, `benchmark_scoring.py`, `responses_llm.py`, `mock_system.py` |

Python 3.11+; ordinary checks use the standard library and need no external tool setup. See [testing](../docs/testing.md), [configuration](../docs/CONFIGURATION.md) and the [evaluation guide](evaluation/README.md).

`project_cases.py` at this directory's top level is the original compatibility entry point for native data and compilation commands. The evaluation compatibility entry points delegate to `evaluation/` and require explicitly supplied complete packages. Archived `--dataset` exports and obsolete frozen-release/staging utilities are not part of this publication.

A native project package is not a filtered prompt. Model task export and export-bound reference review remain separate steps. Local provider settings stay outside task directories; templates contain no credentials.
