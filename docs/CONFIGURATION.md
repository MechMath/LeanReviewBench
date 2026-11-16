# Configuration

The shared environment is defined by [datasets/project-cases.json](../datasets/project-cases.json): Lean `leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`. Per-input upstream revisions remain in each `project.json` and are separate from these common compiler pins.

| File | Purpose |
| --- | --- |
| `pyproject.toml` | Python 3.11+, CLI entry point and package metadata; no runtime third-party dependencies |
| `datasets/project-cases.json` | Registered scope, Lean/library pins and external tool environment variable names |
| `.env.example` | Optional construction path template; no credentials or machine paths |
| `scripts/evaluation/.env.example` | Original optional provider template |
| `protocol/testing/.env.example` | Original compatibility provider template |
| `protocol/v1/prediction.schema.json` | Original prediction contract for separately supplied evaluation packages |
| `.gitignore` | Generated outputs, Lean caches, local settings and credentials |
| `.gitattributes` | Exact-byte preservation for input, evidence and upstream license files |

Reading the data, static validation and offline tests need none of the optional environment settings. No local developer configuration or credential file has been migrated.

For compilation, explicitly set `PAPERLEAN_MATHLIB` and any required `PAPERLEAN_CSLIB`, plus optional tool overrides as described in [ENVIRONMENT.md](ENVIRONMENT.md). The root example file is a template only; construction scripts read exported process variables. No root Lake workspace or dependency download step is required for static checks. Historical upstream Lake configs and original source copies are archive provenance, not the common environment configuration.

For a live model adapter, use the [evaluation setup](../scripts/evaluation/README.md#model-provider-setup) and its provider template. Tests mock provider requests. They need neither an API key nor network access.
