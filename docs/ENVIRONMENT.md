# Environment and configuration

Reading data, static checks and offline tests require Python 3.11+ and its standard library; Lean and model credentials are optional. `pyproject.toml` defines package metadata and the inspection CLI.

Locations are configuration inputs, not machine-specific paths in dataset files.
The shared pins and environment-variable names are declared in
[project-cases.json](../datasets/project-cases.json). No dependency is installed
or environment variable set by a data check.

| Variable | Meaning | Used when |
| --- | --- | --- |
| PAPERLEAN_MATHLIB | Built Mathlib checkout or verified source/cache directory at the pinned revision | Compiling projects |
| PAPERLEAN_CSLIB | Cslib checkout with the pinned revision and matching Mathlib lock | Cases importing Cslib, or Mathlib archive verification |
| PAPERLEAN_LEAN | Explicit Lean executable matching the configured toolchain | Optional compiler override |
| PAPERLEAN_ELAN | Explicit elan executable; otherwise elan is resolved from PATH | Resolving Lean when PAPERLEAN_LEAN is absent |
| PAPERLEAN_LEANTRACE | Compatible exporter bundle directory containing Export.lean and graph.py | Optional re-extraction tooling |
| PAPERLEAN_TEST_LEAN | Lean executable for optional compiler regression tests | Explicit test runs |

Lean is pinned to `leanprover/lean4:v4.34.1`. Mathlib and Cslib revisions remain
in the shared configuration. Dependency directories and revisions are checked
by `scripts/construction/compile_projects.py env`. Lean/tool bundle resolution is available
through `scripts/construction/compile_projects.py tools`; both commands validate caller
configuration rather than changing it. Normal candidate checks require none
of these variables.

PAPERLEAN_LEANTRACE names the compatible statement-graph exporter bundle used
by this project, not an assumed leantrace executable. Resolution checks bundle
entries; it does not prove extractor compatibility or automatically rerun an
extraction. Historical exporter source hashes and commands remain in the pinned
archive. The published construction utilities provide a shared compiler and
configurable tool resolution, not a complete from-scratch production pipeline.

Optional model-provider settings are separate from these construction
dependencies; see [model-provider setup](../scripts/evaluation/README.md#model-provider-setup).

The root `.env.example` documents optional construction variables; construction scripts read exported process variables rather than loading that file automatically. No root Lake workspace is required for static inspection. `.gitignore` excludes build outputs, local settings and credentials; `.gitattributes` preserves exact bytes for source, evidence and licenses. Model-provider setup and its separate environment template remain in the [evaluation guide](../scripts/evaluation/README.md#model-provider-setup).
