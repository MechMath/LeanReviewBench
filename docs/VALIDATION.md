# Validation and testing

Use Python 3.11+. Offline checks require no credentials, network, Lean or research checkout:

```sh
python3 scripts/maintenance/check_support_files.py
python3 scripts/data/check_release_candidate.py
python3 scripts/data/annotation_coverage.py
python3 -m unittest discover -s tests -v
```

The support check uses `metadata/support-inventory.json` and verifies the required docs/configuration/tool inventory, local documentation links and declared Python imports. The native checker verifies the 16 registered batches, source/resource digests, target/index bindings, human-reviewed labels, graph receipts, provenance, upstream evidence, licensing and the data manifest. The annotation audit checks label coverage and indexed analysis hashes; human review is separate from export readiness.

The migrated upstream regression tests exercise formal-context filtering, model output validation, batch identity/resume, abstention/scoring, provider settings with mocked network responses, Lean dependency parsing and environment resolution. Additional release tests cover native input hashes and exact local graph access. These tests use temporary fixtures and do not contact a model provider or run Lean compilation.

Optional compilation requires the dependencies in [ENVIRONMENT.md](ENVIRONMENT.md):

```sh
python3 scripts/construction/compile_projects.py compile --help
```

The current project-case collection has no frozen native model evaluation export. The [evaluation guide](../scripts/evaluation/README.md) describes execution using separately supplied complete packages. The regression tests validate that tooling with synthetic fixtures; they do not establish semantic benchmark scores, gold labels or successful recompilation.

Full historical source acquisition and construction records are archived using the pinned locators described in [DATA-FORMAT.md](DATA-FORMAT.md). They are not dependencies of ordinary benchmark checks.
