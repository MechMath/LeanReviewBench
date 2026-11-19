# Validation and testing

Use Python 3.11+. Offline checks require no credentials, network, Lean or research checkout:

```sh
python3 scripts/maintenance/check_support_files.py
python3 scripts/data/check_release_candidate.py
python3 scripts/data/annotation_coverage.py
python3 -m unittest discover -s tests -v
```

The support check uses `metadata/support-inventory.json` and verifies the required docs/configuration/tool inventory, local documentation links and declared Python imports. The native checker verifies all 18 batches using the same native source/informal/index schema, plus label states, context checks, provenance, indexed evidence, licensing and the data manifest. The annotation audit checks label coverage and indexed analysis hashes; human review is separate from export readiness.

The migrated upstream regression tests exercise formal-context filtering, model output validation, batch identity/resume, abstention/scoring, provider settings with mocked network responses, Lean dependency parsing and environment resolution. Additional release tests cover native input hashes, graph-free native input validation and explicit proof-erasure records that cannot claim certification of original theorem proofs. These tests use temporary fixtures and do not contact a model provider or run Lean compilation.

Optional compilation requires the dependencies in [ENVIRONMENT.md](ENVIRONMENT.md):

```sh
python3 scripts/construction/compile_projects.py compile --help
```

The current project-case collection has no frozen native model evaluation export. The [evaluation guide](../scripts/evaluation/README.md) describes execution using separately supplied complete packages. The regression tests validate that tooling with synthetic fixtures; they do not establish semantic benchmark scores, gold labels or successful recompilation.

Full historical source acquisition and construction records are archived using the pinned locators described in [DATA-FORMAT.md](DATA-FORMAT.md). They are not dependencies of ordinary benchmark checks.

Batches awaiting review use the same native checker without ignored build dependencies:

```sh
python3 scripts/data/check_release_candidate.py
python3 scripts/data/publication_readiness.py
python3 scripts/data/check_release_candidate.py --require-reviewed
```

The default check validates the clean dataset and persistent receipt bindings;
it does not rerun Lean or independently certify archived probes. The strict
`--require-reviewed` gate additionally fails until every new input has a binary
human-reviewed label and a documented license/admission state. The curator has
explicitly included the 11 historical evidence gaps with source-specific notices;
their unresolved factual status remains visible but is no longer an independent
merge blocker. Unaccepted gaps or known explicit restrictions still block.
The remaining current blocker is 26 pending human alignment reviews.
