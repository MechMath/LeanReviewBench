# LeanReviewBench

A benchmark for informal–formal statement alignment in real Lean projects.

This local publication preview retains **171 versioned inputs across 16 registered batches**, with **81 aligned and 90 misaligned human-reviewed labels**. It uses the original **`paperlean-project-case-1`** format documented in [the data contract](docs/DATA-FORMAT.md). All data are ordinary Git-tracked files; no archive extraction, download service or research checkout is needed to inspect or validate them.

The same native layout also contains **26 complete Poincare contexts awaiting
human review**: 15 from qinz1yang and 11 from FrenzyMath. The native loader reads
197 inputs in total. Three technically deferred contexts and five excluded
artifacts are absent. Labels, evidence and validation use the standard metadata
paths. Historical grant-association evidence remains incomplete for 11 versions;
they are included under an explicit curator decision with per-version notices.
This does not establish a historical license grant.
`python3 scripts/data/check_release_candidate.py --require-reviewed` still requires
completed human alignment review and documented admission states.

```text
datasets/
  project-cases.json
  <batch>/
    README.md
    index.csv
    projects/<id>/
      project.json
      informal.jsonl
      CHANGES.md                 # Concise Lean migration and context notes
      formal/
        Main.lean
        dep/
metadata/
  labels/<batch>.jsonl
  evidence/
    upstream/                    # Original upstream claims and input associations
    analysis/<batch>/<id>.json    # Current per-input judgment evidence
  taxonomy/                      # Classification standard and all negative labels
  validation.json                # Input-bound context check results
  provenance.json
  manifest.json
  release.json
scripts/
  data/                          # Dataset loading, inspection and native checks
  construction/                  # Optional Lean compilation
  evaluation/                    # Protocol, schema, runner and adapter
  maintenance/                   # Migration and publication integrity
licenses/
```

Each package retains its informal target, root bindings, version/group links, a statement-only Lean context and a concise `CHANGES.md`. The context contains the required declarations and elaboration support; theorem proofs are replaced by `sorry`, while computational definitions are preserved. All 171 contexts have been compiled and freshly extracted with Lean 4.34.1. Input hashes and evidence bindings follow these current files; the 81 aligned and 90 misaligned verdicts are unchanged. Labels and review evidence remain outside model-visible exports.

## Validate and inspect

Python 3.11+; static checks have no third-party dependencies and need neither Lean nor network access:

```sh
python3 scripts/maintenance/check_support_files.py
python3 scripts/data/check_release_candidate.py
python3 scripts/data/annotation_coverage.py
python3 scripts/data/inspect_dataset.py validate
python3 -m unittest discover -s tests -v
```

The native checker validates registered scope, project indexes and input hashes, label bindings, recorded context checks, upstream evidence, provenance, licensing inventory and publication hashes. The convenience command validates all 197 native Lean inputs without requiring graph files.

Open `datasets/<batch>/projects/<id>/formal/Main.lean` directly to read a source snapshot. No blob restoration step is required. To inspect native metadata and complete informal records:

```sh
python3 scripts/data/inspect_dataset.py inspect --id stacks:STK-0B34
```

```python
from scripts.data.dataset import Dataset

bench = Dataset('.')
package = bench.project('stacks:STK-0B34')
print(package['project']['targets'])
print(package['informal'])
formal_directory = bench.directory('stacks:STK-0B34') / 'formal'
print((formal_directory / 'Main.lean').read_text())
```

These are curator-facing package records, including source/history metadata. They are not filtered model prompts.

## Data contract and evaluation boundary

[DATA-FORMAT.md](docs/DATA-FORMAT.md) defines the native format, label/evidence relationships and current limitations. The [documentation index](docs/README.md) links construction, environment, statistics and maintenance guides. Source revisions are pinned in `metadata/release.json`.

The current dataset contract uses binary semantic labels and requires mathematical reasons and declaration evidence for negative decisions. It is a preparation/publication format, **not a frozen model evaluation export**. Exporting requires selected independent targets and qualifications, formal roots/context, comment/proof filtering, exclusion of review/history clues, and fresh export-bound task/reference hashes. This migration does not assert that all scope notes can be copied directly into a prompt: curator scope notes are not independent quotations.

The [evaluation tools](scripts/evaluation/README.md) and [protocol v1 contract](scripts/evaluation/PROTOCOL.md) retain their original behavior for compatibility with separately supplied complete packages. That older transport supports `insufficient_information` as a model abstention and is not a third gold class. It does not consume native project-case packages directly. No alternative release-only prediction schema or automatic native-to-model conversion is introduced here.

## Reproduction and maintenance

Compilation tools and [pinned environment configuration](docs/ENVIRONMENT.md) are retained. Recompilation needs externally installed pinned Lean, Mathlib and, where used, Cslib/LeanTrace:

```sh
python3 scripts/construction/compile_projects.py env
python3 scripts/construction/compile_projects.py compile --dataset carleson --ids CAR-01-before
```

`metadata/validation.json` records input-bound compilation, extraction and preservation checks. Dependency graphs are generated on demand and are not distributed. These checks do not certify the omitted original theorem proofs or semantic alignment. Source repository/commit/root pins identify the full upstream sources; each input's `CHANGES.md` describes its Lean migration. Ordinary use does not require reconstructing a complete upstream project. See the [construction method](docs/CONSTRUCTION.md) and [known extraction issues](https://github.com/MechMath/LeanReviewBench/issues/2).

See [environment configuration](docs/ENVIRONMENT.md), [validation](docs/VALIDATION.md) and [maintenance](docs/MAINTENANCE.md) for current procedures. Refresh the support inventory before the data manifest after intentional changes.

## Attribution and review status

Code follows [LICENSE](LICENSE); upstream sources retain their own [license records](licenses/index.json) and [NOTICE](NOTICE). This is not a blanket relicensing of source material. The historical AppliedModelingLib license-copy gap remains recorded.

All 171 labels have `human_adjudicated=true` and `review_status=human_reviewed`. Their separate evaluation-export state remains `reference_ready=false` and `gold_label=null`. Two KZG function-binding inputs still lack a verified exact original PDF revision/hash. See [DATA-FORMAT.md](docs/DATA-FORMAT.md) for these qualifications.
