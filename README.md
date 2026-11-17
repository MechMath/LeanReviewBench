# LeanReviewBench

A benchmark for informal–formal statement alignment in real Lean projects.

This local publication preview retains **171 versioned inputs across 16 registered batches**, with **81 aligned and 90 misaligned human-reviewed labels**. It uses the original **`paperlean-project-case-1`** format documented in [the data contract](docs/DATA-FORMAT.md). All data are ordinary Git-tracked files; no archive extraction, download service or research checkout is needed to inspect or validate them.

```text
datasets/
  project-cases.json
  <batch>/
    README.md
    index.csv
    projects/<id>/
      project.json
      informal.jsonl
      CHANGES.md                 # When compatibility changes exist
      formal/
        Main.lean
        dep/
metadata/
  labels/<batch>.jsonl
  evidence/
    upstream/                    # Original upstream claims and input associations
    analysis/<batch>/<id>.json    # Current per-input judgment evidence
  taxonomy/                      # Classification standard and all negative labels
  derived-graphs/
    index.json                   # Current derived-graph/receipt bindings
    retained-index.json          # Local access to all 171 original contexts
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

Each package preserves its original metadata, full informal records, target bindings, scope notes, before/after links and source/resource bytes. Labels and review evidence remain outside model-visible exports. Joint Stacks `STK-0B34` and Equational Sheffer inputs remain single multi-root packages. Original input hashes and verdicts are unchanged. Label records contain concise English reasons and scope, with completed human review recorded explicitly. The analysis index links them to evidence under `metadata/evidence/analysis/`; upstream claims are separate under `metadata/evidence/upstream/`. Technical receipts and composition evidence live under `metadata/derived-graphs/`. Exact compatibility aliases in `metadata/layout.json` resolve embedded historical receipt locators.

## Validate and inspect

Python 3.11+; static checks have no third-party dependencies and need neither Lean nor network access:

```sh
python3 scripts/maintenance/check_support_files.py
python3 scripts/data/check_release_candidate.py
python3 scripts/data/annotation_coverage.py
python3 scripts/data/inspect_dataset.py validate
python3 -m unittest discover -s tests -v
```

The native checker validates registered scope, project indexes and input hashes, label bindings, graph receipts, upstream evidence, provenance, licensing inventory and publication hashes. The convenience command also checks local graph availability for all 171 inputs.

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
graph = bench.graph('stacks:STK-0B34')
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

This packaging migration performs static verification, not a fresh Lean build. Seven retained inputs have legacy blocked flags and recovered contexts: six have statement-type elaboration evidence, and CDG-L94 has a subsequent original-theorem compilation receipt. These records do not assert fresh compilation of the packaged checkout. Compilation is separate from proof completeness and semantic labeling.

To rebuild this publication layout from the pinned research checkout and its local archive Git objects:

```sh
python3 scripts/maintenance/migrate.py --source /path/to/clean/research-checkout \
  --output /path/to/fresh-publication-directory
```

See [environment configuration](docs/ENVIRONMENT.md), [validation](docs/VALIDATION.md) and [maintenance](docs/MAINTENANCE.md) for current procedures. Refresh the support inventory before the data manifest after intentional changes.

## Attribution and review status

Code follows [LICENSE](LICENSE); upstream sources retain their own [license records](licenses/index.json) and [NOTICE](NOTICE). This is not a blanket relicensing of source material. The historical AppliedModelingLib license-copy gap remains recorded.

All 171 labels have `human_adjudicated=true` and `review_status=human_reviewed`. Their separate evaluation-export state remains `reference_ready=false` and `gold_label=null`. Two KZG function-binding inputs still lack a verified exact original PDF revision/hash. See [DATA-FORMAT.md](docs/DATA-FORMAT.md) for these qualifications.
