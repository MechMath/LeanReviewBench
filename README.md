# LeanReviewBench

A benchmark for informal–formal statement alignment in real Lean projects.

This local publication preview retains **172 versioned inputs across 17 registered batches**, with **82 aligned and 90 misaligned provisional labels**. It uses the original **`paperlean-project-case-1`** format described in the paper's construction appendix and the research branch documentation. All data are ordinary Git-tracked files; no archive extraction, download service or research checkout is needed to inspect or validate them.

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
  upstream-evidence/
  derived-graphs/
    index.json                   # Original derived-graph/receipt bindings
    retained-index.json          # Local access to all 172 original contexts
  provenance.json
  manifest.json
  release.json
reports/                         # Retained bound reviews and extraction evidence
licenses/
```

Each package preserves its original metadata, full informal records, target bindings, scope notes, before/after links and source/resource bytes. Labels and review evidence remain outside model-visible exports. Joint Stacks `STK-0B34` and Equational Sheffer inputs remain single multi-root packages. Original input hashes and label records are unchanged.

## Validate and inspect

Python 3.11+; static checks have no third-party dependencies and need neither Lean nor network access:

```sh
python3 scripts/data/check_release_candidate.py
python3 scripts/data/annotation_coverage.py
python3 -m leanreviewbench validate
python3 -m unittest discover -s tests -v
```

The native checker validates registered scope, project indexes and input hashes, label bindings, graph receipts, upstream evidence, provenance, licensing inventory and publication hashes. The convenience command also checks local graph availability for all 172 inputs.

Open `datasets/<batch>/projects/<id>/formal/Main.lean` directly to read a source snapshot. No blob restoration step is required. To inspect native metadata and complete informal records:

```sh
python3 -m leanreviewbench inspect --id stacks:STK-0B34
```

```python
from leanreviewbench import Dataset

bench = Dataset('.')
package = bench.project('stacks:STK-0B34')
print(package['project']['targets'])
print(package['informal'])
graph = bench.graph('stacks:STK-0B34')
```

These are curator-facing package records, including source/history metadata. They are not filtered model prompts.

## Data contract and evaluation boundary

[DATA-FORMAT.md](docs/DATA-FORMAT.md) and [PROJECT-CASE-WORKFLOW.md](docs/PROJECT-CASE-WORKFLOW.md) define the native format. The [paper appendix snapshot](docs/source-contracts/paper/app_imple_detail.tex) describes the same layout. Copies of the [latest fetched research documents](docs/source-contracts/research/README.md) are pinned to commit `2f471585`; dated counts in those copies are historical. The retained data come from integration commit `18086147`, preserving the agreed refactor joint-input layout.

The current dataset contract uses binary semantic labels and requires mathematical reasons and declaration evidence for negative decisions. It is a preparation/publication format, **not a frozen model evaluation export**. Exporting requires selected independent targets and qualifications, formal roots/context, comment/proof filtering, exclusion of review/history clues, and fresh export-bound task/reference hashes. This migration does not assert that all scope notes can be copied directly into a prompt: curator scope notes are not independent quotations.

The original [evaluation tools](scripts/evaluation/README.md) and [protocol/v1](protocol/v1/README.md) are retained unchanged for compatibility with separately supplied complete packages. That older transport supports `insufficient_information` as a model abstention and is not a third gold class. It does not consume native project-case packages directly. No alternative release-only prediction schema or automatic native-to-model conversion is introduced here.

## Reproduction and maintenance

Compilation tools and [pinned environment configuration](docs/ENVIRONMENT.md) are retained. Recompilation needs externally installed pinned Lean, Mathlib and, where used, Cslib/LeanTrace:

```sh
python3 scripts/construction/compile_projects.py env
python3 scripts/construction/compile_projects.py compile --dataset carleson --ids CAR-01-before
```

This packaging migration performs static verification, not a fresh Lean build. Historical full-project compilation remains blocked for eight packages with recovered exported contexts. Compilation is separate from proof completeness and semantic labeling.

To rebuild this publication layout from the pinned research checkout and its local archive Git objects:

```sh
python3 tools/migrate.py --source /path/to/clean/research-checkout \
  --output /path/to/fresh-publication-directory
```

See [migration verification](docs/MIGRATION.md) for byte comparisons, exclusions, sizes and remaining source limitations. After an intentional data change, review input/reference bindings before regenerating `metadata/manifest.json` with `python3 scripts/data/release_metadata.py freeze`.

## Attribution and review status

Code follows [LICENSE](LICENSE); upstream sources retain their own [license records](licenses/index.json) and [NOTICE](NOTICE). This is not a blanket relicensing of source material. The historical AppliedModelingLib license-copy gap remains recorded.

All 172 labels remain provisional with `reference_ready=false`. User decisions and model reviews are preserved without promoting them to human gold. Two KZG function-binding inputs still lack a verified exact original PDF revision/hash. See [DATA-FORMAT.md](docs/DATA-FORMAT.md) for these qualifications.
