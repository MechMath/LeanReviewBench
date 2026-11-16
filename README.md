# LeanReviewBench

A local release preview for assessing whether Lean declarations express independently supplied mathematical statements, including their qualifications and dependency context.

Migrated from PaperLeanBench integration commit `18086147`: **172 inputs across 17 batches**, with **82 aligned and 90 misaligned provisional labels**. Stacks `STK-0B34` remains one joint input with two roots; the new ArkLib/FLT/Equational/APAP collection contributes 30 inputs. The original research repository is unchanged.

The complete dataset is stored **uncompressed and tracked by Git** in `data/0.1.0-preview`. Clone the repository and use it directly: no download service, archive extraction, research checkout or Lean installation is needed for loading and scoring. The dataset contains 3,729 files totaling 139.36 MiB before Git compression.

| Directory | Contents | Intended reader |
| --- | --- | --- |
| `data/0.1.0-preview/inputs/` | Independent informal text and 159 deduplicated declaration contexts | Models and task loaders |
| `data/0.1.0-preview/references/` | Input-bound labels, review states, reports and provenance | Evaluators and reviewers |
| `data/0.1.0-preview/reproduction/` | Exact source/resource bytes, source materials and technical evidence | Source inspection and optional reproduction |

Files use JSON/JSONL or retain their original source bytes. Identical source files share content-addressed blobs; the source inventory maps their original paths to those blobs. Model task loading reads only `inputs/`. See [migration results](docs/MIGRATION.md), [data format](docs/FORMAT.md) and [file hash inventory](releases/0.1.0-preview/manifest.json).

## Quick start

Python 3.10+; no third-party runtime dependencies. From a fresh clone:

```sh
python3 -m leanreviewbench validate \
  --data data/0.1.0-preview \
  --manifest releases/0.1.0-preview/manifest.json
python3 -m unittest discover -s tests -v
```

Validation checks all 172 inputs and, when `--manifest` is supplied, every data file's size and SHA-256. No preparation or unpacking step is needed.

```python
from leanreviewbench import Dataset

data = Dataset('data/0.1.0-preview')
task_id = data.ids()[0]
task = data.task(task_id)
print(task_id, task['roots'])
```

The evaluator-only [catalog](releases/0.1.0-preview/catalog.csv) maps opaque task IDs to original identities. `python3 -m leanreviewbench task --data data/0.1.0-preview --id TASK_ID --output runs/task.json` writes one complete model input. Graphs load on demand without implicit truncation.

## Predictions and development scoring

Supply one JSON object per line:

```json
{"task_id":"TASK_ID","verdict":"misaligned","reason":"A concrete mathematical discrepancy.","declarations":["A.declaration"]}
```

Verdicts are `aligned` or `misaligned`. Both require a nonempty reason; a negative prediction requires at least one known declaration. Unknown IDs and fields, duplicates, stale label bindings and incomplete submissions are rejected. Partial scoring requires `--allow-partial`.

```sh
python3 -m leanreviewbench score \
  --data data/0.1.0-preview --predictions runs/predictions.jsonl \
  --references data/0.1.0-preview/references/labels.jsonl \
  --allow-provisional
```

Every current label has `reference_ready=false`. This preview does not promote existing review decisions to human-adjudicated gold. Scores must be described as provisional.

## Optional source restoration

```sh
python3 -m leanreviewbench restore --data data/0.1.0-preview \
  --id TASK_ID --output build/source-snapshot
```

This materializes byte-checked `formal/Main.lean`, local imports and runtime resources at their original relative paths from the tracked source blobs. It does not download Lean/Mathlib or claim a new compilation run. Existing proof holes and technical limitations remain recorded in evaluator provenance.

## Rebuilding the migration

```sh
python3 tools/migrate.py --source /path/to/clean/research-checkout \
  --version NEW_LOCAL_VERSION
```

This maintainer-only command needs the research repository and its locally available archive Git objects. It writes ordinary files under `data/NEW_LOCAL_VERSION` and a manifest/catalog under `releases/NEW_LOCAL_VERSION`, without creating compressed archives. Generated scratch versions are ignored until deliberately selected for tracking in `.gitignore`. Runtime use needs neither the research checkout, network, Lean nor credentials. File contents are deterministic for a fixed source snapshot.

## Attribution and limitations

Code follows [LICENSE](LICENSE). Retained sources have their own [license records](licenses/index.json) and [NOTICE](NOTICE); this is not a blanket relicensing of data or source snapshots. The historical AppliedModelingLib license-copy gap remains documented.

See [MIGRATION.md](docs/MIGRATION.md) for label-state and source limitations, including the two KZG function-binding inputs whose exact original PDF revisions remain unverified. Eight historically blocked full-project compilation snapshots have recovered declaration contexts; this does not certify complete proofs or full compilation.
