# LeanReviewBench

A local release preview for assessing whether Lean declarations express independently supplied mathematical statements, including their qualifications and dependency context.

This project is migrated from PaperLeanBench integration commit `18086147`. It contains **172 inputs across 17 batches**, with **82 aligned and 90 misaligned provisional labels**. Stacks `STK-0B34` remains one joint input with two roots; the new ArkLib/FLT/Equational/APAP collection contributes 30 inputs. The original research repository is unchanged.

The Git repository contains only code, documentation, attribution, a release manifest and a compact catalog. Large data is distributed as three separate compressed artifacts; local copies and extracted data are ignored by Git.

| Artifact | Contents | Needed by |
| --- | --- | --- |
| `inputs.tar.gz` | Independent informal text and one canonical dependency graph representation; 159 deduplicated contexts | Models and task loaders |
| `references.tar.gz` | Input-bound labels, original review states, review reports and provenance | Evaluators and reviewers |
| `reproduction.tar.gz` | Deduplicated exact Lean source/resource snapshots, source material and compatibility/receipt evidence | Source inspection and optional reproduction |

Exact sizes and SHA-256 hashes are in [the local manifest](releases/0.1.0-preview/manifest.json). No public download URL or final gold release is claimed. See [migration results](docs/MIGRATION.md) and [data format](docs/FORMAT.md).

## Local quick start

Python 3.10+; the loader has no third-party runtime dependencies. Run from this directory:

```sh
python3 -m leanreviewbench prepare \
  --manifest releases/0.1.0-preview/manifest.json \
  --artifacts artifacts/0.1.0-preview \
  --output data/0.1.0-preview --references --reproduction
python3 -m leanreviewbench validate --data data/0.1.0-preview
python3 -m unittest discover -s tests -v
```

The migrated local data is already installed. `prepare` requires fresh role directories; omit it when using this workspace. An input-only installation omits `--references --reproduction`. Installation verifies compressed and expanded hashes, rejects links/path traversal, and installs each artifact role atomically.

Load a mathematical task without opening labels or review metadata:

```python
from leanreviewbench import Dataset

data = Dataset('data/0.1.0-preview')
task_id = data.ids()[0]
task = data.task(task_id)
print(task_id, task['roots'])
```

The evaluator-only [catalog](releases/0.1.0-preview/catalog.csv) maps opaque task IDs to original identities. `python3 -m leanreviewbench task --data data/0.1.0-preview --id TASK_ID --output runs/task.json` writes one complete model input. Graphs are loaded on demand; no implicit truncation is applied.

## Predictions and development scoring

Supply one JSON object per line:

```json
{"task_id":"TASK_ID","verdict":"misaligned","reason":"A concrete mathematical discrepancy.","declarations":["A.declaration"]}
```

Verdicts are exactly `aligned` or `misaligned`. Both require a nonempty reason; a negative prediction requires at least one known declaration. Unknown IDs and fields, duplicate predictions, stale label bindings and incomplete submissions are rejected. Partial scoring requires `--allow-partial`.

```sh
python3 -m leanreviewbench score \
  --data data/0.1.0-preview --predictions runs/predictions.jsonl \
  --references data/0.1.0-preview/references/labels.jsonl \
  --allow-provisional
```

Every current label has `reference_ready=false`; the command intentionally requires explicit development scoring. This preview does not promote model-reviewed/user-confirmed decisions to human-adjudicated gold. Scores must be described as provisional.

## Optional source restoration

```sh
python3 -m leanreviewbench restore --data data/0.1.0-preview \
  --id TASK_ID --output build/source-snapshot
```

This restores byte-checked `formal/Main.lean`, local imports and runtime resources. It does not download Lean/Mathlib or claim a new compilation run. Existing proof holes and technical limitations remain as recorded in evaluator provenance. Original repository/input digests are preserved separately from the normalized release payload hashes.

## Rebuilding the migration

```sh
python3 tools/migrate.py --source /path/to/clean/research-checkout \
  --version NEW_LOCAL_VERSION
```

The one-time migration needs the research repository and its locally available archive Git objects. Runtime loading, validation, scoring and source restoration need neither the research checkout, network, Lean nor credentials. Data artifacts are deterministic for a fixed source snapshot; use a fresh version directory. Research logs, excluded/staging candidates, duplicate graph formats and old experiment runs are not imported into the release tree.

## Attribution and limitations

Code follows [LICENSE](LICENSE). Retained sources have their own [license records](licenses/index.json) and [NOTICE](NOTICE); this is not a blanket relicensing of data or source snapshots. Preserve upstream attribution when redistributing the data artifacts. The historical AppliedModelingLib license-copy gap is retained in the attribution index.

Source hash/locator and label-state limitations are listed in [MIGRATION.md](docs/MIGRATION.md), including the two KZG function-binding inputs whose exact original PDF revisions remain unverified. The preview contains all registered inputs, including historically blocked compilation snapshots with recovered declaration contexts; context availability is not proof completeness or compilation certification.
