# Main-statement reference review and scoring

Review v1 evaluates only `theorem_only` tasks. Its criterion is whether the supplied Formal expresses the main Informal statement, including its scope/encoding qualifications. Interpret formal definitions, structure constraints, aliases, instances, and the retained closure as needed. Hidden dependency descriptions are not criteria. Do not assess proof correctness or silently repair the supplied Informal to match Lean.

Main contains 137 project-case inputs; a complete frozen evaluation export must be prepared separately. Generated dependency descriptions do not block this mode. This review workflow does not establish full-mode readiness. Existing main statements are unreviewed: none becomes a gold label merely through selection, export, or a successful model run.

## Review record

Human records live outside model inputs and model-visible task directories. `benchmark_scoring.py prepare` creates a JSON document with `schema_version: paperlean-review-1` and a `records` array. Each record contains:

| Field | Contract |
| --- | --- |
| `task_id`, `mode` | Stable root identity and `theorem_only`; modes are separate assessment scopes |
| `task_sha256`, `input_sha256` | Exact exported task and input bytes; the task also binds instructions and prediction schema |
| `reference_ready` | Boolean: reference, mapping, qualifications, and necessary formal context have been checked and a binary label adjudicated; does not mean aligned |
| `status` | `pending`, `reviewed`, `adjudicated`, or `unresolved` |
| `label` | `aligned` or `misaligned` only after adjudication; otherwise null |
| `reviews` | Independent judgements, each with nonempty `reviewer`, `verdict`, and `evidence` |
| `adjudication` | Final judgement with the same three fields; null unless adjudicated |

Human verdicts are `aligned`, `misaligned`, or `insufficient_information`. At least two distinct reviewer identities and a final adjudication are required for `adjudicated`. The adjudication verdict must equal the binary label. A designated adjudicator may be one of the reviewers; use a third reviewer for unresolved disagreements. Software checks identities and record structure, while independence and subject expertise are review procedures.

Reviewers should first work independently, using the exact model-visible statement and formal closure. They may consult pinned source context and paper evidence to check reference provenance and mappings; record evidence locations and any context unavailable to the model. Check hypotheses, quantifiers, conclusions, domain restrictions, ambient objects, vacuous hypotheses, and qualification scope. A discrepancy in a definition matters here only insofar as its actual formal meaning changes the main statement. Record the relevant declaration IDs and a concrete semantic argument, counterexample, or reason for equivalence. Retain both initial judgements after reconciliation.

Use `unresolved` with a null label when essential meaning, mapping, or context cannot be established. Human uncertainty is not a gold `insufficient_information` class, and model abstention does not resolve it. Leave `reference_ready` false for unresolved references. Correcting statement text, qualifications, formal context, instructions, or output schema changes hashes and requires renewed review. Rewriting only a hidden dependency description does not change a theorem-only input.

A reviewed misalignment is a valid reference and may be ready. Do not filter negative labels out of exports. Adjudication checks whether the discrepancy concerns the main statement, rather than merely a hidden dependency description. Keep the record outside model input and disclose class balance after review; synthetic scorer fixtures are not dataset labels.

## Pilot and expansion

Select a calibration subset from a separately supplied complete evaluation
package file. The old OpenAI pilot selection is preserved in `11_9_shenhao`
alongside the removed datasets. Prepare pending review records:

```sh
python3 scripts/benchmark_protocol.py export \
  --packages /absolute/path/to/pilot-packages.jsonl --mode theorem_only --allow-draft \
  --output build/main-statement-pilot-tasks
python3 scripts/benchmark_scoring.py prepare \
  --tasks build/main-statement-pilot-tasks \
  --output build/main-statement-pilot-reviews.json
```

Have two reviewers independently annotate all selected tasks, then reconcile disagreements. Summarize initial agreement, disagreement reasons, class balance, unresolved cases, and time per task. If the rubric changes, re-review the pilot under the revised rubric before freezing it. Expand to the full prepared inventory only after that calibration. Missing negative examples must be disclosed; do not invent canonical negatives to balance the pilot.

Set each resolved record to `adjudicated`, fill `label`, retain `reviews`, fill `adjudication`, and set `reference_ready` true only after reference/context checks. This is human review work; the prepare command leaves every record pending. For an export without draft permission, use the same selection and completed reviews:

```sh
python3 scripts/benchmark_protocol.py export \
  --packages /absolute/path/to/pilot-packages.jsonl --mode theorem_only \
  --reviews build/main-statement-pilot-reviews.json \
  --output build/main-statement-pilot-ready
```

Only selected records are required; a review document may cover additional roots. Every selected supplied record must match current hashes, even with `--allow-draft`. The export index binds the review document hash and computes `development_draft` per mode. No human records enter task directories. `full` retains the package-wide completion/review gate; theorem-only review records cannot bypass it.

## Scoring

Run a batch against the intended task export using the [protocol runner](../README.md), then score its receipts and predictions. This offline example uses the mock, which always abstains and validates the pipeline only. For actual evaluation, replace its command with the configured model adapter:

```sh
python3 scripts/benchmark_protocol.py batch \
  --tasks build/main-statement-pilot-ready \
  --output build/main-statement-pilot-runs --timeout 30 -- \
  python3 "$PWD/protocol/v1/mock_system.py"
python3 scripts/benchmark_scoring.py score \
  --tasks build/main-statement-pilot-ready \
  --reviews build/main-statement-pilot-reviews.json \
  --batch build/main-statement-pilot-runs \
  --output build/main-statement-pilot-score.json
```

The batch must have been created from that exact index. Scoring uses each task's run receipt and validated prediction, not the aggregate `predictions.jsonl`. Changed batch/index/task identities or stale reviews are errors. When the export index pins a review document, scoring requires that exact document; new adjudications require a new export and batch. Development exports without a pinned review document can be scored after annotation, with development status retained. A missing receipt is `missing`; a completed receipt lacking a valid prediction is `invalid_submission`. A failed receipt remains a failure even if a prediction file exists. No retries or best-of selection are performed. Record intentional retries in separate batches.

`target_count` is the fixed index population. With `--reviews`, `eligible` counts human references with `reference_ready` true. Missing, pending, unresolved, or otherwise unready references are counted as `unreviewed_or_unresolved` and are never charged as model errors. Among eligible tasks, outcomes partition into `correct`, `incorrect`, `abstained`, `timeout`, `execution_failed`, `invalid_submission`, and `missing`. Every failure and abstention stays in the eligible denominator. Binary answered outcomes also populate confusion counts. `execution_*` counts cover the entire target population independently of review readiness.

| Metric | Formula |
| --- | --- |
| `accuracy` | correct / eligible, including abstentions and failures in the denominator |
| `answer_coverage` | valid binary answers / eligible |
| `answered_accuracy` | correct / valid binary answers |
| `target_correct_fraction` | correct / target_count; conservative population coverage statistic, not accuracy over unresolved references |

A zero denominator produces JSON null. Model `insufficient_information` is an abstention even if a human record is unresolved; it never earns binary correctness. Scoring v1 evaluates verdicts, not issue localization or explanation quality. The result records per-task outcomes, development-task count, and hashes of the index, review document, and batch configuration. Retain the source artifacts and public execution configuration alongside it. Scoring a development export does not turn it into an official benchmark result; official comparisons also require a frozen review release and comparable execution/resource policies.

## Compatibility

Review/score format v1 uses the protocol v1 model input and prediction contract. Unreviewed task exports remain development artifacts. Start a fresh batch after changing runner code, task exports, or adapter identity. Exported tasks, reviews, and run outputs belong under ignored `build/`; the commands prepare pending review records from the supplied selection.

## Provisional model reference scoring

For exploratory scoring against separately prepared, hash-bound model labels, pass
`--provisional-labels /absolute/path/to/provisional-labels.jsonl` instead of
`--reviews`. Only theorem-only inputs with matching input hashes are eligible.
The scorer uses the same fixed-denominator, failure, and abstention accounting,
but reports `reference_kind: provisional_model` and a separate
`provisional_labels_sha256`. Original records retain `reference_ready: false` and
`human_adjudicated: false`. They do not pass the human review gate, and cannot
replace a review document pinned by a human-reviewed task index. The retained
project-case references need a frozen export and exact input bindings before use.
