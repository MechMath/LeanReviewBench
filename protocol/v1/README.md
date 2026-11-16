# Task and prediction contract v1

The transport version is `paperlean-protocol-1`. It supports a local subprocess
adapter for single-call models or internal agent loops. HTTP task transport,
remote polling and parallel scheduling are not implemented.

## Assessment scope

Assess whether Formal expresses the supplied main Informal statement, including
qualifications. Interpret definitions, structure constraints, aliases, instances
and supplied context as needed. Proof correctness is outside this task.

| Mode | Visible Informal | Assessment |
| --- | --- | --- |
| `theorem_only` | Main statement and its qualifications | Main statement using actual Formal dependency meanings |
| `full` | Main statement and supplied definition pairs, with qualifications | Main statement and those definition pairs |

Hidden dependency descriptions are not criteria in `theorem_only`. Modes can
therefore have different verdicts. Other closure nodes provide interpretation
context, not extra Informal assessment targets. Use `insufficient_information`
when essential meaning or context is unavailable; do not silently repair inputs.

## Export input

The exporter requires `--packages <file.jsonl>`. The supported package schemas
are `paperlean-evaluation-1` and the legacy `paperlean-full-draft-2`, both with
complete `formal_context`. They are separate from the project's dataset format
`paperlean-project-case-1`; no native conversion is currently bundled.

A package supplies `root_id`, `main_theorem`, `definitions`, `formal_context`,
`external_boundary` and readiness metadata. Assessment pairs carry identity,
kind, Formal, Informal and qualifiers. Context contains `declarations`,
`external_nodes` and `edges`: retained local types/non-proof values, external
library identities/types and the complete retained dependency graph.
Validation rejects duplicate identities, disconnected or dangling edges,
unexpected context fields, proof bodies and prohibited definition-value traversal
from theorem/proof nodes. See `task_content`, `model_pair` and `validate_context`
in [the implementation](../../scripts/evaluation/benchmark_protocol.py).

These packages contain fragments and resolved types, not a standalone compilable
Lean environment. No truncation or implicit retrieval is performed.

## Exported task layout

```text
tasks/
  index.json                 # Evaluator-side inventory, outside allowed task input
  <opaque-task-directory>/
    task.json
    input.json
    prediction.schema.json
```

`task.json` carries identity, mode, instructions, resource hashes and execution
policy. `input.json` contains the main pair, definition inventory, formal context
and limited environment context. The index binds package/task fingerprints and
development status. Hashes detect changes; they are not authentication.

Model-visible fields are allowlisted from the supplied package. Export omits
source links, labels, upstream evidence, preparation status and review queues.
Lean line and nested block comments are removed while strings and mathematical
definition values are preserved. In `theorem_only`, dependency Informal and
qualifications are also omitted; main qualifications remain visible.

Task directories must contain exactly the three listed files. Extra entries
and symlinked protocol files are rejected. The runner copies only these files
and validates the copy before launch. Export and run outputs require fresh paths.

## Predictions

The [prediction schema](prediction.schema.json) requires exactly `task_id`,
`verdict`, `issues` and `summary`.

- Verdicts are `aligned`, `misaligned` and `insufficient_information`.
- `misaligned` requires at least one issue; `aligned` requires no issues.
- Each issue names a supplied assessment declaration, a category and an explanation.
- Categories are `hypothesis`, `quantifier`, `definition`, `structure_constraint`,
  `conclusion` and `other`.
- Summary and explanations must contain non-whitespace text. Unknown fields and
  declaration IDs are rejected by local validation.

These are system predictions, not published ground truth. No hidden reasoning
is requested. Explanations should identify concrete semantic discrepancies.

```json
{
  "task_id": "Example.main",
  "verdict": "insufficient_information",
  "issues": [],
  "summary": "The supplied fragments do not provide the required notation context."
}
```

Replace the example ID with the actual task ID. Validate with:

```sh
python3 scripts/evaluation/benchmark_protocol.py validate \
  --task /absolute/path/to/task --submission /absolute/path/to/submission.json
```

## Execution and records

The [adapter contract](#local-adapter-contract) specifies paths and environment.
The runner launches argv directly without a shell, enforces a wall-clock budget
and kills the process group on timeout. It does not enforce filesystem/network
isolation, token limits or model/tool call quotas; those are adapter/deployment
responsibilities. A task-only input/no-external-retrieval policy is declared,
but launching inside a copied workspace alone does not enforce it.

Each run contains its task snapshot, `run.json`, stdout/stderr logs, a submission
if produced and a normalized prediction if valid. Status is `completed`,
`timeout`, `execution_failed` or `invalid_submission`. A completed abstention is
distinct from an execution failure. Input errors fail before adapter launch.
Retries use separate output directories and must not select the preferred
semantic verdict. Receipts disclose adapter-managed isolation and unenforced
network policy; they do not certify comparable execution environments.

## Local adapter contract

The runner launches argv once per task, without a shell. Its working directory
is a validated copy of the three-file task package. Use absolute paths for
adapter scripts and configuration. Environment variables are:

| Variable | Contract |
| --- | --- |
| `PAPERLEAN_TASK_DIR` | Absolute path to the copied three-file task package |
| `PAPERLEAN_SUBMISSION_PATH` | Absolute path where the adapter must write its final prediction JSON |
| `PAPERLEAN_TIMEOUT_SECONDS` | Wall-clock budget enforced by the runner |

The adapter must exit zero and produce a valid submission for a completed run.
stdout/stderr are diagnostic logs, not predictions. The runner inherits the
caller's environment; adapters manage authentication and any filesystem/network
isolation or tool/token limits. Task input and provider configuration are separate.

Provider-specific settings, commands and troubleshooting live in the
[evaluation tool guide](../../scripts/evaluation/README.md).

## Reference review and scoring

These are existing tool contracts, not the final annotation policy for the
current dataset. No scoring labels or review records are published. Explicit
[upstream evidence](../../metadata/upstream-evidence/README.md) is not a reference.
Review data stay outside task workspaces and are distinct from removed model
metadata reviews.

### Review records

`scripts/evaluation/benchmark_scoring.py prepare` creates a document with
`schema_version: paperlean-review-1` and pending `records`. It requires an
already exported `theorem_only` task inventory; it does not label anything.

| Field | Existing tool contract |
| --- | --- |
| `task_id`, `mode` | Exported task identity and `theorem_only` scope |
| `task_sha256`, `input_sha256` | Exact exported task and input bindings |
| `reference_ready` | Whether a binary adjudicated reference is ready for scoring |
| `status` | `pending`, `reviewed`, `adjudicated` or `unresolved` |
| `label` | `aligned` / `misaligned` after adjudication; otherwise null |
| `reviews` | Reviewer identities, verdicts and evidence |
| `adjudication` | Final identity, verdict and evidence; otherwise null |

The existing validator requires at least two distinct reviewer identities and a
final adjudication for `adjudicated`, with a binary label matching the final
verdict. It checks record structure and identities, not whether reviewers are
human, independent or qualified. These properties need a separately agreed
review process. The final adjudicator may be one of the reviewers in this format.

The assessment concerns the supplied main Informal and its qualifications,
using actual Formal dependency meanings. Hidden dependency Informal and proof
correctness are not criteria. Unresolved records retain null labels and
`reference_ready: false`. A confirmed mismatch can be scoring-ready; readiness
does not mean aligned. Input, instruction or schema changes require renewed
hash-bound review. Project-case input hashes are not task-export hashes.

### Scoring semantics

`target_count` is the fixed task inventory; `eligible` counts ready references.
Missing, pending and unresolved references are reported separately and are not
charged as model errors. Among eligible tasks, abstentions and failures remain
in the denominator.

| Metric | Formula |
| --- | --- |
| `accuracy` | correct / eligible |
| `answer_coverage` | valid binary answers / eligible |
| `answered_accuracy` | correct / valid binary answers |
| `target_correct_fraction` | correct / target_count; population coverage, not accuracy over unresolved references |

A zero denominator yields JSON null. Model `insufficient_information` is an
abstention, not a third gold class. Scores use each run's receipt and validated
prediction, not the aggregate predictions file. The batch/index, task hashes
and pinned review document must match. Failures cannot be overridden by a
stray prediction file. Retries require separately retained batches.
The scorer evaluates verdicts, not explanation quality or issue localization.

The compatibility option `--provisional-labels` accepts explicitly supplied,
export-input-bound external model labels for exploratory runs. No such labels
are bundled here, upstream evidence is not accepted in that format, and a
human-reviewed export rejects provisional references. Such scores remain
model-referenced development results, not benchmark ground truth.
