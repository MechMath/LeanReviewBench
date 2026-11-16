# Evaluation tools

This guide covers task export, model/agent execution, provider setup and scoring.
The [versioned protocol](PROTOCOL.md) defines input visibility,
adapter I/O, predictions and export-bound references. Implementations are:

| Script | Role |
| --- | --- |
| [benchmark_protocol.py](benchmark_protocol.py) | Export, validate, run and resume sequential batches |
| [responses_llm.py](responses_llm.py) | Single-request Responses adapter |
| [mock_system.py](mock_system.py) | Offline adapter that always abstains |
| [benchmark_scoring.py](benchmark_scoring.py) | Prepare pending reference records and score exported tasks |

The twelve-batch project-case candidate has no native evaluation export or
gold scoring labels. Provisional reviews remain outside model inputs in
`metadata/labels/` and `references/`. Export requires a separately supplied complete JSONL;
it does not construct packages from CSV indexes or Lean sources. Upstream evidence
is not a scoring reference. Development execution is not an official score.

Use Python 3.11+. Commands run from the repository root; generated tasks, reviews
and runs belong under ignored `build/`, outside published data.

## Offline checks

```sh
python3 -m unittest discover -s tests -p 'test_benchmark_protocol.py' -v
```

These tests use temporary synthetic packages and mocked model responses. They
need no labels, Lean, credentials or network access. See the repository-wide
[testing guide](../../docs/testing.md) for the full suite. Offline tests do not
establish live provider compatibility.

## Export and run

Supply an existing JSONL matching the [export contract](PROTOCOL.md#export-input).
Export and run outputs require fresh paths:

```sh
python3 scripts/evaluation/benchmark_protocol.py export \
  --packages /absolute/path/to/evaluation-packages.jsonl \
  --mode theorem_only --allow-draft --output build/evaluation/tasks
```

Read the export's `index.json` to locate a task directory, then run the mock:

```sh
python3 scripts/evaluation/benchmark_protocol.py run \
  --task /absolute/path/to/exported-task-directory \
  --output build/evaluation/mock-run --timeout 30 -- \
  python3 "$PWD/scripts/evaluation/mock_system.py"
```

The mock returns `insufficient_information` and checks transport only.
`--allow-draft` permits development execution without reference approval. Use
`--mode full` when supplied dependency Informal pairs should also be assessed.
Mode-specific visibility and readiness are defined in the protocol.

Validate a separately produced submission with:

```sh
python3 scripts/evaluation/benchmark_protocol.py validate \
  --task /absolute/path/to/exported-task-directory \
  --submission /absolute/path/to/submission.json
```

## Model provider setup

The [blank template](.env.example) lives next to the adapter. To use dotenv,
copy it locally and supply a credential, endpoint and model:

```sh
cp scripts/evaluation/.env.example scripts/evaluation/.env
```

Local `.env` files are ignored. Process environment overrides dotenv settings:

| Variable | Requirement |
| --- | --- |
| `OPENAI_API_KEY` | Required bearer token |
| `OPENAI_MODEL` | Required model supported by the configured provider |
| `OPENAI_BASE_URL` | Defaults to `https://api.openai.com/v1`; include the API prefix |
| `OPENAI_REASONING_EFFORT` | Optional provider setting |

Dotenv accepts literal values, quotes, optional `export`, blank lines and comments.
It does not run shell expressions or interpolate variables. Credentials stay
outside task inputs; model settings are separate from Lean dependencies.

```sh
python3 scripts/evaluation/benchmark_protocol.py run \
  --task /absolute/path/to/exported-task-directory \
  --output build/evaluation/model-run --timeout 180 -- \
  python3 "$PWD/scripts/evaluation/responses_llm.py" \
  --env-file "$PWD/scripts/evaluation/.env"
```

The adapter sends the full task in one request, includes the prediction schema
in instructions and requests JSON output. It has no tools or automatic retries.
Live requests send task content to the provider and may incur usage.

| Option | Default | Use |
| --- | --- | --- |
| `--env-file PATH` | None | Literal dotenv settings |
| `--config PATH` | None | External TOML; mutually exclusive with `--env-file` |
| `--api-path` | `/responses` | `/responses` or `/v1/responses` appended to the base URL |
| `--max-output-tokens` | `4096` | Response token limit |
| `--max-input-bytes` | `500000` | Reject oversized requests before transport, without truncation |

TOML mode reads `model`, `model_provider`, optional `model_reasoning_effort` and
the selected `model_providers` entry. That provider requires `wire_api = "responses"`
and an HTTPS `base_url`. Authentication uses `experimental_bearer_token` or the
environment variable specified by `env_key` (default `OPENAI_API_KEY`). The
adapter does not reuse Codex login tokens. A valid config does not certify live
provider compatibility.

The adapter writes `input_preflight.json`, checkpoints `llm_metadata.json` and
produces `llm_output.txt` when processing final response text. Metadata includes
model, response status/ID, usage, elapsed time and effective generation limits.
It does not save hidden reasoning or the full provider response; `store: false`
is requested. HTTP error bodies are omitted from normal logs. Invalid/incomplete
responses fail separately from valid alignment predictions.

| Symptom | Check |
| --- | --- |
| Missing key/model or 401/403 | Required settings, overrides and provider permissions |
| 404 | Base URL prefix and endpoint suffix |
| 429 or gateway failure | Quota, availability and sanitized diagnostic message |
| Incomplete response or timeout | Metadata, token limit and wall-clock budget |
| Invalid submission | Task identity, fields, verdict and issue consistency |
| Resume rejected | Task/index, code, dependencies and effective provider settings |

## Batches and custom adapters

```sh
python3 scripts/evaluation/benchmark_protocol.py batch \
  --tasks build/evaluation/tasks --output build/evaluation/batch --timeout 30 -- \
  python3 "$PWD/scripts/evaluation/mock_system.py"
```

Repeat the exact command with `--resume` before `--` to continue. Execution is
sequential; finished runs, including failures, are retained without re-execution.
Resume requires identical task/index hashes, timeout, runner and adapter identity.
Intentional retries use separate outputs. Concurrent writers are rejected;
a crash may leave `.running`, requiring inspection before removing the lock.

Each batch writes `batch.json`, per-task runs, `predictions.jsonl` and
`summary.json`. The summary reports execution/verdict counts, not accuracy;
the batch exits nonzero if a task fails. No retries or parallel scheduling are
automatic. The runner enforces a process timeout; adapters/deployment enforce
filesystem/network restrictions and model/tool budgets.

Custom adapters obey the [local adapter contract](PROTOCOL.md#local-adapter-contract).
Declare other code, prompts or config with repeatable
`--fingerprint-file /absolute/path/to/file` and external revisions with
`--adapter-version VERSION`, before `--`. File arguments must be absolute,
since execution uses a task copy. Keep credentials out of fingerprints.
Bundled Responses batch identity includes effective non-secret provider settings
and launch-file hashes; credential files are excluded, allowing credential rotation.
Arbitrary imports, custom environment and remote revisions need explicit declarations.

## Scoring setup

The [reference/scoring contract](PROTOCOL.md#reference-review-and-scoring)
describes existing tooling, not the final annotation policy. Prepare pending
records from an exported theorem-only inventory:

```sh
python3 scripts/evaluation/benchmark_scoring.py prepare \
  --tasks build/evaluation/tasks --output build/evaluation/pending-reviews.json
```

This labels nothing. After a separately completed review process, export a fresh
inventory using `--reviews /absolute/path/to/adjudicated-reviews.json` instead of
`--allow-draft`. The index binds the review document hash; every selected record
must match the exact task/input hashes. Theorem-only reviews cannot bypass the
package-wide `full` readiness gate. Keep reviews outside task directories. Run a
batch against that exact reviewed export, then score:

```sh
python3 scripts/evaluation/benchmark_scoring.py score \
  --tasks /absolute/path/to/reviewed-task-export \
  --reviews /absolute/path/to/adjudicated-reviews.json \
  --batch /absolute/path/to/matching-batch \
  --output build/evaluation/score.json
```

Use the fixed task population and retain failures/abstentions. Development runs
and external provisional model references do not become benchmark ground truth.
This publication supplies neither final references nor a canonical task export.
