# System evaluation protocol

Protocol v1 evaluates statement alignment systems, including single-call models, tool-using models, and autonomous agents. It specifies task delivery and final submissions independently of a model vendor or agent framework. The implemented transport is a local subprocess. HTTP sessions, remote polling, automatic retries, and parallel scheduling are not implemented. Binary verdict scoring for reviewed `theorem_only` tasks is available through the [review and scoring workflow](review/README.md). Sequential batch execution and explicit resume are available.

Use Python 3.11 or later for the bundled Responses adapter and complete test suite. Start with the mock example below, then consult the [adapter reference](adapters/README.md), [validation guide](../docs/testing.md), and [live test setup](testing/README.md).

## Task semantics and modes

A task contains one main theorem and the def/structure inventory selected from existing AST extraction. Definition bodies and structure constraints determine statement meaning. Proof correctness is outside the task.

- `full`: main theorem and dependency Informal descriptions are visible. Assess both the main theorem and supplied definition pairs.
- `theorem_only`: only main theorem Informal is visible. Infer dependency meanings from Formal and assess the final statement. Hidden reference descriptions are not judgement criteria.

Verdicts can differ between modes; do not assume every internal description mismatch is observable in theorem_only. Other retained project graph nodes are supplied as formal interpretation context outside the paired assessment inventory. The v1 task package supplies fragments and resolved types, not a standalone compilable Lean environment. Supply a complete package inventory with `export --packages /absolute/path/to/evaluation-packages.jsonl`; the retained CSV batches still need a native evaluation export. Use `insufficient_information` if essential context is unavailable. No truncation or implicit retrieval is performed.

Current references are unreviewed and some descriptions are generated or paraphrased from Lean. Export refuses them by default; `--allow-draft` explicitly enables development runs. In `theorem_only`, `--reviews` supplies hash-bound, adjudicated main-statement references independently of hidden dependency descriptions. In `full`, the package-wide reference completion/review gate remains in force. Draft status is recorded in the export index, outside model-visible task content. Development runs are not official benchmark scores.

## Task package

```text
tasks/
  index.json
  <opaque-task-directory>/
    task.json
    input.json
    prediction.schema.json
```

`task.json` contains `protocol_version`, stable `task_id`, mode, instructions, resource hashes, and execution policy. `input.json` contains the main theorem, dependency pairs, formal dependency context, and limited environment context. `index.json` records original package fingerprints and task-manifest hashes. Hashes detect accidental changes; they are not signatures or authentication.

Model inputs are allowlisted from frozen released evaluation packages. Labels, preparation status, original raw comments, paper links, and review queues are omitted. Lean line and nested block comments are removed from Formal in both modes; string contents are preserved. In theorem_only, dependency Informal and its qualifiers are omitted as well. Main theorem qualifications are always included. Comments are presentation metadata; mathematical definition bodies are preserved.

Export paths are newly created. Export never overwrites an existing task directory. Keep indexes and evaluation-side material outside the system's allowed input workspace.

Task directories must contain exactly `task.json`, `input.json`, and `prediction.schema.json`. Extra files or directories and symlinked protocol files are rejected before launching an adapter. The runner copies only these three files and validates the copied package before launch.

## Local adapter contract

The runner invokes an argv command directly, without a shell, once per task. The adapter may implement one model request or an arbitrary internal agent loop. Its current working directory is a copy of the task package. Environment variables are:

| Variable | Meaning |
| --- | --- |
| `PAPERLEAN_TASK_DIR` | Absolute path to the task package |
| `PAPERLEAN_SUBMISSION_PATH` | Absolute path where final JSON must be written |
| `PAPERLEAN_TIMEOUT_SECONDS` | Wall-clock budget enforced by the runner |

Exit code zero indicates execution success; a valid submission must also exist. stdout and stderr are logs, not predictions. The adapter must read task instructions and submit exactly one final object. API authentication and provider configuration are the adapter's responsibility; credentials must not be written into tasks or command arguments.

The runner inherits the caller's environment. It enforces wall-clock timeout and kills the process group on timeout. It does not isolate the filesystem, disable networking, cap tokens, limit tool/model calls, or sanitize arbitrary agent execution. Use trusted adapters for local development. For comparable restricted Agent runs, the adapter or deployment must enforce task-only filesystem access and no external information retrieval. A model service connection may carry task requests, but is not permission to browse outside resources. Launching from a task directory alone is not isolation. Runner receipts explicitly record isolation as adapter-managed and network enforcement as false.

No chain-of-thought is requested. Final explanations should identify concrete semantic discrepancies. Tools and model usage may be logged by adapters, but are not yet a standardized v1 event stream.

## Submission contract

See [prediction.schema.json](v1/prediction.schema.json). Required fields are `task_id`, `verdict`, `issues`, and `summary`; unknown fields are rejected.

- Verdicts: `aligned`, `misaligned`, `insufficient_information`.
  The paper calls the last verdict `undetermined`; `insufficient_information` is its JSON encoding.
- `misaligned` requires at least one issue; `aligned` requires an empty issue list.
- Each issue identifies a supplied declaration, a category, and a nonempty explanation.
- Categories: hypothesis, quantifier, definition, structure_constraint, conclusion, other.
- Summary and explanations must contain non-whitespace text.

The validator checks task identity and known declaration IDs in addition to JSON structure. It does not establish semantic correctness.

For example, a structurally valid result for a task whose ID is `Example.main` is:

```json
{
  "task_id": "Example.main",
  "verdict": "insufficient_information",
  "issues": [],
  "summary": "The supplied fragments do not provide the required notation context."
}
```

Replace the example ID with the actual task ID. JSON Schema describes the submission shape; the local validator additionally rejects whitespace-only explanations and unknown declaration IDs.

## Example

From the repository root:

```sh
python3 scripts/benchmark_protocol.py export \
  --packages /absolute/path/to/evaluation-packages.jsonl \
  --mode theorem_only --allow-draft --output build/protocol-demo/tasks
```

Use `index.json` to locate the task directory, then run an adapter with absolute paths:

```sh
python3 scripts/benchmark_protocol.py run \
  --task /absolute/path/to/task-directory \
  --output build/protocol-demo/run --timeout 300 \
  -- python3 /absolute/path/to/protocol/v1/mock_system.py
```

The mock deliberately returns `insufficient_information`; it tests plumbing only. Real model/Agent integrations replace the command. A file-based integration can consume task packages independently and validate its submission with:

```sh
python3 scripts/benchmark_protocol.py validate \
  --task /absolute/path/to/task-directory --submission /path/to/submission.json
```

## Run records and failures

Each run writes its own directory with a task snapshot, `stdout.log`, `stderr.log`, `submission.json` if produced, normalized `prediction.json` if valid, and `run.json`. Existing run directories cannot be reused. The receipt records command, task identity/hash, mode, elapsed time, timeout, exit code where available, and status.

Statuses are `completed`, `timeout`, `execution_failed`, or `invalid_submission`. A completed run may have an `insufficient_information` verdict; this is distinct from execution failure. Input errors fail before launching the adapter. The CLI returns nonzero for failure. Retrying creates a separate run and must not select results according to their semantic verdict.

Official scoring requires reviewed references, semantic labels, declared execution capabilities, and reproducible resource constraints. The separate theorem-only scorer computes verdict accuracy, answer coverage, and answered accuracy against adjudicated references. The transport does not certify sandbox enforcement or model comparability. Future transports must preserve task identity, input visibility, final submission semantics, and separate execution failures from semantic outcomes.

## Sequential batch execution and resume

```sh
python3 scripts/benchmark_protocol.py batch \
  --tasks build/protocol-v1-all/theorem-only \
  --output build/protocol-batch-demo --timeout 300 \
  -- python3 /absolute/path/to/protocol/v1/mock_system.py
```

Prepare that task export first with `python3 scripts/benchmark_protocol.py export --packages /absolute/path/to/evaluation-packages.jsonl --mode theorem_only --allow-draft --output build/protocol-v1-all/theorem-only`. Choose a fresh directory if it already exists. The [validation guide](../docs/testing.md) includes a complete offline batch-and-resume example for both modes.

Repeat the exact command with `--resume` before `--` to continue. The runner validates all indexed task hashes before starting. Resume requires identical task index, adapter argv, timeout and runner version. Existing finished runs, including failed runs, are retained without re-execution. An incomplete run directory requires inspection; resume refuses to overwrite it. To retry failures, create a separate batch and retain both results.

`batch.json` also records hashes of the resolved executable and existing file arguments, including adapter scripts. File arguments must use absolute paths because adapters execute inside the task workspace. For the bundled Responses adapter, it records the effective endpoint, model, reasoning effort, and output token limit after applying configuration and environment precedence. Credential configuration files are excluded from file hashing; tokens are neither stored nor hashed. Credential rotation alone does not change batch identity. Effective provider settings and launch-file hashes are checked again before each task and on resume; changes reject continuation. Batches created before this identity record was introduced cannot be resumed with the updated runner.

For custom adapters, declare additional imported code, prompts, or configuration files with repeatable `--fingerprint-file /absolute/path/to/file` options before `--`. Use `--adapter-version VERSION` for a pinned package/container revision or other external dependencies. These declarations are part of batch identity. Automatic inspection covers local file arguments and the bundled Responses settings; it cannot discover arbitrary imports, custom environment settings, or remote service revisions. Declare those dependencies explicitly. Do not pass credential files to `--fingerprint-file`.

Each batch contains `batch.json`, one run directory per task, `predictions.jsonl`, and `summary.json`. Summary counts execution statuses and verdicts, total execution time, completed coverage and development tasks; it does not compute semantic accuracy. A batch exits nonzero if any task failed. Concurrent writers to the same batch are rejected by a lock. A forced crash may leave `.running`; remove it only after confirming no batch writer remains. No automatic retry, quota for model/tool calls, or parallel scheduling is provided.

## Responses LLM adapter

`adapters/responses_llm.py` sends the complete exported task input in a single model request, using an external Codex TOML provider configuration, a local dotenv file, or process environment variables. It reads the configured model, reasoning effort, HTTPS base URL, and bearer token (or provider `env_key`). Requires Python 3.11+ for `tomllib`. See [live test setup](testing/README.md) for dotenv configuration and offline verification. Supply its absolute path as the process command:

```sh
python3 /absolute/path/to/protocol/adapters/responses_llm.py \
  --config /path/to/external.config.toml
```

The default endpoint suffix is `/responses`; `--api-path /v1/responses` supports a base URL without an API prefix. The adapter requests JSON object output with the protocol schema in instructions; local validation remains authoritative. Requests use `store: false`. The adapter uses no tools or automatic retries. Oversized requests fail before transport without truncation; see the [adapter reference](adapters/README.md) for configuration and input limits. Provider compatibility is determined by actual integration, not by the configuration format.

Secrets are read at runtime and are not copied into task inputs or request logs. Only configuration paths appear in command receipts. Provider HTTP error bodies are not logged. Successful responses produce `llm_output.txt` and `llm_metadata.json` (model, response status/ID, usage, reasoning effort, output limit, elapsed time) alongside the submission. No hidden reasoning is requested or saved.

Offline tests mock provider responses; they do not certify live provider compatibility. Use the [live test guide](testing/README.md) to verify your configured endpoint. Generated run artifacts belong under ignored `build/`.

## Formal dependency context

Released evaluation package format `paperlean-evaluation-1` supplies `formal_context` in both task modes. Its `declarations` array contains the remaining project closure nodes (including abbreviations, classes, inductive types, constructors, and generated helpers) with formal types and retained non-proof values. Its `external_nodes` array records library-boundary identities and types; its `edges` array preserves the complete retained dependency graph across assessment pairs, context declarations, and external nodes. Context carries no informal descriptions or review metadata. Lean comments are removed from context text before model delivery, just as for assessment pairs.

Validation rejects duplicate identities, dangling edges, disconnected closures, unexpected context fields, proof bodies, and definition-value traversal from theorem/proof nodes. Issues must still refer to the main theorem or a paired definition; explain context-related uncertainty against the affected assessment target. Context does not expand the set of informal pairs to judge. No truncation is performed, so larger closures may exceed a provider's input capacity.

Export task directories directly from the released packages. Legacy external `paperlean-full-draft-2` packages with complete formal context are also accepted; no preparation tools are required. The transport version remains `paperlean-protocol-1`, but old task snapshots without `formal_context` are no longer accepted by this runner. Task hashes distinguish expanded inputs from historical inputs, and old batches must not be resumed with the new runner.

## Retained references

The four reviewed project-case batches retain provisional records under
`references/`, outside model-visible task directories. These are not frozen
scoring references; the project-case format still needs an evaluation export
and exact input bindings. See the [reference guide](../references/README.md).

OpenAI, FLT and Kakeya datasets and references are archived on `11_9_shenhao`
and are no longer bundled with main. Historical `--dataset` commands apply
only in a checkout containing that archived release.
