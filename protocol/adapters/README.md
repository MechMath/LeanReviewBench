# Model and agent adapters

An adapter is a trusted executable launched once per task by the [local protocol runner](../README.md). It reads the copied task package through `PAPERLEAN_TASK_DIR` and writes one final prediction to `PAPERLEAN_SUBMISSION_PATH`. Use absolute paths for scripts and configuration because the runner changes the working directory to the task workspace. Logs are diagnostic; stdout is not a submission.

## Responses adapter

`responses_llm.py` sends the complete exported task input in one model request. Python 3.11 or later is required. It includes the prediction schema in instructions and requests JSON object output. The runner validates the final prediction against task identity and protocol semantics.

| Option | Default | Purpose |
| --- | --- | --- |
| `--env-file PATH` | None | Read literal dotenv settings; process environment overrides them |
| `--config PATH` | None | Read external TOML provider settings; mutually exclusive with `--env-file` |
| `--api-path` | `/responses` | Choose `/responses` or `/v1/responses` to append to the base URL |
| `--max-output-tokens` | `4096` | Set the response output limit |
| `--max-input-bytes` | `500000` | Reject an oversized request before contacting the provider |

Without a configuration file, settings come from the process environment. Dotenv mode uses the same names:

| Variable | Requirement |
| --- | --- |
| `OPENAI_API_KEY` | Required bearer token |
| `OPENAI_MODEL` | Required model name supported by the selected provider |
| `OPENAI_BASE_URL` | Defaults to `https://api.openai.com/v1`; include the API prefix if needed |
| `OPENAI_REASONING_EFFORT` | Optional value passed through to the provider |

Dotenv entries are literal: blank lines, comments, optional `export`, and single/double quotes are supported. Shell commands, substitutions, and variable interpolation are not evaluated. See [live setup](../testing/README.md) for the local template and a complete runner command.

TOML mode reads `model`, `model_provider`, optional `model_reasoning_effort`, and the selected entry in `model_providers`. That provider must have `wire_api = "responses"` and an HTTPS `base_url`. Authentication uses `experimental_bearer_token` if present, otherwise the environment variable named by `env_key` (default `OPENAI_API_KEY`). Compatibility depends on the actual provider response, not the configuration file format.

## Artifacts and failures

The adapter checkpoints `llm_metadata.json` alongside the submission path throughout execution, including failures, and writes `llm_output.txt` when processing a final response. Metadata includes requested/returned model, response ID and status, usage, elapsed time, reasoning effort, and output limit. It does not save the complete response or hidden reasoning. `store: false` is requested from the provider. `input_preflight.json` records request size and the input byte limit; oversized inputs fail without truncation. There are no tools or automatic retries.

An incomplete response, connection failure, HTTP error, or unparseable final JSON causes a nonzero exit. HTTP error bodies are omitted from normal logs. The runner records these as `execution_failed`; an adapter that exits successfully but submits a protocol-invalid prediction is recorded as `invalid_submission`. Neither is an alignment verdict.

## Batch identity and custom adapters

For this bundled adapter, the runner records effective non-secret model settings and launch-file hashes. It excludes the TOML/dotenv credential file from hashing and allows credential rotation. Model, endpoint, reasoning effort, output limit, or adapter code changes require a new batch.

Custom adapters can implement internal agent loops under the same submission contract. Declare additional local dependencies with repeatable `--fingerprint-file` options and external revisions with `--adapter-version`, before the runner's `--` separator. For example:

```sh
python3 scripts/benchmark_protocol.py batch \
  --tasks build/custom-tasks --output build/custom-runs \
  --fingerprint-file /absolute/path/to/prompt.txt \
  --adapter-version agent-v1 -- \
  python3 /absolute/path/to/agent.py
```

The runner cannot discover arbitrary imported code, custom environment configuration, or remote revisions. Declare those dependencies explicitly, keeping credential files out of fingerprint inputs. Adapters remain responsible for filesystem/network restrictions and any tool or model-call budget; the runner enforces only its process timeout.
