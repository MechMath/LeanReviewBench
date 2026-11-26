# Live model setup and troubleshooting

Use Python 3.11 or later. See the [adapter reference](ADAPTERS.md) for options and configuration precedence, and the [validation guide](../../docs/VALIDATION.md) for the complete offline workflow.

## Local configuration

Copy `.env.example` to `.env` in this directory and fill in a credential, base URL, and model authorized for testing. Local `.env` files are ignored by Git. Keep the file outside exported task directories and use an absolute path when invoking an adapter from the runner.

```sh
cp scripts/evaluation/.env.example scripts/evaluation/.env
```

Then use the normal protocol runner with this adapter command:

```sh
python3 /absolute/path/to/scripts/evaluation/responses_llm.py \
  --env-file /absolute/path/to/scripts/evaluation/.env
```

`OPENAI_BASE_URL` includes any API prefix, e.g. `https://api.openai.com/v1`. The adapter appends `/responses`. `OPENAI_API_KEY` and `OPENAI_MODEL` are required; `OPENAI_REASONING_EFFORT` is optional. Process environment variables override dotenv values. TOML configuration via `--config` remains an alternative; it cannot be combined with `--env-file`.

The dotenv parser supports literal KEY=VALUE, single/double quotes, `export`, blank lines, and comments. It does not execute shell expressions or interpolate variables. No key is bundled with the repository. An internal key must be supplied locally by an authorized user; the adapter does not reuse Codex login tokens.

Live tests send the selected public task content to the configured provider and may incur usage. Failures and semantic verdicts are recorded separately. Do not publish local credential files or raw provider errors.

## Offline checks

Run the offline suite without credentials or network access:

```sh
python3 -m unittest discover -s tests -v
```

Coverage includes dotenv and TOML configuration, request construction, split output text, metadata, incomplete/refused/empty responses, sanitized HTTP/connection failures without retries, and adapter-to-runner integration. The integration test replaces the HTTP boundary and checks accepted predictions and rejected task identities; it does not establish live provider compatibility.

Protocol regression tests also reject extra task files and symlinked resources, verify that copied workspaces contain only protocol files, and prevent batch resume after adapter code, declared dependencies, adapter version, or effective provider settings change. Configuration identity tests cover dotenv, TOML, environment precedence, and credential rotation without storing or hashing credentials.

## Live request

Export a frozen task using the [protocol example](README.md#example) before invoking the adapter. Select its directory from the export's `index.json`. Use a fresh output directory for each attempt:

```sh
python3 scripts/evaluation/benchmark_protocol.py run \
  --task /absolute/path/to/exported/task \
  --output build/llm-smoke/new-run --timeout 180 -- \
  python3 /absolute/path/to/scripts/evaluation/responses_llm.py \
  --env-file /absolute/path/to/scripts/evaluation/.env
```

If the configured base URL has no API prefix, explicitly test `--api-path /v1/responses`. Inspect `run.json` and `stderr.log` in the output directory. A failed request is an execution failure, not an alignment verdict.

## Troubleshooting

| Symptom | What to check |
| --- | --- |
| Missing key or model | Supply both required settings and check environment overrides |
| HTTP 401/403 | Verify credentials and model permissions with the selected provider |
| HTTP 404 | Check the base URL prefix and chosen endpoint suffix |
| HTTP 429 | Check provider quota/rate limits; the adapter does not retry automatically |
| HTTP 502 | Inspect a sanitized provider error during diagnosis; a gateway may wrap request-validation errors as 502 |
| Incomplete response | Check metadata status, token limit, and provider behavior |
| Runner timeout | Check the wall-clock budget; the adapter reserves five seconds when setting its request timeout, with a one-second minimum |
| Invalid submission | Inspect final JSON for task identity, required fields, supported verdicts, and issue consistency |
| Resume configuration differs | Compare task index, runner, adapter files, declared dependencies, and effective model settings; intentional changes require a new batch |

Normal adapter logs deliberately omit provider error bodies. During manual diagnosis, extract only the necessary sanitized message and request ID; avoid saving complete provider responses or credentials. Retain failures separately from later successful attempts.
