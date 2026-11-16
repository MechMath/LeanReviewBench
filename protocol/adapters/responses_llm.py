#!/usr/bin/env python3
"""Single-request Responses adapter with external TOML, dotenv, or environment settings."""
import argparse
import json
import os
import re
from pathlib import Path
import sys
import time
import tomllib
import urllib.error
import urllib.request


def load_dotenv(path):
    """Read literal KEY=VALUE entries; no shell evaluation or interpolation."""
    values = {}
    for number, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        if line.startswith('export '):
            line = line[7:].lstrip()
        match = re.fullmatch(r'([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)', line)
        if not match:
            raise ValueError(f'Invalid dotenv entry at line {number}')
        key, value = match.groups()
        if value.startswith(('"', "'")):
            if len(value) < 2 or value[-1] != value[0]:
                raise ValueError(f'Invalid dotenv quoting at line {number}')
            value = value[1:-1]
        else:
            value = re.split(r'\s+#', value, maxsplit=1)[0].rstrip()
        values[key] = value
    return values


def settings(args):
    env = load_dotenv(args.env_file.expanduser()) if args.env_file else {}
    env.update(os.environ)  # Process environment takes precedence over dotenv.
    if args.config:
        config = tomllib.loads(args.config.expanduser().read_text())
        provider = config['model_providers'][config['model_provider']]
        if provider.get('wire_api') != 'responses':
            raise ValueError('This adapter requires a Responses provider')
        token = provider.get('experimental_bearer_token') or env.get(provider.get('env_key', 'OPENAI_API_KEY'))
        base, model = provider['base_url'], config['model']
        effort = config.get('model_reasoning_effort')
    else:
        token = env.get('OPENAI_API_KEY')
        base = env.get('OPENAI_BASE_URL', 'https://api.openai.com/v1')
        model = env.get('OPENAI_MODEL')
        effort = env.get('OPENAI_REASONING_EFFORT')
    if not token or not model:
        raise ValueError('API key and model are required; set OPENAI_API_KEY and OPENAI_MODEL')
    endpoint = base.rstrip('/') + args.api_path
    if not endpoint.startswith('https://'):
        raise ValueError('HTTPS endpoint required')
    return token, endpoint, model, effort


def argument_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument('--config', type=Path)
    source.add_argument('--env-file', type=Path)
    parser.add_argument('--max-output-tokens', type=int, default=4096)
    parser.add_argument('--max-input-bytes', type=int, default=500000)
    parser.add_argument('--api-path', default='/responses', choices=('/responses', '/v1/responses'))
    return parser


def main():
    args = argument_parser().parse_args()
    token, endpoint, model, effort = settings(args)
    directory = Path(os.environ['PAPERLEAN_TASK_DIR'])
    submission = Path(os.environ['PAPERLEAN_SUBMISSION_PATH'])
    task = json.loads((directory / 'task.json').read_text())
    schema = json.loads((directory / 'prediction.schema.json').read_text())
    if args.max_input_bytes <= 0 or args.max_output_tokens <= 0:
        raise ValueError('Input and output limits must be positive')
    payload = json.loads((directory / 'input.json').read_text())
    body = {'model': model, 'store': False,
            'instructions': task['instructions'] + '\nReturn only the final JSON object. Output schema:\n' + json.dumps(schema),
            'input': [{'role': 'user', 'content': 'Return a JSON object for this task:\n' +
                       json.dumps({**payload, 'task_id': task['task_id']}, ensure_ascii=False)}],
            'max_output_tokens': args.max_output_tokens,
            'text': {'format': {'type': 'json_object'}}}
    if effort:
        body['reasoning'] = {'effort': effort}
    timeout = max(1, float(os.environ.get('PAPERLEAN_TIMEOUT_SECONDS', '180')) - 5)
    start = time.monotonic()
    result = {}
    requests = []
    outcome = 'running'
    termination = None

    def persist():
        metadata = {'model_requested': model, 'model_returned': result.get('model'),
                    'response_id': result.get('id'), 'status': result.get('status'),
                    'outcome': outcome, 'termination_reason': termination,
                    'usage': result.get('usage'), 'elapsed_seconds': time.monotonic() - start,
                    'max_output_tokens': args.max_output_tokens, 'reasoning_effort': effort,
                    'requests': requests, 'store_requested': False}
        submission.with_name('llm_metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')

    persist()
    try:
        encoded = json.dumps(body, ensure_ascii=False).encode()
        preflight = {'input_bytes': len(encoded), 'max_input_bytes': args.max_input_bytes,
                     'within_budget': len(encoded) <= args.max_input_bytes,
                     'measurement': 'UTF-8 request body bytes; not tokens'}
        submission.with_name('input_preflight.json').write_text(json.dumps(preflight, indent=2) + '\n')
        if not preflight['within_budget']:
            raise RuntimeError('Model input exceeds byte budget; no truncation performed; see input_preflight.json')
        remaining = timeout - (time.monotonic() - start)
        if remaining <= 0:
            raise RuntimeError('Adapter wall-clock budget exhausted')
        request = urllib.request.Request(endpoint, data=encoded,
                                         headers={'Authorization': 'Bearer ' + token, 'Content-Type': 'application/json'})
        try:
            with urllib.request.urlopen(request, timeout=remaining) as response:
                result = json.load(response)
        except urllib.error.HTTPError as error:
            raise RuntimeError(f'Provider HTTP status {error.code}') from None
        except urllib.error.URLError:
            raise RuntimeError('Provider connection failed') from None
        except TimeoutError:
            raise RuntimeError('Provider request timed out') from None
        requests.append({'response_id': result.get('id'), 'status': result.get('status'),
                         'usage': result.get('usage'), 'input_bytes': len(encoded)})
        if any(item.get('type') == 'function_call' for item in result.get('output', [])):
            raise RuntimeError('Unexpected tool call; this adapter requires a final JSON response')
        text = ''.join(c.get('text', '') for item in result.get('output', []) if item.get('type') == 'message'
                       for c in item.get('content', []) if c.get('type') == 'output_text')
        submission.with_name('llm_output.txt').write_text(text)
        if result.get('status') != 'completed':
            raise RuntimeError('Provider response did not complete; see metadata')
        prediction = json.loads(text)
        submission.write_text(json.dumps(prediction, ensure_ascii=False, indent=2) + '\n')
        outcome = 'prediction_returned'  # Runner separately validates the protocol.
        termination = 'final_answer'
    except Exception as error:
        outcome = 'failed'
        termination = str(error) if isinstance(error, RuntimeError) else type(error).__name__
        raise
    finally:
        persist()


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(f'{type(error).__name__}: {error}', file=sys.stderr)
        sys.exit(1)
