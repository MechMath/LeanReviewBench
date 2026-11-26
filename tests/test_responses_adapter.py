import argparse
import importlib.util
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
import urllib.error
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('adapter', Path(__file__).resolve().parents[1] / 'scripts/evaluation/responses_llm.py')
A = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(A)


class AdapterTests(unittest.TestCase):
    def invoke(self, directory, response=None, error=None, options=(), expected_requests=1):
        task = directory / 'task'
        task.mkdir(exist_ok=True)
        (task / 'task.json').write_text(json.dumps({
            'task_id': 'Root', 'mode': 'full', 'instructions': 'Assess statements.'}))
        (task / 'input.json').write_text(json.dumps({
            'main_theorem': {'id': 'Root', 'kind': 'theorem', 'formal': {'type': 'True'}, 'informal': 'True'},
            'definitions': [], 'formal_context': {'declarations': [
                {'id': 'Alias', 'kind': 'abbrev', 'formal': {'type': 'Type', 'value': 'Nat'}}],
                'external_nodes': [], 'edges': [{'source': 'Root', 'target': 'Alias', 'site': 'type'}]},
            'context': {'standalone_lean': False}}))
        (task / 'prediction.schema.json').write_text('{"type":"object"}')
        env = {'OPENAI_API_KEY': 'test-secret', 'OPENAI_MODEL': 'test-model',
               'OPENAI_BASE_URL': 'https://example.test/v1',
               'PAPERLEAN_TASK_DIR': str(task),
               'PAPERLEAN_SUBMISSION_PATH': str(directory / 'submission.json'),
               'PAPERLEAN_TIMEOUT_SECONDS': '30'}
        with patch.dict(os.environ, env, clear=True), patch('sys.argv', ['adapter', *options]), \
                patch.object(A.urllib.request, 'urlopen') as send:
            if error is not None:
                send.side_effect = error
            elif isinstance(response, list):
                send.side_effect = [io.BytesIO(json.dumps(r).encode()) for r in response]
            else:
                send.return_value = io.BytesIO(json.dumps(response).encode())
            try:
                A.main()
            finally:
                self.assertEqual(send.call_count, expected_requests)
        return send.call_args

    def response(self, **updates):
        prediction = {'task_id': 'Root', 'verdict': 'aligned', 'issues': [], 'summary': 'Matches.'}
        encoded = json.dumps(prediction)
        result = {'id': 'resp_test', 'model': 'returned-model', 'status': 'completed',
                  'usage': {'output_tokens': 12}, 'output': [
                      {'type': 'reasoning', 'summary': [], 'content': 'PRIVATE'},
                      {'type': 'message', 'content': [
                          {'type': 'output_text', 'text': encoded[:20]},
                          {'type': 'output_text', 'text': encoded[20:]}]}]}
        result.update(updates)
        return result

    def test_request_and_completed_response(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            args = self.invoke(directory, self.response())
            request = args.args[0]
            self.assertEqual(request.full_url, 'https://example.test/v1/responses')
            self.assertEqual(request.get_header('Authorization'), 'Bearer test-secret')
            self.assertGreater(args.kwargs['timeout'], 24)
            self.assertLessEqual(args.kwargs['timeout'], 25)
            body = json.loads(request.data)
            self.assertEqual(body['model'], 'test-model')
            self.assertFalse(body['store'])
            self.assertNotIn('tools', body)
            self.assertNotIn('reasoning', body)
            self.assertEqual(body['text']['format'], {'type': 'json_object'})
            content = body['input'][0]['content']
            self.assertIn('json', content.lower())
            self.assertEqual(json.loads(content.split('\n', 1)[1])['task_id'], 'Root')
            self.assertEqual(json.loads(content.split('\n', 1)[1]),
                             {**json.loads((directory / 'task/input.json').read_text()), 'task_id': 'Root'})
            self.assertIn('Output schema:', body['instructions'])
            self.assertEqual(json.loads((directory / 'submission.json').read_text())['verdict'], 'aligned')
            metadata = json.loads((directory / 'llm_metadata.json').read_text())
            self.assertEqual(metadata['response_id'], 'resp_test')
            self.assertEqual(metadata['usage'], {'output_tokens': 12})
            artifacts = ''.join(p.read_text() for p in directory.iterdir() if p.is_file())
            self.assertNotIn('test-secret', artifacts)
            self.assertNotIn('PRIVATE', artifacts)

    def test_unsuccessful_responses_never_create_submission(self):
        for response, expected in [
                (self.response(status='incomplete'), RuntimeError),
                (self.response(output=[]), json.JSONDecodeError),
                (self.response(output=[{'type': 'message', 'content': [
                    {'type': 'refusal', 'refusal': 'Cannot respond'}]}]), json.JSONDecodeError)]:
            with self.subTest(response=response), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                with self.assertRaises(expected):
                    self.invoke(directory, response)
                self.assertFalse((directory / 'submission.json').exists())
                self.assertTrue((directory / 'llm_metadata.json').exists())

    def test_provider_errors_are_sanitized_and_not_retried(self):
        for error, message in [
                (urllib.error.HTTPError('https://example.test', 502, 'test-secret', {},
                                        io.BytesIO(b'test-secret')), 'Provider HTTP status 502'),
                (urllib.error.URLError('test-secret'), 'Provider connection failed')]:
            with self.subTest(message=message), tempfile.TemporaryDirectory() as temp:
                with self.assertRaisesRegex(RuntimeError, message) as caught:
                    self.invoke(Path(temp), error=error)
                self.assertNotIn('test-secret', str(caught.exception))
                self.assertFalse((Path(temp) / 'submission.json').exists())

    def test_toml_provider_settings(self):
        with tempfile.TemporaryDirectory() as temp:
            config = Path(temp) / 'provider.toml'
            config.write_text('model="test-model"\nmodel_provider="test"\n'
                              'model_reasoning_effort="high"\n[model_providers.test]\n'
                              'wire_api="responses"\nbase_url="https://example.test/"\n'
                              'env_key="TEST_PROVIDER_KEY"\n')
            args = argparse.Namespace(config=config, env_file=None, api_path='/v1/responses')
            with patch.dict(os.environ, {'TEST_PROVIDER_KEY': 'secret'}, clear=True):
                self.assertEqual(A.settings(args),
                                 ('secret', 'https://example.test/v1/responses', 'test-model', 'high'))
            config.write_text(config.read_text().replace('https://', 'http://'))
            with patch.dict(os.environ, {'TEST_PROVIDER_KEY': 'secret'}, clear=True):
                with self.assertRaisesRegex(ValueError, 'HTTPS'):
                    A.settings(args)

    def test_dotenv_literals_and_environment_precedence(self):
        with tempfile.TemporaryDirectory() as temp:
            p = Path(temp) / '.env'
            p.write_text('# comment\nOPENAI_API_KEY="test-secret"\nOPENAI_MODEL=test-model\nOPENAI_BASE_URL=https://example.test/v1\nexport OPENAI_REASONING_EFFORT=medium # comment\nLITERAL=$(do-not-execute)\n')
            self.assertEqual(A.load_dotenv(p)['LITERAL'], '$(do-not-execute)')
            args = argparse.Namespace(env_file=p, config=None, api_path='/responses')
            with patch.dict(os.environ, {'OPENAI_MODEL': 'override'}, clear=True):
                token, endpoint, model, effort = A.settings(args)
            self.assertEqual((token, endpoint, model, effort), ('test-secret', 'https://example.test/v1/responses', 'override', 'medium'))
            p.write_text('OPENAI_API_KEY="unterminated\n')
            with self.assertRaises(ValueError):
                A.load_dotenv(p)

    def test_missing_configuration(self):
        args = argparse.Namespace(env_file=None, config=None, api_path='/responses')
        with patch.dict(os.environ, {}, clear=True):
            with self.assertRaises(ValueError):
                A.settings(args)

    def test_budget_rejects_before_network(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            with self.assertRaisesRegex(RuntimeError, 'exceeds byte budget'):
                self.invoke(directory, self.response(), options=['--max-input-bytes', '10'], expected_requests=0)
            self.assertFalse((directory / 'submission.json').exists())
            self.assertFalse(json.loads((directory / 'input_preflight.json').read_text())['within_budget'])

    def tool_response(self, name='get_declaration', arguments=None):
        return {'id': 'resp_tools', 'status': 'completed', 'output': [
            {'type': 'function_call', 'name': name, 'call_id': 'call_1',
             'arguments': json.dumps(arguments if arguments is not None else {'id': 'Alias'})}]}

    def test_unexpected_tool_call_is_not_executed(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            with self.assertRaisesRegex(RuntimeError, 'Unexpected tool call'):
                self.invoke(directory, self.tool_response())
            self.assertFalse((directory / 'submission.json').exists())

    def test_provider_timeout_retains_failure_metadata(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            with self.assertRaisesRegex(RuntimeError, 'timed out'):
                self.invoke(directory, error=TimeoutError('private transport details'))
            metadata = json.loads((directory / 'llm_metadata.json').read_text())
            self.assertEqual(metadata['termination_reason'], 'Provider request timed out')
            self.assertEqual(metadata['requests'], [])

    def test_wall_clock_budget_prevents_transport(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            with patch.object(A.time, 'monotonic', side_effect=[0] + [100] * 30):
                with self.assertRaisesRegex(RuntimeError, 'wall-clock'):
                    self.invoke(directory, self.response(), expected_requests=0)
            self.assertEqual(json.loads((directory / 'llm_metadata.json').read_text())['outcome'], 'failed')

if __name__ == '__main__':
    unittest.main()
