import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

BASE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('protocol', BASE / 'scripts/evaluation/benchmark_protocol.py')
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


class ProtocolTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        source = 'def x := "-- keep /- text -/" /- hidden /- nested -/ still hidden -/\n-- hidden\ndef y := x'
        cleaned = P.strip_comments(source)
        self.assertIn('"-- keep /- text -/"', cleaned)
        self.assertNotIn('hidden', cleaned)
        self.assertIn('def y := x', cleaned)
        with self.assertRaises(ValueError):
            P.strip_comments('/- unterminated')

    def fixture(self, directory):
        pair = {'id': 'Root', 'kind': 'theorem',
                'formal': {'statement_source': 'theorem Root : True', 'value': None},
                'informal': {'text': 'True', 'origin': 'existing_lean_informal_comment'}, 'qualifiers': []}
        dep = {'id': 'Definition', 'kind': 'def',
               'formal': {'source_fragment': '/-- SECRET /- nested -/ -/\ndef Definition := True', 'value': 'True'},
               'informal': {'text': 'SECRET', 'origin': 'upstream_docstring'},
               'qualifiers': [{'text': 'SECRET'}]}
        package = {'schema_version': 'paperlean-full-draft-2', 'root_id': 'Root',
                   'formal_context': {'declarations': [], 'external_nodes': [],
                                      'edges': [{'source': 'Root', 'target': 'Definition', 'site': 'type'}]},
                   'main_theorem': pair, 'definitions': [dep], 'external_boundary': 'Pinned',
                   'status': {'reference_informal_complete': False, 'informal_review_complete': False}}
        path = directory / 'packages.jsonl'
        path.write_text(json.dumps(package) + '\n')
        return path

    def call(self, *args):
        return subprocess.run([sys.executable, str(BASE / 'scripts/evaluation/benchmark_protocol.py'), *map(str, args)],
                              capture_output=True, text=True)

    def test_export_run_and_failure_states(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            packages = self.fixture(temp)
            tasks = temp / 'tasks'
            args = ['export', '--packages', packages, '--output', tasks, '--mode', 'theorem_only']
            self.assertNotEqual(self.call(*args).returncode, 0)
            self.assertFalse(tasks.exists())
            result = self.call(*args, '--allow-draft')
            self.assertEqual(result.returncode, 0, result.stderr)
            task_dir = tasks / P.load(tasks / 'index.json')['tasks'][0]['directory']
            self.assertNotIn('SECRET', (task_dir / 'input.json').read_text())
            run = temp / 'run'
            result = self.call('run', '--task', task_dir, '--output', run, '--',
                               sys.executable, BASE / 'scripts/evaluation/mock_system.py')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(P.load(run / 'run.json')['status'], 'completed')
            self.assertEqual(P.load(run / 'prediction.json')['verdict'], 'insufficient_information')
            for name, command, expected in [
                ('invalid', [sys.executable, '-c', 'pass'], 'invalid_submission'),
                ('failed', [sys.executable, '-c', 'raise SystemExit(2)'], 'execution_failed'),
                ('timeout', [sys.executable, '-c', 'import time; time.sleep(10)'], 'timeout')]:
                result = self.call('run', '--task', task_dir, '--output', temp / name,
                                   '--timeout', '0.2', '--', *command)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(P.load(temp / name / 'run.json')['status'], expected)
            (task_dir / 'input.json').write_text('{}')
            self.assertNotEqual(self.call('validate', '--task', task_dir).returncode, 0)

    def test_batch_resume_and_index_integrity(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            packages = self.fixture(temp)
            tasks, batch = temp / 'tasks', temp / 'batch'
            self.assertEqual(self.call('export', '--packages', packages, '--output', tasks,
                                       '--allow-draft').returncode, 0)
            args = ['batch', '--tasks', tasks, '--output', batch]
            command = ['--', sys.executable, BASE / 'scripts/evaluation/mock_system.py']
            result = self.call(*args, *command)
            self.assertEqual(result.returncode, 0, result.stderr)
            index = P.load(tasks / 'index.json')
            receipt = batch / index['tasks'][0]['directory'] / 'run.json'
            original = receipt.read_bytes()
            result = self.call(*args, '--resume', *command)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(receipt.read_bytes(), original)
            self.assertEqual(P.load(batch / 'summary.json')['execution_statuses'], {'completed': 1})
            self.assertNotEqual(self.call(*args, '--resume', '--timeout', '1', *command).returncode, 0)
            index['tasks'][0]['task_sha256'] = 'invalid'
            P.write(tasks / 'index.json', index)
            self.assertNotEqual(self.call(*args, '--resume', *command).returncode, 0)

    def test_prediction_semantics(self):
        task = {'task_id': 'Root'}
        payload = {'main_theorem': {'id': 'Root'}, 'definitions': []}
        pred = {'task_id': 'Root', 'verdict': 'misaligned', 'issues': [], 'summary': 'Mismatch'}
        with self.assertRaises(ValueError):
            P.validate_prediction(pred, task, payload)
        pred['issues'] = [{'declaration_id': 'Unknown', 'category': 'definition', 'explanation': 'Mismatch'}]
        with self.assertRaises(ValueError):
            P.validate_prediction(pred, task, payload)
        pred['issues'][0]['declaration_id'] = 'Root'
        P.validate_prediction(pred, task, payload)
        pred['verdict'] = 'aligned'
        with self.assertRaises(ValueError):
            P.validate_prediction(pred, task, payload)

    def test_task_package_rejects_extra_files_and_symlinks(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            tasks = temp / 'tasks'
            self.assertEqual(self.call('export', '--packages', self.fixture(temp),
                                       '--output', tasks, '--allow-draft').returncode, 0)
            task = tasks / P.load(tasks / 'index.json')['tasks'][0]['directory']
            extra = task / 'reference.txt'
            extra.write_text('Private evaluation reference')
            result = self.call('run', '--task', task, '--output', temp / 'rejected',
                               '--', sys.executable, BASE / 'scripts/evaluation/mock_system.py')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Unexpected task package files', result.stderr)
            self.assertFalse((temp / 'rejected').exists())
            extra.unlink()
            original = (task / 'input.json').read_bytes()
            (task / 'input.json').unlink()
            outside = temp / 'input.json'
            outside.write_bytes(original)
            (task / 'input.json').symlink_to(outside)
            self.assertNotEqual(self.call('validate', '--task', task).returncode, 0)
            (task / 'input.json').unlink()
            (task / 'input.json').write_bytes(original)
            result = self.call('run', '--task', task, '--output', temp / 'accepted',
                               '--', sys.executable, BASE / 'scripts/evaluation/mock_system.py')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual({p.name for p in (temp / 'accepted/task').iterdir()}, P.TASK_FILES)

    def test_batch_resume_rejects_changed_adapter_and_dependencies(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            tasks, batch = temp / 'tasks', temp / 'batch'
            self.assertEqual(self.call('export', '--packages', self.fixture(temp),
                                       '--output', tasks, '--allow-draft').returncode, 0)
            adapter, dependency = temp / 'adapter.py', temp / 'dependency.txt'
            source = (BASE / 'scripts/evaluation/mock_system.py').read_text()
            adapter.write_text(source)
            dependency.write_text('v1')
            args = ['batch', '--tasks', tasks, '--output', batch,
                    '--fingerprint-file', dependency, '--adapter-version', 'v1']
            command = ['--', sys.executable, adapter]
            result = self.call(*args, *command)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = batch / P.load(tasks / 'index.json')['tasks'][0]['directory'] / 'run.json'
            original = receipt.read_bytes()
            adapter.write_text(source + '\n# updated adapter\n')
            result = self.call(*args, '--resume', *command)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Resume configuration differs', result.stderr)
            adapter.write_text(source)
            dependency.write_text('v2')
            self.assertNotEqual(self.call(*args, '--resume', *command).returncode, 0)
            dependency.write_text('v1')
            self.assertNotEqual(self.call(*args, '--adapter-version', 'v2', '--resume', *command).returncode, 0)
            result = self.call(*args, '--resume', *command)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(receipt.read_bytes(), original)

    def test_responses_identity_uses_effective_settings_without_credentials(self):
        with tempfile.TemporaryDirectory() as temp, patch.dict(os.environ, {}, clear=True):
            config = Path(temp) / '.env'
            original = ('OPENAI_API_KEY=private-secret\nOPENAI_MODEL=model-a\n'
                        'OPENAI_BASE_URL=https://example.test/v1\nOPENAI_REASONING_EFFORT=medium\n')
            config.write_text(original)
            command = [sys.executable, str(BASE / 'scripts/evaluation/responses_llm.py'),
                       '--env-file', str(config)]
            identity = P.adapter_identity(command)
            self.assertEqual(identity['settings']['model'], 'model-a')
            self.assertNotIn('private-secret', json.dumps(identity))
            self.assertNotIn(str(config), json.dumps(identity))
            config.write_text(original.replace('private-secret', 'rotated-secret'))
            self.assertEqual(P.adapter_identity(command), identity)
            for old, new in [('model-a', 'model-b'), ('medium', 'high'),
                             ('https://example.test/v1', 'https://other.test/v1')]:
                config.write_text(original.replace(old, new))
                self.assertNotEqual(P.adapter_identity(command), identity)
            config.write_text(original)
            self.assertNotEqual(P.adapter_identity(command + ['--max-output-tokens', '100']), identity)
            self.assertNotEqual(P.adapter_identity(command + ['--max-input-bytes', '100']), identity)
            with patch.dict(os.environ, {'OPENAI_MODEL': 'override'}):
                self.assertEqual(P.adapter_identity(command)['settings']['model'], 'override')
            toml = Path(temp) / 'config.toml'
            toml.write_text('model="model-a"\nmodel_provider="test"\n'
                            '[model_providers.test]\nwire_api="responses"\n'
                            'base_url="https://example.test/v1"\n'
                            'experimental_bearer_token="private-secret"\n')
            command = command[:2] + ['--config', str(toml)]
            identity = P.adapter_identity(command)
            toml.write_text(toml.read_text().replace('model-a', 'model-b'))
            self.assertNotEqual(P.adapter_identity(command), identity)
            self.assertNotIn('private-secret', json.dumps(identity))

    def test_batch_resume_rejects_effective_model_change(self):
        with tempfile.TemporaryDirectory() as temp, patch.dict(os.environ, {}, clear=True):
            temp = Path(temp)
            tasks, batch = temp / 'tasks', temp / 'batch'
            self.assertEqual(self.call('export', '--packages', self.fixture(temp),
                                       '--output', tasks, '--allow-draft').returncode, 0)
            config = temp / '.env'
            config.write_text('OPENAI_API_KEY=private-secret\nOPENAI_MODEL=model-a\n')
            # Mock submission avoids network calls while the runner fingerprints
            # the Responses configuration supplied in the command arguments.
            command = ['--', sys.executable, BASE / 'scripts/evaluation/mock_system.py',
                       BASE / 'scripts/evaluation/responses_llm.py', '--env-file', config]
            args = ['batch', '--tasks', tasks, '--output', batch]
            result = self.call(*args, *command)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertNotIn('private-secret', (batch / 'batch.json').read_text())
            config.write_text('OPENAI_API_KEY=rotated-secret\nOPENAI_MODEL=model-a\n')
            self.assertEqual(self.call(*args, '--resume', *command).returncode, 0)
            config.write_text('OPENAI_API_KEY=rotated-secret\nOPENAI_MODEL=model-b\n')
            result = self.call(*args, '--resume', *command)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Resume configuration differs', result.stderr)

    def test_responses_adapter_through_runner(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            tasks = temp / 'tasks'
            exported = self.call('export', '--packages', self.fixture(temp),
                                 '--output', tasks, '--allow-draft')
            self.assertEqual(exported.returncode, 0, exported.stderr)
            task = tasks / P.load(tasks / 'index.json')['tasks'][0]['directory']
            for task_id, status in [('Root', 'completed'), ('Wrong', 'invalid_submission')]:
                with self.subTest(task_id=task_id):
                    prediction = {'task_id': task_id, 'verdict': 'aligned',
                                  'issues': [], 'summary': 'Matches.'}
                    response = {'status': 'completed', 'output': [{'type': 'message',
                                'content': [{'type': 'output_text', 'text': json.dumps(prediction)}]}]}
                    # Replace only the HTTP boundary in a real adapter subprocess.
                    wrapper = temp / 'fake_provider.py'
                    wrapper.write_text(
                        'import io, os, runpy, sys, urllib.request\n'
                        'os.environ.update(OPENAI_API_KEY="test", OPENAI_MODEL="test", '
                        'OPENAI_BASE_URL="https://example.test/v1")\n'
                        f'payload = {json.dumps(response).encode()!r}\n'
                        'urllib.request.urlopen = lambda *a, **k: io.BytesIO(payload)\n'
                        'sys.argv = ["adapter"]\n'
                        f'runpy.run_path({str(BASE / "scripts/evaluation/responses_llm.py")!r}, '
                        'run_name="__main__")\n')
                    output = temp / status
                    result = self.call('run', '--task', task, '--output', output,
                                       '--', sys.executable, wrapper)
                    self.assertEqual(result.returncode, 0 if status == 'completed' else 1, result.stderr)
                    self.assertEqual(P.load(output / 'run.json')['status'], status)
                    self.assertTrue((output / 'llm_metadata.json').is_file())
                    self.assertEqual((output / 'prediction.json').exists(), status == 'completed')


if __name__ == '__main__':
    unittest.main()
