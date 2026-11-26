import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

BASE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('construction_environment', BASE / 'scripts/construction/environment.py')
E = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(E)


class ConstructionEnvironmentTests(unittest.TestCase):
    def setUp(self):
        self.config = json.loads((BASE / 'datasets/project-cases.json').read_text())

    def test_explicit_lean_does_not_use_elan(self):
        with tempfile.TemporaryDirectory() as temp:
            executable = Path(temp) / 'lean'
            executable.touch()
            with patch.dict(os.environ, {'PAPERLEAN_LEAN': str(executable)}, clear=True), \
                    patch.object(E.subprocess, 'check_output', return_value='Lean (version 4.34.1, test)') as invoke:
                self.assertEqual(E.resolve_lean(self.config), executable)
                self.assertEqual(invoke.call_count, 1)
                self.assertEqual(invoke.call_args.args[0], [str(executable), '--version'])

    def test_configured_elan_receives_pinned_toolchain(self):
        with patch.dict(os.environ, {'PAPERLEAN_ELAN': '/external/elan'}, clear=True), \
                patch.object(E.subprocess, 'check_output', side_effect=['/external/lean\n', 'Lean (version 4.34.1, test)']) as invoke:
            self.assertEqual(E.resolve_lean(self.config), Path('/external/lean'))
            args, kwargs = invoke.call_args_list[0]
            self.assertEqual(args[0], ['/external/elan', 'which', 'lean'])
            self.assertEqual(kwargs['env']['ELAN_TOOLCHAIN'], self.config['lean_toolchain'])

    def test_wrong_toolchain_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            executable = Path(temp) / 'lean'
            executable.touch()
            with patch.dict(os.environ, {'PAPERLEAN_LEAN': str(executable)}, clear=True), \
                    patch.object(E.subprocess, 'check_output', return_value='Lean (version 4.33.0, test)'), \
                    self.assertRaisesRegex(ValueError, 'version differs'):
                E.resolve_lean(self.config)

    def test_exporter_bundle_is_explicit_and_complete(self):
        with patch.dict(os.environ, {}, clear=True), self.assertRaisesRegex(ValueError, 'PAPERLEAN_LEANTRACE'):
            E.resolve_leantrace(self.config)
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            with patch.dict(os.environ, {'PAPERLEAN_LEANTRACE': temp}, clear=True):
                with self.assertRaisesRegex(ValueError, 'Export.lean'):
                    E.resolve_leantrace(self.config)
                (directory / 'Export.lean').touch()
                with self.assertRaisesRegex(ValueError, 'graph.py'):
                    E.resolve_leantrace(self.config)
                (directory / 'graph.py').touch()
                self.assertEqual(E.resolve_leantrace(self.config), directory)
