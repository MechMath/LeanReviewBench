import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

BASE = Path(__file__).resolve().parents[1]


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, BASE / 'scripts/evaluation' / filename)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


P = module('protocol', 'benchmark_protocol.py')


class FormalContextTests(unittest.TestCase):
    def test_context_integrity_and_assessment_boundary(self):
        pairs = [{'id': 'Root', 'kind': 'theorem', 'formal': {}}]
        context = {'declarations': [{'id': 'Alias', 'kind': 'abbrev', 'module': 'Test',
                                    'formal': {'type': 'Type', 'value': 'Nat'}}],
                   'external_nodes': [],
                   'edges': [{'source': 'Root', 'target': 'Alias', 'site': 'type'}]}
        P.validate_context(context, pairs)
        mutations = [
            lambda c: c['edges'].clear(),
            lambda c: c['edges'][0].update(target='Unknown'),
            lambda c: c['declarations'][0].update(id='Root'),
            lambda c: c['declarations'][0].update(informal='hidden'),
            lambda c: c['declarations'][0].update(kind='theorem'),
            lambda c: c['edges'][0].update(site='definition_value')]
        for mutate in mutations:
            invalid = copy.deepcopy(context)
            mutate(invalid)
            with self.subTest(context=invalid), self.assertRaises(ValueError):
                P.validate_context(invalid, pairs)
        prediction = {'task_id': 'Root', 'verdict': 'misaligned', 'summary': 'Mismatch',
                      'issues': [{'declaration_id': 'Alias', 'category': 'definition',
                                  'explanation': 'Context is not an assessment target'}]}
        with self.assertRaisesRegex(ValueError, 'Unknown declaration ID'):
            P.validate_prediction(prediction, {'task_id': 'Root'},
                                  {'main_theorem': pairs[0], 'definitions': [], 'formal_context': context})



if __name__ == '__main__':
    unittest.main()
