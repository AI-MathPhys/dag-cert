"""Protect archived results from the reproduction command's output routing."""
import tempfile
import unittest
import importlib
import sys
from pathlib import Path
import reproduce


class ReproductionTests(unittest.TestCase):
    def test_statistical_roundoff_is_recorded(self):
        import math
        differences = reproduce.compare_summary({'count': 10, 'ratio': [math.nextafter(1., 2.)]},
                                                {'count': 10, 'ratio': [1.]})
        self.assertEqual(len(differences), 1)
        self.assertEqual(differences[0]['path'], 'summary.ratio[0]')

    def test_summary_validation_rejects_changed_results(self):
        for actual, expected in (({'count': 11}, {'count': 10}), (1., 1),
                                 ([1.], [1., 2.]), (1.001, 1.),
                                 ({'extra': 1}, {'count': 1}), (float('nan'), 1.)):
            with self.assertRaises(ValueError):
                reproduce.compare_summary(actual, expected)

    def test_imported_project_modules_are_local(self):
        for name in ('dag_mcts.compiled_retirement', 'paper.uct_frontier_study',
                     'paper.uct_backup_benchmark'):
            importlib.import_module(name)
        for name, module in tuple(sys.modules.items()):
            if name.split('.')[0] in ('dag_mcts', 'paper') and getattr(module, '__file__', None):
                self.assertTrue(Path(module.__file__).resolve().is_relative_to(reproduce.ROOT), name)

    def test_rejects_frozen_output(self):
        for path in (reproduce.ROOT, reproduce.FROZEN, reproduce.FROZEN / 'new',
                     reproduce.ROOT / 'paper', reproduce.ROOT / 'appendix/results'):
            with self.assertRaises(ValueError):
                reproduce.output_dir(path)

    def test_fresh_run_does_not_overwrite(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'trial'
            reproduce.output_dir(path, fresh=True)
            with self.assertRaises(FileExistsError):
                reproduce.output_dir(path, fresh=True)

    def test_patches_are_restored_on_error(self):
        class Settings:
            DEST = 'frozen'
        with self.assertRaises(RuntimeError):
            with reproduce.patch(Settings, DEST='new'):
                self.assertEqual(Settings.DEST, 'new')
                raise RuntimeError()
        self.assertEqual(Settings.DEST, 'frozen')
