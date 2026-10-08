"""Offline checks for the pre-registered queue-screen gate; never call a model."""
import importlib.util
from pathlib import Path
import unittest
import tempfile
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / 'experiments/idea-engine-2026-10-02/step3/settle_nomap.py'
spec = importlib.util.spec_from_file_location('settle_nomap', SCRIPT)
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)


class Analysis(unittest.TestCase):
    def setUp(self):
        self.jobs = [
            {'problem': '1', 'set': 'dev', 'solved': True, 'k': 2},
            {'problem': '2', 'set': 'dev', 'solved': False, 'k': 2},
            {'problem': '3', 'set': 'open', 'map_mean': .01, 'k': 1},
            {'problem': '4', 'set': 'open', 'map_mean': .02, 'k': 1},
        ]
        self.rows = [{'problem': str(i), 'draws': ds, 'cost': .2}
                     for i, ds in enumerate(([.4, .6], [.02, .04], [.01], [.02]), 1)]

    def test_ties_and_constant_values(self):
        self.assertAlmostEqual(M.rank_correlation([1, 1, 3], [1, 2, 3]), 3 ** .5 / 2)
        self.assertEqual(M.rank_correlation([1, 2, 3], [3, 2, 1]), -1)
        self.assertIsNone(M.rank_correlation([0, 0], [1, 2]))

    def test_complete_pass_uses_draws_not_saved_mean(self):
        self.rows[0]['mean'] = 0
        result = M.analyze(self.rows, self.jobs)
        self.assertEqual(result['decision'], 'sweep')
        self.assertAlmostEqual(result['dev_gap'], .47)

    def test_partial_cannot_trigger_sweep(self):
        result = M.analyze(self.rows[:-1], self.jobs)
        self.assertEqual(result['decision'], 'pending')
        self.assertEqual(result['missing'], ['4'])

    def test_missing_or_invalid_draw_is_not_a_completed_problem(self):
        for draws in ([.4], [.4, None], [.4, float('nan')], [.4, 1.1]):
            with self.subTest(draws=draws):
                self.rows[0]['draws'] = draws
                result = M.analyze(self.rows, self.jobs)
                self.assertEqual(result['decision'], 'pending')
                self.assertEqual(result['invalid'], ['1'])

    def test_duplicate_is_not_an_independent_problem(self):
        result = M.analyze(self.rows + [self.rows[0]], self.jobs)
        self.assertEqual(result['decision'], 'pending')

    def test_negative_correlation_keeps_forum_order(self):
        self.rows[-1]['draws'] = [0]
        self.assertEqual(M.analyze(self.rows, self.jobs)['decision'], 'keep_forum_order')

    def test_unknown_cost_is_not_zero(self):
        self.rows[0]['cost'] = None
        result = M.analyze(self.rows, self.jobs)
        self.assertEqual(result['unknown_cost_rows'], 1)
        self.assertIsNone(result['mean_cost_per_recorded_draw_usd'])

    def test_sweep_stops_before_fetching_or_model_calls(self):
        with patch.object(M.sys, 'argv', ['settle_nomap.py', '--sweep']), \
                patch.object(M, 'calibration_analysis', return_value={'decision': 'pending'}), \
                patch.object(M, 'jobs_sweep') as jobs, patch.object(M, 'draw') as draw:
            self.assertEqual(M.main(), 2)
            jobs.assert_not_called()
            draw.assert_not_called()

    def test_usage_limit_stops_without_drawing_later_problems(self):
        jobs = [{'problem': str(n), 'set': 'open', 'statement': 's', 'lean': 'l', 'masked': False, 'k': 1}
                for n in (1, 2)]
        with tempfile.TemporaryDirectory() as tmp, patch.object(M, 'HERE', Path(tmp)), \
                patch.object(M.sys, 'argv', ['settle_nomap.py', '--calib']), \
                patch.object(M, 'jobs_calib', return_value=jobs), \
                patch.object(M, 'draw', side_effect=RuntimeError('session limit')) as draw:
            with self.assertRaisesRegex(RuntimeError, 'session limit'):
                M.main()
            self.assertEqual(draw.call_count, 1)

    def test_sweep_honors_daily_and_invocation_cap_before_call(self):
        import resolution as R
        jobs = [{'problem': '1', 'k': 1}]
        for spent, cap in ((149, '150'), (0, '1')):
            with self.subTest(spent=spent), tempfile.TemporaryDirectory() as tmp, \
                    patch.object(M, 'ROOT', Path(tmp)), \
                    patch.object(M.sys, 'argv', ['settle_nomap.py', '--sweep', '--max-spend', cap]), \
                    patch.object(M, 'calibration_analysis', return_value={'decision': 'sweep'}), \
                    patch.object(M, 'jobs_sweep', return_value=jobs), \
                    patch.object(R, 'spent_since', return_value=spent), \
                    patch.object(R, 'load_cfg', return_value={'daily_cap_usd': 150}), \
                    patch.object(M, 'draw') as draw:
                self.assertEqual(M.main(), 3)
                draw.assert_not_called()


if __name__ == '__main__':
    unittest.main()
