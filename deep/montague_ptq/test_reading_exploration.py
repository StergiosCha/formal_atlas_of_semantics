"""Discovery-tool regressions. Semantic correctness is checked by Coq separately."""
import json
from pathlib import Path
import unittest

from explore_readings import Explorer, emit, rank, sentences, tokenize
from check_reading_exploration import CANONICAL, alpha_normalize, signature


class ReadingExplorationTests(unittest.TestCase):
    def test_twenty_registered_strings(self):
        self.assertEqual(len(sentences()), 20)
        self.assertEqual(sentences()[0], ('Bill', 'walks'))

    def test_unknown_words_are_not_silently_accepted(self):
        self.assertEqual(tokenize(('Bill', 'teleports')), ())

    def test_two_derivations_can_be_one_reading(self):
        search = Explorer('amended', 100)
        trees = {t for ts in tokenize(sentences()[0]) for t in search.parse('CT', 'infinitive', ts)}
        self.assertEqual(len(trees), 2)
        self.assertEqual(len({signature(t) for t in trees}), 1)

    def test_cap_raises_instead_of_truncating(self):
        search = Explorer('amended', 1)
        with self.assertRaisesRegex(RuntimeError, 'no completeness claim'):
            for ts in tokenize(sentences()[0]):
                search.parse('CT', 'infinitive', ts)

    def test_literal_and_amended_coordination_are_separate(self):
        for policy, expected in [('literal', 0), ('amended', 23)]:
            search = Explorer(policy, 10000)
            trees = {t for ts in tokenize(sentences()[18]) for t in search.parse('CT', 'infinitive', ts)}
            self.assertEqual(len(trees), expected)

    def test_splitting_an_index_class_decreases_rank(self):
        self.assertLess(rank((('index', 0, 0), ('index', 1, 1))),
                        rank((('index', 0, 0), ('index', 0, 1))))

    def test_alpha_normalization_ignores_unused_levels(self):
        self.assertEqual(alpha_normalize(('lambda', 3, ('bound', 3))),
                         alpha_normalize(('lambda', 0, ('bound', 0))))

    def test_belief_boundary_is_not_erased_by_grouping(self):
        search = Explorer('amended', 10000)
        trees = {t for ts in tokenize(sentences()[16]) for t in search.parse('CT', 'infinitive', ts)}
        self.assertEqual(len(trees), 1842)
        self.assertEqual(len({signature(t) for t in trees}), 3)

    def test_emission_is_actual_grammar_not_invented_formulas(self):
        self.assertEqual(emit(('s4', ('name', 'bill'), ('word', 'liv', 'walk'))),
                         '(s4 (s1_name bill) (s1_word (liv walk)))')

    def test_registry_proposals_have_twenty_separate_scopes(self):
        self.assertEqual(len(CANONICAL), 20)
        self.assertEqual(sum(len(set(row)) for row in CANONICAL), 27)

    def test_report_does_not_claim_search_completeness(self):
        report = json.loads((Path(__file__).parent / 'reading_exploration.json').read_text())
        self.assertFalse(report['search_completeness_proved'])
        self.assertEqual(report['build_mode'], 'isolated')
        self.assertEqual(report['model'], 'none')
        self.assertEqual(report['witnesses'], 2073)
        self.assertEqual(report['registered_classes_reached'], 27)


if __name__ == '__main__':
    unittest.main()
