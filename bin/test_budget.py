"""The budget check's exit code (`python3 bin/test_budget.py`): zero on a tree within its budgets or with only the
violations its baseline records; non-zero on one more, a second of a kind in one file included; and the skill's three
exceptions, each read off the code.
"""
import os, subprocess, sys, tempfile, unittest

BUDGET = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'budget.py')


class BudgetTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.root = os.path.join(self.dir.name, 'modules')
        self.pkg = os.path.join(self.root, 'm', 'src', 'main', 'scala', 'p')
        os.makedirs(self.pkg)
        self.baseline = os.path.join(self.dir.name, 'baseline.txt')
        for f in ['A', 'B', 'C']: self.write(f, f"object {f}:\n  def f(a: Int): Int = a\n")

    def tearDown(self): self.dir.cleanup()

    def write(self, name, text):
        with open(os.path.join(self.pkg, name + '.scala'), 'w') as f: f.write(text)

    def run_budget(self, *more):
        return subprocess.run([sys.executable, BUDGET, self.root, '--baseline', self.baseline, *more],
                              capture_output=True, text=True).returncode

    def test_within_the_budgets_it_passes(self):
        self.assertEqual(self.run_budget(), 0)

    def test_a_new_violation_fails_and_the_baseline_admits_it(self):
        self.write('A', "object A:\n  def f(a: Int, b: Int, c: Int, d: Int, e: Int): Int = a\n")
        self.assertEqual(self.run_budget(), 1)
        self.assertEqual(self.run_budget('--write-baseline'), 0)
        self.assertEqual(self.run_budget(), 0)
        self.write('A', "object A:\n  def f(a: Int, b: Int, c: Int, d: Int, e: Int): Int = a\n"
                        "  def f(a: Int, b: Int, c: Int, d: Int, e: Int, g: Int): Int = a\n")
        self.assertEqual(self.run_budget(), 1)

    def test_a_long_line_and_a_small_package_fail(self):
        self.write('B', "object B:\n  val x = \"" + "y" * 130 + "\"\n")
        self.assertEqual(self.run_budget(), 1)
        self.write('B', "object B\n")
        os.remove(os.path.join(self.pkg, 'C.scala'))
        self.assertEqual(self.run_budget(), 1)

    def test_a_def_that_is_one_match_of_short_cases_may_be_long(self):
        cases = "".join(f"    case {i} =>\n      {i}\n" for i in range(12))
        self.write('A', "object A:\n  def f(a: Int): Int = a match\n" + cases)
        self.assertEqual(self.run_budget(), 0)
        self.write('A', "object A:\n  def f(a: Int): Int = a match\n" + cases.replace("      0\n", "      0\n      0\n"))
        self.assertEqual(self.run_budget(), 1)
        self.write('A', "object A:\n  def f(a: Int): Int =\n" + "    a\n" * 22)
        self.assertEqual(self.run_budget(), 1)

    def test_an_apply_mirroring_a_definitions_arity_may_take_more_than_four(self):
        apply = "  def apply(a: Int, b: Int, c: Int, d: Int, e: Int): Int = a\n"
        self.write('A', "object A:\n  extension [A, B, C, D, E, R](f: Definition[(A, B, C, D, E) => R])\n  " + apply)
        self.assertEqual(self.run_budget(), 0)
        self.write('A', "object A:\n  extension [A, B, C, D, R](f: Definition[(A, B, C, D) => R])\n  " + apply)
        self.assertEqual(self.run_budget(), 1)
        self.write('A', "object A:\n  extension [A, B, C, D, E, R](f: Fn[(A, B, C, D, E) => R])\n  " + apply)
        self.assertEqual(self.run_budget(), 1)

    def test_every_parameter_list_counts_but_using(self):
        self.write('A', "object A:\n  def f(a: Int, b: Int)(c: Int)(using x: Int, y: Int): Int = a\n")
        self.assertEqual(self.run_budget(), 0)
        self.write('A', "object A:\n  def f(a: Int, b: Int, c: Int)(d: Int,\n      e: Int): Int = a\n")
        self.assertEqual(self.run_budget(), 1)

    def test_the_facade_package_may_hold_one_file_in_eval_only(self):
        for module, code in [('eval', 0), ('dsl', 1)]:
            facade = os.path.join(self.root, module, 'src', 'main', 'scala', 'frflow')
            os.makedirs(facade)
            with open(os.path.join(facade, 'package.scala'), 'w') as f: f.write("package frflow\n")
            self.assertEqual(self.run_budget(), code)

    def test_an_examples_app_and_tests_may_hold_one_file_a_package_and_its_model_not(self):
        examples = os.path.join(self.dir.name, 'examples')
        def one(*at):
            d = os.path.join(examples, 'x', *at, 'scala', 'x')
            os.makedirs(d)
            with open(os.path.join(d, 'X.scala'), 'w') as f: f.write("package x\n")
        run = lambda: subprocess.run([sys.executable, BUDGET, self.root, examples, '--baseline', self.baseline],
                                     capture_output=True, text=True).returncode
        one('app', 'src', 'main'); one('src', 'test')
        self.assertEqual(run(), 0)
        one('src', 'main')
        self.assertEqual(run(), 1)

    def test_a_baseline_comment_is_no_violation(self):
        with open(self.baseline, 'w') as f: f.write("# why\n")
        self.assertEqual(self.run_budget(), 0)


if __name__ == '__main__':
    unittest.main()
