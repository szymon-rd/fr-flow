"""The budget check's exit code (`python3 docs/redesign/tools/test_budget.py`): zero on a tree within its budgets or
with only the violations its baseline records; non-zero on one more, a second of a kind in one file included.
"""
import os, subprocess, sys, tempfile, unittest

BUDGET = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'budget.py')


class BudgetTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.root = os.path.join(self.dir.name, 'next')
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


if __name__ == '__main__':
    unittest.main()
