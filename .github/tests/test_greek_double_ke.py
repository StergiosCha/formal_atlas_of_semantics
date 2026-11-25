"""Compile the published Greek double-ke fragment and check its assumptions."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class GreekDoubleKeTests(unittest.TestCase):
    def test_five_results_and_counterexamples(self):
        source = Path(__file__).resolve().parents[2] / "research/greek-double-ke/DoubleAdditive.v"
        with tempfile.TemporaryDirectory() as work:
            shutil.copyfile(source, Path(work) / source.name)
            compile_result = subprocess.run(
                ["coqc", source.name], cwd=work, check=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            self.assertEqual(compile_result.stdout.splitlines().count("Closed under the global context"), 5)
            recheck = subprocess.run(
                ["coqchk", "-silent", "-o", source.stem], cwd=work, check=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            self.assertIn("* Axioms: <none>", recheck.stdout)
