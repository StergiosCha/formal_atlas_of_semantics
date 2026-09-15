"""CI setup regression tests. Requires PyYAML (python3-yaml in the job).

The build-step checks use fake compiler/make executables to verify command
ordering and failure propagation; they are not a Docker or Coq integration run.
"""
from pathlib import Path
import os
import shlex
import subprocess
import tempfile
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = yaml.safe_load((ROOT / ".github/workflows/verify.yml").read_text())
JOB = WORKFLOW["jobs"]["verify"]
STEPS = {step["name"]: step for step in JOB["steps"] if "name" in step}


class VerificationSetupTests(unittest.TestCase):
    def test_checkout_can_write_runner_state_before_any_run_step(self):
        self.assertEqual(JOB["container"]["image"], "coqorg/coq:8.20.1")
        self.assertEqual(shlex.split(JOB["container"]["options"]), ["--user", "root"])
        self.assertEqual(JOB["steps"][0]["uses"], "actions/checkout@v4")
        self.assertEqual(WORKFLOW["permissions"], {"contents": "read"})

    def test_root_uses_existing_coq_switch_and_failure_propagating_shell(self):
        self.assertEqual(shlex.split(JOB["defaults"]["run"]["shell"]),
                         ["opam", "exec", "--root=/home/coq/.opam", "--", "bash",
                          "--noprofile", "--norc", "-e", "-o", "pipefail", "{0}"])

    def test_fresh_build_configuration_does_not_overwrite_committed_makefile(self):
        command = STEPS["Compile the corpus"]["run"]
        self.assertIn("coq_makefile -f _CoqProject -o Makefile.coq\n", command)
        self.assertIn('make -f Makefile.coq -k -j"$(nproc)"', command)
        self.assertNotIn("| tail", command)
        self.assertNotIn("chown", command)

    def build_fixture(self, generator_status=0, make_status=0):
        with tempfile.TemporaryDirectory(prefix="atlas-ci-test-") as directory:
            root = Path(directory)
            stubs = {
                "coq_makefile": f"echo GENERATE\nexit {generator_status}\n",
                "make": f"echo BUILD\nexit {make_status}\n",
                "nproc": "echo 2\n",
            }
            for name, body in stubs.items():
                path = root / name
                path.write_text("#!/bin/sh\n" + body)
                path.chmod(0o755)
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ["PATH"])
            return subprocess.run(
                ["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", "-c",
                 STEPS["Compile the corpus"]["run"]],
                cwd=root, env=env, capture_output=True, text=True)

    def test_compiler_setup_failure_stops_before_make(self):
        result = self.build_fixture(generator_status=43)
        self.assertEqual(result.returncode, 43)
        self.assertEqual(result.stdout.splitlines(), ["GENERATE"])

    def test_make_failure_is_not_hidden_by_logging(self):
        result = self.build_fixture(make_status=42)
        self.assertEqual(result.returncode, 42)
        self.assertEqual(result.stdout.splitlines(), ["GENERATE", "BUILD"])

    def test_successful_build_runs_both_commands_in_order(self):
        result = self.build_fixture()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ["GENERATE", "BUILD"])

    def test_mechanical_and_integrity_gates_remain_mandatory(self):
        for name in ("coqchk — independent kernel recheck (atlas layer)",
                     "Mechanical verification (counts, assumptions, fingerprints)",
                     "Gate — measured state must match the committed records",
                     "Gate — atlas layer invariants"):
            self.assertIn(name, STEPS)
            self.assertFalse(STEPS[name].get("continue-on-error", False))
            self.assertNotIn("if", STEPS[name])
        self.assertIn("git diff --exit-code -- atlas_data/records atlas_data/claims.lock",
                      STEPS["Gate — measured state must match the committed records"]["run"])

    def test_untracked_sidecars_cannot_escape_the_record_gate(self):
        with tempfile.TemporaryDirectory(prefix="atlas-ci-gate-") as directory:
            git = Path(directory) / "git"
            git.write_text('#!/bin/sh\nif [ "$1" = "ls-files" ]; then\n'
                           '  echo atlas_data/records/wrong_key.mech.json\nfi\nexit 0\n')
            git.chmod(0o755)
            env = dict(os.environ, PATH=directory + os.pathsep + os.environ["PATH"])
            result = subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c",
                 STEPS["Gate — measured state must match the committed records"]["run"]],
                cwd=directory, env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("untracked records", result.stdout)


if __name__ == "__main__":
    unittest.main()
