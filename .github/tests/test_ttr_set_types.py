import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class CooperSetTypes(unittest.TestCase):
    def test_membership_against_the_canonical_module(self):
        sources = [
            ROOT / "ttr_mtt/TTR_base.v",
            ROOT / "ttr_mtt/TTR_types.v",
            ROOT / "research/ttr-set-types/SetTypeChecks.v",
        ]
        with tempfile.TemporaryDirectory() as directory:
            for source in sources:
                shutil.copyfile(source, Path(directory) / source.name)
                subprocess.run(["coqc", source.name], cwd=directory, check=True)
            subprocess.run(["coqchk", "-silent", "SetTypeChecks"], cwd=directory, check=True)
