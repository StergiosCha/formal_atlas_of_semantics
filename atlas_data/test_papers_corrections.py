"""Field corrections are applied after the frozen survey and addendum."""
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent


class PapersCorrectionsTests(unittest.TestCase):
    def test_every_correction_reaches_the_consolidated_survey(self):
        papers = {str(p["id"]): p for p in json.loads((HERE / "atlas.json").read_text())["papers"]}
        for c in json.loads((HERE / "papers_corrections.json").read_text()):
            for key, value in c.items():
                if key not in ("id", "note"):
                    with self.subTest(id=c["id"], field=key):
                        self.assertEqual(papers[str(c["id"])][key], value)

    def test_bekki_mineshima_title(self):
        paper = {str(p["id"]): p for p in json.loads((HERE / "atlas.json").read_text())["papers"]}["38"]
        self.assertEqual(paper["title"], "Context-Passing and Underspecification in Dependent Type Semantics")
        self.assertIn(paper["title"], paper["citation"])


if __name__ == "__main__":
    unittest.main()
