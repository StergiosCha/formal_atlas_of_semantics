"""Heim traceability and reporting checks, not independent source-fidelity review."""
import hashlib
import json
from pathlib import Path
import unittest

import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
COUNTS = {"atlas__heim1982": 34, "atlas__heim1982_examples": 17,
          "atlas__heim1982_extensions": 22, "atlas__heim1982_indexed": 19}


def record(key, suffix=""):
    return json.loads((HERE / "records" / f"{key}{suffix}.json").read_text())


def results():
    return json.loads((HERE / "campaigns/heim_1982_results.json").read_text())


class HeimCampaignTests(unittest.TestCase):
    def test_all_modules_registered_and_linked_additively(self):
        files = [record(key)["file"] for key in COUNTS]
        self.assertEqual(results()["files"], files)
        project = (ROOT / "_CoqProject").read_text().splitlines()
        links = json.loads((HERE / "paper_evidence.json").read_text())["7"]
        paper = next(p for p in json.loads((HERE / "atlas.json").read_text())["papers"]
                     if str(p["id"]) == "7")
        for path in files:
            self.assertEqual(project.count(path), 1)
            self.assertIn(path, links)
            self.assertIn(path, paper["coq_files"])
        for path in ("extras/FCS.v", "extras/FCS2.v", "extras/DonkeyScope.v"):
            self.assertIn(path, paper["coq_files"])

    def test_all_declarations_have_scoped_ledger_entries(self):
        ids = {t["id"] for t in results()["targets"]}
        for key, count in COUNTS.items():
            with self.subTest(key=key):
                rec = record(key)
                decls, warnings = verify.parse(ROOT / rec["file"])
                self.assertFalse(warnings)
                parsed = {".".join(d["modpath"] + [d["name"]])
                          for d in decls if d["kind"] == "theorem"}
                listed = [t["name"] for t in rec["theorems"]]
                self.assertEqual(len(listed), count)
                self.assertEqual(len(set(listed)), count)
                self.assertEqual(set(listed), parsed)
                for theorem in rec["theorems"]:
                    self.assertEqual(theorem["status"], "proved")
                    self.assertIn(theorem["inventory_id"], ids)
                    self.assertTrue(theorem["source_claim"])
                    self.assertTrue(theorem["claim_kind"])

    def test_all_coverage_targets_have_existing_support(self):
        ledger = results()
        self.assertEqual([t["id"] for t in ledger["targets"]],
                         [f"H{n:02d}" for n in range(1, 20)])
        measured = {name for key in COUNTS for name in record(key, ".mech")["statements"]}
        for target in ledger["targets"]:
            self.assertTrue(target["scope"])
            self.assertTrue(target["status"])
            self.assertTrue(target["support"])
            self.assertLessEqual(set(target["support"]), measured)
        self.assertEqual([r["id"] for r in ledger["requirements"]],
                         [f"R{n}" for n in range(1, 8)])
        for requirement in ledger["requirements"]:
            self.assertLessEqual(set(requirement["evidence"]),
                                 {t["id"] for t in ledger["targets"]})

    def test_complete_mechanical_audit_and_exact_classical_dependencies(self):
        classical = set()
        closed = 0
        for key, count in COUNTS.items():
            mech = record(key, ".mech")
            self.assertTrue(mech["compile"]["ok"])
            self.assertFalse(mech["compile"]["unsafe_flags"])
            self.assertEqual(mech["counts"]["proved"], count)
            self.assertEqual(mech["counts"]["theorems"], count)
            for field in ("admitted", "admitted_definitions", "aborted",
                          "unparsed_status", "toplevel_axioms"):
                self.assertEqual(mech["counts"][field], 0)
            self.assertEqual(mech["assumptions"]["queried"], count)
            self.assertFalse(mech["assumptions"]["unresolved"])
            self.assertFalse(mech["assumptions"]["undocumented_axioms"])
            self.assertFalse(mech["disputes_vs_record"])
            closed += mech["assumptions"]["closed"]
            for name, dep in mech["assumptions"]["detail"].items():
                if not dep["closed"]:
                    self.assertEqual(dep["axioms"], ["Classical_Prop.classic"])
                    classical.add(name)
        self.assertEqual(closed, 89)
        self.assertEqual(classical, {
            "dynamic.Heim1982_Extensions.nontrivial_entailment_forces_familiarity",
            "dynamic.Heim1982_Extensions.criterion_C_exhaustive_on_felicitous_true_inputs",
            "dynamic.Heim1982_Indexed.modal_duality_classical",
        })

    def test_probe_flags_preserved_without_vacuity_or_bailouts(self):
        trivial_counts = [12, 4, 4, 2]
        for (key, count), trivial in zip(COUNTS.items(), trivial_counts):
            probe = record(key, ".probe")
            self.assertEqual(probe["summary"],
                             {"probed": count, "vacuous": 0, "trivial": trivial, "bailout": 0})
            self.assertEqual(set(probe["probes"]), set(record(key, ".mech")["statements"]))
            for result in probe["probes"].values():
                self.assertFalse(any(v.startswith("BAILOUT") for v in result.values()))

    def test_claim_fingerprints_are_registered(self):
        claims = json.loads((HERE / "claims.lock").read_text())["claims"]
        for key in COUNTS:
            mech = record(key, ".mech")
            for name, fingerprint in mech["statements"].items():
                self.assertEqual(claims[name]["file"], mech["file"])
                self.assertEqual(claims[name]["statement_sha"], fingerprint)
                self.assertEqual(claims[name]["status"], "active")

    def test_conditional_interfaces_cannot_be_reported_as_whole_source_completion(self):
        ledger = results()
        self.assertFalse(ledger["whole_source_complete"])
        self.assertFalse(ledger["independent_review"])
        self.assertIsNone(ledger["accepted_outcome"])
        by_id = {t["id"]: t["status"] for t in ledger["targets"]}
        for target in ("H09", "H12"):
            self.assertEqual(by_id[target], "conditional_policy_interface")
        self.assertEqual(by_id["H13"], "partial_open_policy")
        self.assertEqual(by_id["H19"], "partial_grammar_interface")
        for key in COUNTS:
            rec = record(key)
            self.assertEqual(rec["assessment_status"], "incomplete")
            self.assertEqual(rec["determination"], "unassessed")
            self.assertEqual(rec["faithfulness"]["verdict"], "partial")
        paper = next(p for p in json.loads((HERE / "atlas.json").read_text())["papers"]
                     if str(p["id"]) == "7")
        self.assertEqual(paper["level"], "F3")
        self.assertEqual(paper["formality"], 4)
        self.assertEqual(paper["determination_status"], "review_required")
        self.assertIsNone(paper["determination_actual"])

    def test_historical_research_and_grades_preserved(self):
        previous = json.loads((HERE / "audits/source_reviews_2026_09_15/manifest.json").read_text())
        # Shared build inventory/generated atlas intentionally changed; research did not.
        changed = {"_CoqProject", "atlas_data/atlas.json"}
        for name, expected in previous["files"].items():
            if name in changed:
                continue
            with self.subTest(file=name):
                self.assertEqual(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(), expected)


if __name__ == "__main__":
    unittest.main()
