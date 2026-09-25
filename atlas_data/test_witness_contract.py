"""Bounded witness-contract evidence, not a whole-theory semantic review."""
import hashlib
import json
from pathlib import Path
import unittest

import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
KEY = "atlas__witness_contract"
PREFIX = "ttr.Witness_Contract."


def record(suffix=""):
    return json.loads((HERE / "records" / f"{KEY}{suffix}.json").read_text())


class WitnessContractTests(unittest.TestCase):
    def test_all_statements_registered_and_closed(self):
        rec, mech = record(), record(".mech")
        self.assertEqual((ROOT / "_CoqProject").read_text().splitlines().count(rec["file"]), 1)
        decls, warnings = verify.parse(ROOT / rec["file"])
        self.assertFalse(warnings)
        names = {".".join(d["modpath"] + [d["name"]]) for d in decls if d["kind"] == "theorem"}
        self.assertEqual(len(names), 30)
        self.assertEqual(names, {t["name"] for t in rec["theorems"]})
        self.assertEqual({PREFIX + n for n in names}, set(mech["statements"]))
        self.assertTrue(mech["compile"]["ok"])
        self.assertFalse(mech["compile"]["unsafe_flags"])
        self.assertEqual(mech["counts"]["proved"], 30)
        for field in ("admitted", "admitted_definitions", "aborted", "unparsed_status", "toplevel_axioms"):
            self.assertEqual(mech["counts"][field], 0)
        self.assertEqual(mech["assumptions"]["queried"], 30)
        self.assertEqual(mech["assumptions"]["closed"], 30)
        self.assertFalse(mech["assumptions"]["unresolved"])
        self.assertFalse(mech["assumptions"]["detail"])
        self.assertFalse(mech["disputes_vs_record"])
        claims = json.loads((HERE / "claims.lock").read_text())["claims"]
        for name, sha in mech["statements"].items():
            self.assertEqual(claims[name]["statement_sha"], sha)
            self.assertEqual(claims[name]["status"], "active")

    def test_preservation_separation_and_model_obligations_present(self):
        names = set(record(".mech")["statements"])
        for name in (
            "Packages.image_exactly_aligned", "Packages.join_split", "Packages.split_join",
            "Packages.Separation.no_total_recovery", "Fragment.ttr_adequacy",
            "Fragment.ttr_mtt_carrier_roundtrips", "Fragment.mtt_ranta_roundtrips",
            "Fragment.preservation_extends_to_meets", "Fragment.reflection_extends_to_meets",
            "Fragment.transport_split_commutes_on_witnesses", "Fragment.whole_carrier_inhabitation",
            "Fragment.ModelSeparation.separating_models_admissible",
            "Fragment.ModelSeparation.atomic_truth_agreement_not_meet_agreement",
        ):
            self.assertIn(PREFIX + name, names)

    def test_linked_without_theory_or_source_promotion(self):
        rec = record()
        self.assertEqual(rec["determination"], "not_applicable")
        self.assertEqual(rec["faithfulness"]["verdict"], "not_applicable")
        self.assertEqual(rec["assessment_status"], "incomplete")
        self.assertEqual(rec["sources"], [])
        atlas = json.loads((HERE / "atlas.json").read_text())
        self.assertEqual(len(atlas["files"]), 87)
        self.assertEqual(len(atlas["papers"]), 230)
        self.assertEqual(sum(f["_key"] == KEY for f in atlas["files"]), 1)
        self.assertTrue(all(rec["file"] not in p.get("coq_files", []) for p in atlas["papers"]))
        for key in ("ttr__mtt", "mtt__ranta"):
            profile = next(e["_profile"] for e in atlas["edges"] if e["_key"] == key)
            support = next(s for s in profile["support"] if s["record_key"] == KEY)
            self.assertEqual(support["source_sha256"], hashlib.sha256((ROOT / rec["file"]).read_bytes()).hexdigest())
            self.assertEqual(profile["theory_relation"], "unassessed")
            self.assertTrue(all(o["status"] == "unassessed" for o in profile["obligations"]))
        for field in ("theorems", "proved", "admitted"):
            self.assertEqual(atlas["stats"][field], sum(f.get("counts", {}).get(field, 0) for f in atlas["files"]))


if __name__ == "__main__":
    unittest.main()
