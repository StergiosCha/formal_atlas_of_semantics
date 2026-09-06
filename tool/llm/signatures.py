"""Generate signatures.json — each atlas theory's actual vocabulary.

v0 of A3_PLAN's signature manifest ("a NOT-STATABLE without a signature
manifest behind it is a guess wearing a badge"), produced from verify.py's
comment-stripped parse rather than SerAPI (step 7 upgrades this). Fed into
the draft prompt so models stop guessing constant names, and rendered by
the /check page as the theory's browsable vocabulary.

Run from anywhere; writes signatures.json next to this file.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ATLAS_DATA = os.path.join(os.path.dirname(os.path.dirname(HERE)), "atlas_data")
sys.path.insert(0, ATLAS_DATA)
import verify  # noqa: E402  (the A3 verifier: parse(), logical_name())

FILES = [
    "atlas/montague/PTQ.v", "atlas/dynamic/DPL.v", "atlas/inquisitive/InqB.v",
    "atlas/mtt_ranta/MTT.v", "atlas/mtt_ranta/Ranta.v",
    "atlas/mtt_ranta/Ranta_GQ.v", "atlas/mtt_ranta/DTS.v",
    "atlas/probabilistic/RSA.v", "atlas/categorical/DisCoCat.v",
    "atlas/type_logical/Lambek.v", "atlas/montague/PTQ_vs_Lambek.v",
    "atlas/montague/PTQ_vs_MTT.v", "atlas/mtt_ranta/MTT_vs_Ranta.v",
]


def main() -> None:
    out = {}
    for rel in FILES:
        path = os.path.join(verify.REPO, rel)
        decls, _ = verify.parse(path)
        mod = verify.logical_name(path)
        qual = lambda d: ".".join(d["modpath"] + [d["name"]])
        out[mod] = {
            "file": rel,
            "definitions": [qual(d) for d in decls if d["kind"] == "definition"],
            "theorems": [qual(d) for d in decls if d["kind"] == "theorem"
                         and d["status"] == "proved"],
        }
    dst = os.path.join(HERE, "signatures.json")
    json.dump(out, open(dst, "w"), indent=1, ensure_ascii=False)
    n = sum(len(v["definitions"]) + len(v["theorems"]) for v in out.values())
    print(f"wrote {dst}: {len(out)} theories, {n} named constants/theorems")


if __name__ == "__main__":
    main()
