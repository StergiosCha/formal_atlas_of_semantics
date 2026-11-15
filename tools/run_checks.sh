#!/usr/bin/env bash
# Run the reporting and provenance checks from the CI "reporting" job.
#
# Usage (from anywhere in the repository):
#   bash tools/run_checks.sh            # Python and Node checks
#   bash tools/run_checks.sh --editor   # also rebuild the bundled Coq editor
#
# Requires Python 3 with fastapi and uvicorn, and Node.js 22.
# Coq compilation and record verification are separate: see the README.

set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

step() { printf '\n== %s\n' "$*"; }

if [[ "${1:-}" == "--editor" ]]; then
  step "Rebuild the bundled editor"
  npm ci --prefix tool/editor --ignore-scripts --no-fund --no-audit
  npm --prefix tool/editor run build
  git diff --exit-code -- atlas_data/site/vendor
fi

step "Source registry"
python3 atlas_data/source_registry.py

step "Python tests"
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 -m unittest discover -s tool/llm -p 'test_*.py'
python3 tool/checker/test_workspace.py
python3 tool/checker/test_sessions.py

step "Consolidated evidence is up to date"
python3 atlas_data/consolidate.py
git diff --exit-code -- atlas_data/atlas.json atlas_data/ATLAS.md

step "Site build and rendering tests"
python3 atlas_data/build_site.py
for test in landing reading source_registry claim_comparison rosch_campaign \
            outcomes proofs research edge_profiles workspace; do
  node "atlas_data/site/test_${test}.cjs"
done

step "Whitespace"
git diff --check

printf '\nAll reporting checks passed.\n'
