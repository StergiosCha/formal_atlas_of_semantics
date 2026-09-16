#!/usr/bin/env bash
set -euo pipefail

# Invoke from the repository root. Fresh copies prevent stale .vo reuse and
# leave the research corpus and historical verification records untouched.
review_dir=atlas_data/audits/source_reviews_2026_09_15
test -f "$review_dir/ReviewChecks.v"
review_tmp=$(mktemp -d "${TMPDIR:-/tmp}/atlas-source-review.XXXXXX")
echo "Review build and logs retained at: $review_tmp"
cp shallow/MontagueFragment.v extras/FCS.v extras/FCS2.v \
   extras/DonkeyScope.v atlas/categorical/DisCoCat.v \
   "$review_dir/ReviewChecks.v" "$review_tmp/"
coqc --version
for unit in MontagueFragment FCS FCS2 DonkeyScope DisCoCat ReviewChecks; do
  echo "Compiling $unit"
  coqc -q -Q "$review_tmp" "" "$review_tmp/$unit.v" \
    > "$review_tmp/$unit.log" 2>&1 || {
      cat "$review_tmp/$unit.log"
      exit 1
    }
done
cat "$review_tmp/ReviewChecks.log"
coqchk -silent -Q "$review_tmp" "" ReviewChecks \
  > "$review_tmp/coqchk.log" 2>&1 || {
    cat "$review_tmp/coqchk.log"
    exit 1
  }
echo "Fresh compilation and independent kernel recheck passed."
echo "This is not source-outcome approval; inspect the assumption report above."
