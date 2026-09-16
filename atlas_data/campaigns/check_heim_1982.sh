#!/usr/bin/env bash
set -euo pipefail
# From the repository root. Fresh dependency closure; no existing .vo reused.
heim_build=$(mktemp -d "${TMPDIR:-/tmp}/atlas-heim-1982.XXXXXX")
mkdir "$heim_build/dynamic"
echo "Fresh Heim build and logs: $heim_build"
coqc --version
for unit in Heim1982 Heim1982_Examples Heim1982_Extensions Heim1982_Indexed; do
  cp "atlas/dynamic/$unit.v" "$heim_build/dynamic/"
  coqc -q -R "$heim_build" "" "$heim_build/dynamic/$unit.v" \
    > "$heim_build/$unit.log" 2>&1 || {
      cat "$heim_build/$unit.log"
      exit 1
    }
  echo "Compiled $unit"
done
coqchk -silent -R "$heim_build" "" dynamic.Heim1982 \
  dynamic.Heim1982_Examples dynamic.Heim1982_Extensions dynamic.Heim1982_Indexed \
  > "$heim_build/coqchk.log" 2>&1 || {
    cat "$heim_build/coqchk.log"
    exit 1
  }
echo "Fresh compilation and kernel recheck passed."
echo "For every-theorem dependencies, run atlas_data/verify.py on the four files."
