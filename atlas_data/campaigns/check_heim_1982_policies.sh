#!/usr/bin/env bash
set -euo pipefail
# Run from the repository root; no previously compiled Heim objects reused.
heim_policy_build=$(mktemp -d "${TMPDIR:-/tmp}/atlas-heim-policies.XXXXXX")
mkdir "$heim_policy_build/dynamic"
echo "Fresh policy build and logs: $heim_policy_build"
coqc --version
units=(Heim1982 Heim1982_Examples Heim1982_Extensions Heim1982_Indexed
       Heim1982_Binding Heim1982_Integration Heim1982_EndToEnd Heim1982_Policies)
modules=()
for unit in "${units[@]}"; do
  cp "atlas/dynamic/$unit.v" "$heim_policy_build/dynamic/"
  coqc -q -R "$heim_policy_build" "" "$heim_policy_build/dynamic/$unit.v" \
    > "$heim_policy_build/$unit.log" 2>&1 || {
      cat "$heim_policy_build/$unit.log"
      exit 1
    }
  modules+=("dynamic.$unit")
  echo "Compiled $unit"
done
coqchk -silent -R "$heim_policy_build" "" "${modules[@]}" \
  > "$heim_policy_build/coqchk.log" 2>&1 || {
    cat "$heim_policy_build/coqchk.log"
    exit 1
  }
echo "Fresh compilation and kernel recheck passed."
