#!/usr/bin/env bash
set -euo pipefail
# Run from the repository root. Rebuild the complete seven-module closure.
heim_integration_build=$(mktemp -d "${TMPDIR:-/tmp}/atlas-heim-integration.XXXXXX")
mkdir "$heim_integration_build/dynamic"
echo "Fresh integration build and logs: $heim_integration_build"
coqc --version
units=(Heim1982 Heim1982_Examples Heim1982_Extensions Heim1982_Indexed
       Heim1982_Binding Heim1982_Integration Heim1982_EndToEnd)
modules=()
for unit in "${units[@]}"; do
  cp "atlas/dynamic/$unit.v" "$heim_integration_build/dynamic/"
  coqc -q -R "$heim_integration_build" "" "$heim_integration_build/dynamic/$unit.v" \
    > "$heim_integration_build/$unit.log" 2>&1 || {
      cat "$heim_integration_build/$unit.log"
      exit 1
    }
  modules+=("dynamic.$unit")
  echo "Compiled $unit"
done
coqchk -silent -R "$heim_integration_build" "" "${modules[@]}" \
  > "$heim_integration_build/coqchk.log" 2>&1 || {
    cat "$heim_integration_build/coqchk.log"
    exit 1
  }
echo "Fresh compilation and kernel recheck passed."
