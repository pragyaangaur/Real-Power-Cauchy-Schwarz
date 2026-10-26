#!/bin/bash
# Builds the library and Solution.lean, fails on any sorry, native_decide or declared axiom, and
# prints the axioms of every theorem named in THEOREMS. Passes only if each depends on propext,
# Classical.choice and Quot.sound at most. Challenge.lean is left out of the build on purpose,
# because its statements are sorry by design.
set -u
cd "$(dirname "$0")/.."
bad=0
build=$(lake build RealPowerCauchySchwarz Solution 2>&1); code=$?
[ $code -ne 0 ] && { echo "$build"; echo "FAIL: lake build exited with code $code"; exit 1; }
echo "$build" | grep -qE "declaration uses .sorry." && { echo "FAIL: sorry present"; bad=1; }
grep -nE "native_decide|^\s*(axiom|opaque)\s" RealPowerCauchySchwarz/*.lean Challenge.lean Solution.lean && { echo "FAIL: native_decide, axiom or opaque in source"; bad=1; }
tmp=".check_axioms.lean"
printf "import RealPowerCauchySchwarz\nimport Solution\n" > "$tmp"
while read -r t; do [ -n "$t" ] && echo "#print axioms $t" >> "$tmp"; done < THEOREMS
out=$(lake env lean "$tmp" 2>&1); rm -f "$tmp"
echo "$out"
echo "$out" | grep -q "sorryAx" && { echo "FAIL: sorryAx in axioms"; bad=1; }
ax=$(echo "$out" | grep -oE "depends on axioms: \[[^]]*\]" | sed -E 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/ //g' | sort -u | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$ax" ] && { echo "FAIL: non-standard axioms: $ax"; bad=1; }
n=$(echo "$out" | grep -c "depends on axioms\|does not depend on any axioms")
[ "$n" -lt "$(grep -c . THEOREMS)" ] && { echo "FAIL: axioms not printed for every theorem"; bad=1; }
[ $bad -eq 0 ] && echo "PASS: every theorem in THEOREMS compiles with no sorry and only standard axioms"
exit $bad
