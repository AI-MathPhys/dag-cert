#!/usr/bin/env bash
# Prints the axioms of every theorem of JointRootCert.Manuscript (scripts/check_axioms.lean) and
# fails if any of them depends on an axiom other than propext, Classical.choice and Quot.sound
# (in particular on sorryAx), or if Lean reports an error.
# Requires the library to be built (`lake build`); the index module itself is not imported by
# JointRootCert.lean, so it is built here. Run from anywhere.
set -u
cd "$(dirname "$0")/.." || exit 1

if ! lake build JointRootCert.Manuscript >/dev/null 2>&1; then
  echo "FAIL: could not build JointRootCert.Manuscript"; exit 1
fi
out=$(lake env lean scripts/check_axioms.lean 2>&1)
status=$?
# `#print axioms` may wrap a long axiom list over several lines: join each report into one line.
joined=$(printf '%s\n' "$out" | awk '
  /^'"'"'/ { if (cur != "") print cur; cur = $0; next }
  { if (cur != "") cur = cur " " $0; else print }
  END { if (cur != "") print cur }')

expected=$(grep -c '^#print axioms' scripts/check_axioms.lean)
reports=$(printf '%s\n' "$joined" | grep -cE "depends on axioms|does not depend on any axioms")
bad=$(printf '%s\n' "$joined" | grep -E "depends on axioms" \
  | sed -E 's/.*depends on axioms: \[(.*)\].*/\1/' | tr ',' '\n' | sed -E 's/^ +| +$//g' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sort -u)

printf '%s\n' "$joined"
echo "----"
echo "theorems checked: $reports of $expected"
fail=0
if [ "$status" -ne 0 ] || printf '%s\n' "$out" | grep -q "error"; then
  echo "FAIL: Lean reported an error (exit status $status)"; fail=1
fi
if [ "$reports" -ne "$expected" ]; then
  echo "FAIL: expected $expected axiom reports, got $reports"; fail=1
fi
if printf '%s\n' "$out" | grep -q "sorryAx"; then
  echo "FAIL: some theorem depends on sorryAx"; fail=1
fi
if [ -n "$bad" ]; then
  echo "FAIL: axioms outside propext, Classical.choice, Quot.sound:"; printf '  %s\n' $bad; fail=1
fi
if [ "$fail" -ne 0 ]; then exit 1; fi
echo "OK: every theorem uses only propext, Classical.choice, Quot.sound"
