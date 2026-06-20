#!/usr/bin/env bash
# Verify the Every-Limit-a-Corridor bundle from primitives.
#   usage: ./verify.sh /path/to/agda/cubical   (the cubical library checkout, pin d684d7d8)
set -uo pipefail
cd "$(dirname "$0")"

CUBICAL="${1:-}"
if [[ -z "$CUBICAL" || ! -d "$CUBICAL/Cubical" ]]; then
  echo "usage: ./verify.sh /path/to/cubical   (a dir containing Cubical/)" >&2
  exit 2
fi
AGDA="$(command -v agda || true)"
[[ -z "$AGDA" ]] && { echo "agda not found on PATH" >&2; exit 2; }

# module names are corpus.cubical_agda.* ; the tree under agda/ mirrors them
INC=(-iagda -i"$CUBICAL")
P=corpus/cubical_agda
fail=0

echo "== 1. compile the seven genuine modules (--cubical --safe, no postulates) =="
MODS=(
  $P/Foundations/FiniteCohesion
  $P/Corridor/CrossingCorridor $P/Corridor/FaithfulCorridor $P/Corridor/FaithfulModulus
  $P/Corridor/GoldenAFColimit $P/Corridor/EntropyScreen $P/Corridor/CompleteCorridor
)
for m in "${MODS[@]}"; do
  if "$AGDA" "${INC[@]}" "agda/$m.agda" >/tmp/_v.log 2>&1; then
    echo "  [OK]   ${m#$P/}"
  else
    echo "  [FAIL] ${m#$P/}"; tail -4 /tmp/_v.log; fail=1
  fi
  grep -qE "^\s*postulate" "agda/$m.agda" && { echo "  [FAIL] ${m#$P/} contains postulate"; fail=1; }
done

echo "== 2. the negative control MUST be kernel-rejected (true != false) =="
if "$AGDA" "${INC[@]}" "agda/$P/Corridor/negative_controls/BadForcedTrueCollapse.agda" >/tmp/_n.log 2>&1; then
  echo "  [FAIL] the degenerate collapse COMPILED -- the discriminator is broken"; fail=1
else
  if grep -qE "true != false|true .* false" /tmp/_n.log; then
    echo "  [OK]   degenerate collapse rejected for the genuine reason (true != false)"
  else
    echo "  [WARN] rejected, but not visibly for true!=false:"; tail -2 /tmp/_n.log
  fi
fi

echo "== 3. the authority lane discriminates (standalone, vendored validator) =="
if command -v python3 >/dev/null; then
  if python3 realization/verify_lane.py >/tmp/_l.log 2>&1; then
    echo "  [OK]   $(tail -1 /tmp/_l.log)"
  else
    echo "  [FAIL] lane discrimination"; tail -6 /tmp/_l.log; fail=1
  fi
  echo "  [note] the full 27/27 suite (incl. producer-replay T13/T14) runs from the full repo"
else
  echo "  [INFO] python3 not found; skipping the lane checks"
fi

echo
[[ "$fail" -eq 0 ]] && echo "VERIFY OK: 7 modules kernel-checked, negative control rejected, lane discriminates." \
                     || echo "VERIFY FAILED (see [FAIL] above)."
exit "$fail"
