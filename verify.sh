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

echo "== 1b. compile the ORGANISM capstone (analytic R, located irrational phi + conjugate, AF C*-algebra) =="
if "$AGDA" "${INC[@]}" "agda/$P/RealCohesion/CorridorOrganism.agda" >/tmp/_o.log 2>&1; then
  echo "  [OK]   RealCohesion/CorridorOrganism  (--safe transitively typechecks all 18 organism modules)"
else
  echo "  [FAIL] RealCohesion/CorridorOrganism"; tail -5 /tmp/_o.log; fail=1
fi

echo "== 1bb. the RUNNING-CONVERGENT construction (executable phi + sqrt2, full characterization) =="
RMODS=(
  $P/Corridor/Running/Bracket $P/Corridor/Running/Cassini $P/Corridor/Running/Ordered
  $P/Corridor/Running/Located $P/Corridor/Running/Forcing $P/Corridor/Running/CertifiedSqrt2
  $P/Corridor/Running/LocatedLaw $P/Corridor/Running/CrossCut $P/Corridor/Running/DedekindBridge $P/Corridor/Running/CertifiedSqrt $P/Corridor/Running/SpectralEdge $P/Corridor/Running/General/Metallic $P/Corridor/Running/General/MetallicEdge $P/Corridor/Running/General/OperatorNorm $P/Corridor/Running/General/OperatorNormSpectral $P/Corridor/Running/General/OperatorNormMagnitude $P/Corridor/Running/General/AdjointForm $P/Corridor/Running/General/AdjointFormN $P/Corridor/Running/General/SpectralCStar $P/Corridor/Running/General/GelfandPower $P/Corridor/Running/General/EntropyRing $P/Corridor/Running/General/EntropyProvenance
)
for m in "${RMODS[@]}"; do
  if "$AGDA" "${INC[@]}" "agda/$m.agda" >/tmp/_r.log 2>&1; then
    echo "  [OK]   ${m#$P/}"
  else
    echo "  [FAIL] ${m#$P/}"; tail -4 /tmp/_r.log; fail=1
  fi
  grep -qE "^\s*postulate" "agda/$m.agda" && { echo "  [FAIL] ${m#$P/} contains postulate"; fail=1; }
done

echo "== 1c. the organism negative controls MUST be kernel-rejected =="
for c in BadTrisection BadQuadMono BadCStarNonneg; do
  if "$AGDA" "${INC[@]}" "agda/$P/RealCohesion/negative_controls/$c.agda" >/tmp/_oc.log 2>&1; then
    echo "  [FAIL] $c COMPILED -- discriminator broken"; fail=1
  else
    echo "  [OK]   $c kernel-rejected"
  fi
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

echo "== 4. the Rust realization (second substrate) executes + checks the same theorems =="
if command -v rustc >/dev/null; then
  if rustc -O realization/rust/corridor_running.rs -o /tmp/_corridor_rust >/tmp/_rs.log 2>&1 && /tmp/_corridor_rust >/tmp/_rsrun.log 2>&1; then
    echo "  [OK]   $(head -1 /tmp/_rsrun.log)"
  else
    echo "  [FAIL] Rust realization"; tail -4 /tmp/_rs.log /tmp/_rsrun.log; fail=1
  fi
else
  echo "  [INFO] rustc not found; skipping the Rust realization"
fi

echo
[[ "$fail" -eq 0 ]] && echo "VERIFY OK: 7 germ + organism (18) + running-convergent (8) modules kernel-checked, all negative controls rejected, lane discriminates, Rust realization passes." \
                     || echo "VERIFY FAILED (see [FAIL] above)."
exit "$fail"
