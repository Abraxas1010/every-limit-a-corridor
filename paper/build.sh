#!/usr/bin/env bash
# IAOM paper build pipeline.
# Three pdflatex passes + bibtex resolve all cross-references.

set -euo pipefail

cd "$(dirname "$0")"

PAPER="${1:-paper}"
MODE="${2:-technical}"
if [[ "${PAPER}" == "publication" ]]; then
  PAPER="paper"
  MODE="publication"
fi
JOB="${PAPER}"
LATEX_TARGET=("${PAPER}.tex")
if [[ "${MODE}" == "publication" ]]; then
  JOB="${PAPER}_publication"
  LATEX_TARGET=("\\def\\IAOMPUBLICATION{1}\\input{${PAPER}.tex}")
elif [[ "${MODE}" != "technical" ]]; then
  echo "[build] unknown mode: ${MODE} (expected technical|publication)"
  exit 2
fi

echo "[build] pdflatex pass 1..."
pdflatex -interaction=nonstopmode -jobname="${JOB}" "${LATEX_TARGET[@]}" > /dev/null 2>&1 || true

echo "[build] bibtex..."
bibtex "${JOB}" > /dev/null 2>&1 || true

echo "[build] pdflatex pass 2..."
pdflatex -interaction=nonstopmode -jobname="${JOB}" "${LATEX_TARGET[@]}" > /dev/null 2>&1 || true

echo "[build] pdflatex pass 3..."
pdflatex -interaction=nonstopmode -jobname="${JOB}" "${LATEX_TARGET[@]}"

if [[ -f "${JOB}.pdf" ]]; then
  PAGES=$(pdfinfo "${JOB}.pdf" 2>/dev/null | awk '/^Pages:/ {print $2}')
  echo "[build] OK: ${JOB}.pdf (${PAGES:-?} pages)"
else
  echo "[build] FAILED: no PDF produced"
  exit 1
fi
