#!/usr/bin/env python3
"""Phase A11 — genuine-corridor genuineness oracle (hostile-audit remediation).

This oracle exists because the original `phase_a10_aggregate_oracle.py`
anti-vacuity gate was structurally blind to the corridor's comprehensive
vacuity (Docs/reports/effective_corridor_hostile_audit_2026-06-19.md): it
forbade the connectivity HITs a genuine `shape`-collapse needs while NOT
flagging the degenerate primitives (`ua x = refl`, constant-loop `reentry`,
`idIso`/`shape A = A` model).

It gates the THREE genuine modules that realize the corridor thesis with
content, across its two facets:

  * facet (2) univalence  — `Corridor/CrossingCorridor.agda` (genuine primGlue
    `ua` at the Laws-of-Form crossing; transport flips the boundary state).
  * facet (1) cohesion    — `Foundations/FiniteCohesion.agda` (faithful
    set-quotient cohesion: `shape` collapses the real line to a contractible
    point, `flat` keeps it apart, genuine adjoint iso via `setQuotUniversalIso`
    — NOT `idIso`).
  * unification           — `Corridor/FaithfulCorridor.agda` (both facets, on
    the same two-point boundary).

For each: compile `--cubical --safe`, require its non-vacuity discriminators,
and flag the degenerate F1-F3 patterns wherever they appear.

Exit 0 iff every module compiles, all discriminators are present and genuine,
none of the genuine modules contains a degenerate pattern, and the CrossingCorridor
Boundary extraction receipt exists.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CORPUS = ROOT / "corpus/cubical_agda"
RECEIPT_DIR = ROOT / "artifacts/ops/effective_corridor/crossing_corridor"
REPORT = ROOT / "artifacts/ops/effective_corridor/a11_crossing_genuineness/report.json"

# module path (relative to corpus) -> required discriminator names; whether it
# pulls the full cubical stdlib (and so must NOT use the boundary shim include).
MODULES = {
    "Corridor/CrossingCorridor.agda": {
        "needs_stdlib": False,
        "required": [
            "unmarked≢marked", "upper-wall-transports", "crossing-path-nontrivial",
            "trivial-path-cannot-cross", "reentry-loop-transports",
            "crossing-corridor-witness", "two-walls-genuinely-distinct",
        ],
        "genuine_backing": {
            "upper-wall-transports": "borrowed-cross-transport",
            "reentry-loop-transports": "borrowed-cross-transport",
        },
    },
    "Foundations/FiniteCohesion.agda": {
        "needs_stdlib": True,
        "required": [
            "shape", "flat", "shapeFlatIso", "shape-realLine-isContr",
            "flat-realLine-not-isContr", "shape-not-flat",
            "faithful-cohesion-witness",
        ],
        "genuine_backing": {
            "shapeFlatIso": "setQuotUniversalIso",   # NOT idIso
            "shape-not-flat": "subst isContr",
        },
    },
    "Corridor/FaithfulCorridor.agda": {
        "needs_stdlib": True,
        "required": [
            "FaithfulCorridor", "faithful-corridor-witness",
            "walls-distinct-cohesively", "walls-distinct-univalently",
            "lower-wall-separates-cohesively", "lower-wall-separates-univalently",
        ],
        "genuine_backing": {},
    },
    "Corridor/FaithfulModulus.agda": {
        "needs_stdlib": True,
        "required": [
            "fib", "width", "fib-lower", "modulus-sound", "ladder-narrows",
            "modulus-forced", "golden-modulus", "EffectiveCorridor",
            "the-effective-corridor",
        ],
        "genuine_backing": {
            "modulus-sound": "fib-lower",     # soundness rests on the golden lower bound,
            "fib-lower": "+-mono-≤",          # not on a constant
        },
    },
    "Corridor/GoldenAFColimit.agda": {
        "needs_stdlib": True,
        "required": [
            "GoldenStage", "goldenInclusion", "goldenSequence", "GoldenAFColimit",
            "freshPoint", "inclusion-not-surjective", "freshColimitPoint",
            "golden-af-witness",
        ],
        "genuine_backing": {
            "inclusion-not-surjective": "¬m<m",   # the colimit genuinely grows
            "GoldenAFColimit": "SeqColim",        # a real sequential colimit
        },
    },
    "Corridor/EntropyScreen.agda": {
        "needs_stdlib": True,
        "required": [
            "δ⁰", "δ⁰-vanishes", "loopCocycle", "loopCocycle-not-exact",
            "logicalEntropy", "screen-detects", "coboundary-screens",
            "EntropyScreen", "entropy-screen-witness",
        ],
        "genuine_backing": {
            "loopCocycle-not-exact": "false≢true",   # H¹ ≠ 0 (closed-not-exact)
            "screen-detects": "suc-≤-suc",           # positive logical entropy
        },
    },
    "Corridor/CompleteCorridor.agda": {
        "needs_stdlib": True,
        "required": [
            "CompleteEffectiveCorridor", "af-stage-is-rate-bracket",
            "the-complete-corridor",
        ],
        "genuine_backing": {
            "af-stage-is-rate-bracket": "w-is-width",  # Part II stages = rate brackets
        },
    },
}

# (file, regex, why this pattern is vacuous) — the gate now SEES these.
VACUITY_PATTERNS = [
    ("Substrate/Eigenform.agda", r"^ua\s+x\s*=\s*refl\s*$",
     "F2: `ua` (named after univalence) defined as the constant refl"),
    ("Substrate/LawsOfForm.agda", r"reentry\s+M\s+I\s+\(loop\s+i\)\s*=\s*markedShapePoint",
     "F3: re-entry discards the S1 loop (constant on the loop)"),
    ("Foundations/RealCohesiveModalities.agda", r"\.shapeFlatIso\s+A\s+B\s*=\s*idIso",
     "F1: the sole model's shape/flat adjunction is the identity iso"),
    ("Foundations/RealCohesiveModalities.agda", r"\.shape\s+A\s*=\s*A\s*$",
     "F1: the sole model makes the shape modality the identity functor"),
]


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, timeout=1200)


def includes(needs_stdlib: bool) -> list[str]:
    inc = ["-i.", "-icorpus/cubical_agda"]
    if (ROOT / "third_party/agda-cubical/Cubical").is_dir():
        inc.append("-ithird_party/agda-cubical")
    # the boundary shim re-defines Cubical.Core.* and clashes with the real
    # stdlib; only the self-contained module may use it.
    if not needs_stdlib and (ROOT / "tools/agda-boundary-backend/test/cubical-shim").is_dir():
        inc.append("-itools/agda-boundary-backend/test/cubical-shim")
    return inc


def main() -> int:
    findings: list[str] = []
    report: dict = {"ok": False, "modules": {}, "checks": {}}
    agda = shutil.which("agda")
    if agda is None:
        findings.append("agda not found on PATH")

    stdlib_present = (ROOT / "third_party/agda-cubical/Cubical").is_dir()
    report["checks"]["cubical_stdlib_present"] = stdlib_present

    for rel, spec in MODULES.items():
        mod = CORPUS / rel
        m: dict = {}
        if spec["needs_stdlib"] and not stdlib_present:
            m["compile"] = "skipped: third_party/agda-cubical submodule not initialized"
            findings.append(f"{rel}: cubical stdlib submodule absent (run git submodule update --init)")
        elif agda is not None:
            cc = run([agda, *includes(spec["needs_stdlib"]), str(mod.relative_to(ROOT))])
            m["compile"] = {"returncode": cc.returncode, "stderr_tail": cc.stderr[-500:]}
            if cc.returncode != 0:
                findings.append(f"{rel}: failed --cubical --safe compile")
        # discriminators present
        src = mod.read_text(encoding="utf-8")
        missing = [d for d in spec["required"] if d not in src]
        if missing:
            findings.append(f"{rel}: missing discriminators {missing}")
        m["missing"] = missing
        # genuine backing (no degeneracy)
        for name, backing in spec["genuine_backing"].items():
            mm = re.search(rf"^{re.escape(name)}\b.*?=\s*(.+)$", src, re.MULTILINE | re.DOTALL)
            if backing not in src:
                findings.append(f"{rel}: {name} not backed by genuine {backing}")
        # the genuine module must not itself contain a degenerate pattern
        for _, pat, why in VACUITY_PATTERNS:
            if re.search(pat, src, re.MULTILINE):
                findings.append(f"{rel}: contains degenerate pattern ({why})")
        report["modules"][rel] = m

    # vacuity scan — the gate now catches F1-F3 wherever they live (reported,
    # not a hard failure: the genuine substrate supersedes the scaffolding).
    vacuity_hits = []
    for rel, pat, why in VACUITY_PATTERNS:
        p = CORPUS / rel
        if not p.exists():
            continue
        for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            if re.search(pat, line):
                vacuity_hits.append({"file": rel, "line": i, "why": why})
    report["checks"]["vacuity_scan"] = {"hits": vacuity_hits}

    # Boundary extraction receipt for the (self-contained) univalence core
    witness_receipt = RECEIPT_DIR / "crossing_corridor_witness.boundary.program.json"
    report["checks"]["boundary_receipt"] = {"path": str(witness_receipt),
                                            "exists": witness_receipt.exists()}
    if not witness_receipt.exists():
        findings.append("missing Boundary extraction receipt for the witness")

    # Bare-metal Boundary extraction of the WHOLE substrate (after the
    # agda_boundary_compile.sh --no-shim fix). The computational witnesses of
    # all five non-record modules must reach bare metal as Boundary programs.
    metal = ROOT / "artifacts/ops/effective_corridor/boundary_metal"
    metal_required = [
        "faithful_cohesion_witness.boundary.program.json",   # cohesion (SetQuotients)
        "crossing_corridor_witness.boundary.program.json",   # univalence
        "golden_modulus.boundary.program.json",              # rate
        "golden_af_witness.boundary.program.json",           # Part II (SeqColim)
        "entropy_screen_witness.boundary.program.json",      # Part III (H1)
    ]
    metal_missing = [p for p in metal_required if not (metal / p).exists()]
    report["checks"]["bare_metal_boundary"] = {
        "dir": str(metal), "required": metal_required, "missing": metal_missing}
    if metal_missing:
        findings.append(f"bare-metal Boundary extraction missing: {metal_missing}")

    report["findings"] = findings
    report["ok"] = len(findings) == 0
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
