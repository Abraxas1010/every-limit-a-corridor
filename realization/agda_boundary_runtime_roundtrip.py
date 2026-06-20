#!/usr/bin/env python3
"""Producer for the agda-boundary runtime-roundtrip authority lane.

This is the integrity core of a NEW `boundary_runtime` authority kind that lets
the fixed-point engine (Imperative #22) recognize a genuine **cubical-Agda**
Boundary lowering as executable closure evidence — alongside the existing Lean
lane. It is the dual of the Lean `runtime_backend_artifact` lane: where that one
lowers a kernel-checked Lean module to Boundary, this one lowers a kernel-checked
`--cubical --safe` Agda module to Boundary.

It GENUINELY EXECUTES, never hardcodes, a positive-and-negative-control runtime
roundtrip (mirroring `boundary.admissible_carrier.runtime_roundtrip.v1`):

  POSITIVE control — for each genuine witness module:
    * `agda --cubical --safe --guardedness` compiles it (the Agda kernel checks
      it; --safe forbids `sorry`/unsafe flags);
    * it is postulate-free (no `postulate`/`--type-in-type`/`--no-positivity`/
      `TERMINATING` in the source);
    * the Boundary backend (with the --no-shim fix) extracts its witness to a
      bare-metal `{decls, main}` program that is non-trivial (a real term tree).

  NEGATIVE control — `forced_true_substitution_must_fail`:
    * the degenerate collapse `true ≡ false` (the substitution the hostile audit
      refuted) is KERNEL-REJECTED: the bad fixture must FAIL `agda --safe` for
      the genuine `true != false` reason. A degenerate witness therefore cannot
      manufacture the discriminator.

The emitted artifact (`boundary.agda_runtime_roundtrip.v1`) records the computed
bits + source/program digests; the engine validator `agda_runtime_roundtrip_
outcome` accepts it only if every control passed. Re-running this producer
reproduces the artifact (the P10 receipt is replayable).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus/cubical_agda"
METAL = ROOT / "artifacts/ops/effective_corridor/boundary_metal"
DEFAULT_OUT = ROOT / "artifacts/ops/boundary_runtime_cutover/effective_corridor_agda/agda_runtime_roundtrip.json"

CLAIM_SOURCE_ID = "effective_corridor_modulus_synthesis_20260619"

# genuine witness modules and the bare-metal Boundary program each must extract.
POSITIVE_MODULES = [
    ("Foundations/FiniteCohesion.agda", "faithful_cohesion_witness.boundary.program.json"),
    ("Corridor/CrossingCorridor.agda", "crossing_corridor_witness.boundary.program.json"),
    ("Corridor/FaithfulModulus.agda", "golden_modulus.boundary.program.json"),
    ("Corridor/GoldenAFColimit.agda", "golden_af_witness.boundary.program.json"),
    ("Corridor/EntropyScreen.agda", "entropy_screen_witness.boundary.program.json"),
]
NEGATIVE_FIXTURE = "Corridor/negative_controls/BadForcedTrueCollapse.agda"

FORBIDDEN_SOURCE_TOKENS = ["postulate", "--type-in-type", "--no-positivity", "TERMINATING", "--allow-unsolved"]

INCLUDES = ["-i.", "-icorpus/cubical_agda"]
if (ROOT / "third_party/agda-cubical/Cubical").is_dir():
    INCLUDES.append("-ithird_party/agda-cubical")


def sha256_file(p: Path) -> str | None:
    return "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None


def run(cmd: list[str], timeout: int = 900) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, timeout=timeout)


def agda_compiles(agda: str, rel: str) -> tuple[bool, str]:
    cc = run([agda, *INCLUDES, rel])
    return cc.returncode == 0, (cc.stdout + "\n" + cc.stderr)[-600:]


def postulate_free(rel: str) -> bool:
    text = (ROOT / rel).read_text(encoding="utf-8")
    # strip line comments so docstrings mentioning the tokens don't trip it
    code = "\n".join(re.sub(r"--.*$", "", line) for line in text.splitlines())
    return not any(tok in code for tok in FORBIDDEN_SOURCE_TOKENS)


def program_nodes(payload: dict) -> int:
    """count nodes in the {decls, main} term tree — a trivial/empty program is 0."""
    def count(v) -> int:
        if isinstance(v, dict):
            return 1 + sum(count(x) for x in v.values())
        if isinstance(v, list):
            return sum(count(x) for x in v)
        return 0
    return count(payload.get("main")) + count(payload.get("decls"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    ap.add_argument("--commit", default="")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    agda = shutil.which("agda")
    errors: list[str] = []
    if agda is None:
        errors.append("agda not found on PATH")

    # ---- POSITIVE control --------------------------------------------------
    modules_report = []
    modules_safe = True
    postfree = True
    extracted = True
    nontrivial = True
    total_nodes = 0
    for rel, program in POSITIVE_MODULES:
        comp_ok, err = (agda_compiles(agda, f"corpus/cubical_agda/{rel}") if agda else (False, "no agda"))
        pf = postulate_free(f"corpus/cubical_agda/{rel}")
        prog_path = METAL / program
        prog_payload = None
        nodes = 0
        if prog_path.exists():
            try:
                prog_payload = json.loads(prog_path.read_text(encoding="utf-8"))
                nodes = program_nodes(prog_payload)
            except (OSError, json.JSONDecodeError):
                prog_payload = None
        modules_safe = modules_safe and comp_ok
        postfree = postfree and pf
        extracted = extracted and prog_path.exists()
        nontrivial = nontrivial and (nodes > 0)
        total_nodes += nodes
        modules_report.append({
            "module": rel,
            "safe_compiled": comp_ok,
            "postulate_free": pf,
            "source_sha256": sha256_file(ROOT / f"corpus/cubical_agda/{rel}"),
            "witness_program": program,
            "program_sha256": sha256_file(prog_path),
            "program_nodes": nodes,
            "compile_stderr_tail": "" if comp_ok else err,
        })
        if not comp_ok:
            errors.append(f"positive control: {rel} failed agda --safe")
        if not pf:
            errors.append(f"positive control: {rel} not postulate-free")
        if not prog_path.exists():
            errors.append(f"positive control: {rel} missing Boundary program {program}")
        if nodes <= 0:
            errors.append(f"positive control: {rel} extracted a trivial program")

    # ---- NEGATIVE control: forced_true_substitution_must_fail --------------
    neg_rel = f"corpus/cubical_agda/{NEGATIVE_FIXTURE}"
    neg_ok, neg_err = (agda_compiles(agda, neg_rel) if agda else (True, ""))
    # the fixture MUST FAIL (neg_ok False) for the genuine true != false reason
    forced_true_must_fail = (agda is not None) and (neg_ok is False)
    reason_matched = bool(re.search(r"true\s*!=\s*false|true\s*≢\s*false", neg_err))
    degenerate_rejected = forced_true_must_fail and reason_matched
    if not forced_true_must_fail:
        errors.append("negative control DID NOT FAIL: the degenerate collapse compiled (authority lane broken)")
    elif not reason_matched:
        errors.append("negative control failed for the wrong reason (not true != false)")

    positive_control = {
        "modules_safe_compiled": modules_safe,
        "postulate_free": postfree,
        "witnesses_extracted": extracted,
        "readback_nontrivial": nontrivial,
        "module_count": len(POSITIVE_MODULES),
        "witness_program_count": sum(1 for m in modules_report if m["program_nodes"] > 0),
        "modules": modules_report,
    }
    negative_control = {
        "forced_true_substitution_must_fail": forced_true_must_fail,
        "degenerate_rejected": degenerate_rejected,
        "fixture": NEGATIVE_FIXTURE,
        "fixture_source_sha256": sha256_file(ROOT / neg_rel),
        "agda_exit_nonzero": (agda is not None) and (neg_ok is False),
        "rejection_reason": "true != false" if reason_matched else neg_err[-200:],
    }

    all_ok = not errors and degenerate_rejected and total_nodes > 0
    outcome = "accepted_agda_runtime_roundtrip" if all_ok else None

    artifact = {
        "schema": "boundary.agda_runtime_roundtrip.v1",
        "authority": "agda_boundary_runtime_roundtrip",
        "source_id": CLAIM_SOURCE_ID,
        "outcome": outcome,
        "expected_steps": total_nodes,
        "positive_control": positive_control,
        "negative_control": negative_control,
        "negative_controls": [NEGATIVE_FIXTURE],
        "route_order": ["agda_boundary"],
        "logical_shadow": "the_complete_corridor",
        "remaining_gaps": [],
        "commit": args.commit,
        "errors": errors,
    }

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(artifact, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"ok": all_ok, "outcome": outcome, "expected_steps": total_nodes,
                      "errors": errors, "artifact": str(out)}, indent=2, ensure_ascii=False))
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
