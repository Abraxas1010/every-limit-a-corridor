#!/usr/bin/env python3
"""Standalone authority-lane verifier for the corridor bundle.

This vendors the engine's `agda_runtime_roundtrip_outcome` validator (a pure,
30-line function) so the lane's *discrimination* can be re-checked without the
full repo: the genuine artifact is ACCEPTED, and every degenerate / spoofed /
tampered variant is REJECTED. The negative controls are the point — a runtime
authority that cannot reject bad evidence is worse than none.

Run:  python3 realization/verify_lane.py     (from the bundle root)

This checks the validator's accept/reject logic and that the bare-metal programs
are on disk and non-trivial. The *live* kernel re-run of the witness modules and
the degenerate control is done by `verify.sh` (which invokes Agda directly); the
producer-reproducibility checks (T13/T14) need Agda + the full producer and run
from the full repo. What this file establishes standalone: the lane accepts the
genuine evidence and rejects every bad variant.
"""
from __future__ import annotations
import copy, json, sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent          # bundle root
ARTIFACT = ROOT / "realization" / "agda_runtime_roundtrip.json"
METAL = ROOT / "artifacts" / "boundary_metal"


def agda_runtime_roundtrip_outcome(payload: dict[str, Any]) -> str | None:
    """Vendored verbatim from scripts/claim_gate.py (the single source of truth).

    Admissible iff every POSITIVE control passed (modules compiled --cubical
    --safe, postulate-free, extracted to non-trivial bare-metal programs) AND the
    NEGATIVE control held (the degenerate `true ≡ false` collapse was
    kernel-rejected). Structure check; the producer genuinely executes the
    controls and is replayable.
    """
    if not isinstance(payload, dict):
        return None
    pos = payload.get("positive_control") if isinstance(payload.get("positive_control"), dict) else {}
    neg = payload.get("negative_control") if isinstance(payload.get("negative_control"), dict) else {}
    ok = (
        payload.get("schema") == "boundary.agda_runtime_roundtrip.v1"
        and pos.get("modules_safe_compiled") is True
        and pos.get("postulate_free") is True
        and pos.get("witnesses_extracted") is True
        and pos.get("readback_nontrivial") is True
        and int(pos.get("witness_program_count") or 0) > 0
        and neg.get("forced_true_substitution_must_fail") is True
        and neg.get("degenerate_rejected") is True
        and int(payload.get("expected_steps") or 0) > 0
        and not payload.get("errors")
    )
    return "accepted_agda_runtime_roundtrip" if ok else None


results: list[tuple[str, bool]] = []
def check(name: str, cond: bool) -> None:
    results.append((name, bool(cond)))

def genuine() -> dict:
    return json.loads(ARTIFACT.read_text(encoding="utf-8"))

def mutate(path: list, value) -> dict:
    d = copy.deepcopy(genuine()); node = d
    for k in path[:-1]:
        node = node[k]
    node[path[-1]] = value
    return d


if not ARTIFACT.exists():
    print(f"artifact not found: {ARTIFACT}", file=sys.stderr); sys.exit(2)

# T1: the genuine artifact is ACCEPTED
g = genuine()
check("genuine artifact accepted", agda_runtime_roundtrip_outcome(g) == "accepted_agda_runtime_roundtrip")
check("genuine artifact's own outcome field is accepted", g.get("outcome") == "accepted_agda_runtime_roundtrip")

# T2..T11: every degenerate mutation is REJECTED (returns None)
for name, path, val in [
    ("wrong schema", ["schema"], "boundary.runtime_backend_artifact.v1"),
    ("modules_safe_compiled False", ["positive_control", "modules_safe_compiled"], False),
    ("postulate_free False", ["positive_control", "postulate_free"], False),
    ("witnesses_extracted False", ["positive_control", "witnesses_extracted"], False),
    ("readback_nontrivial False", ["positive_control", "readback_nontrivial"], False),
    ("witness_program_count 0", ["positive_control", "witness_program_count"], 0),
    ("forced_true_substitution_must_fail False", ["negative_control", "forced_true_substitution_must_fail"], False),
    ("degenerate_rejected False", ["negative_control", "degenerate_rejected"], False),
    ("expected_steps 0", ["expected_steps"], 0),
    ("errors non-empty", ["errors"], ["something broke"]),
]:
    check(f"REJECT: {name}", agda_runtime_roundtrip_outcome(mutate(path, val)) is None)

# T12: a SPOOFED raw outcome cannot rescue a failing control
spoof = mutate(["positive_control", "modules_safe_compiled"], False)
spoof["outcome"] = "accepted_agda_runtime_roundtrip"
check("REJECT: spoofed outcome with failing control", agda_runtime_roundtrip_outcome(spoof) is None)

# T16: the bare-metal programs are on disk and non-trivial (bundle paths)
for m in g.get("positive_control", {}).get("modules", []):
    p = METAL / Path(m["witness_program"]).name
    check(f"program on disk + non-trivial: {m.get('module','?')}", p.exists() and int(m.get("program_nodes") or 0) > 0)
    check(f"safe + postulate-free recorded: {m.get('module','?')}", m.get("safe_compiled") is True and m.get("postulate_free") is True)

passed = sum(1 for _, ok in results if ok); total = len(results)
for name, ok in results:
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
print(f"\n{passed}/{total} lane checks passed (validator discrimination, standalone)")
sys.exit(0 if passed == total else 1)
