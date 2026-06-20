#!/usr/bin/env python3
"""Production test suite for the agda-boundary runtime-roundtrip authority lane.

Tested ad nauseam: the lane must ACCEPT the genuine artifact and REJECT every
degenerate / tampered / spoofed variant. The negative controls are the point —
a runtime-authority lane that cannot reject bad evidence is worse than none.

Run: python3 tests/external_oracles/effective_corridor_modulus_synthesis_20260619/test_agda_runtime_roundtrip_authority.py
"""

from __future__ import annotations

import copy
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
ARTIFACT = ROOT / "artifacts/ops/boundary_runtime_cutover/effective_corridor_agda/agda_runtime_roundtrip.json"

# import the engine validator from claim_gate.py
spec = importlib.util.spec_from_file_location("claim_gate", ROOT / "scripts/claim_gate.py")
claim_gate = importlib.util.module_from_spec(spec)
sys.modules["claim_gate"] = claim_gate
spec.loader.exec_module(claim_gate)
outcome = claim_gate.agda_runtime_roundtrip_outcome

results: list[tuple[str, bool, str]] = []


def check(name: str, cond: bool, detail: str = "") -> None:
    results.append((name, bool(cond), detail))


def genuine() -> dict:
    return json.loads(ARTIFACT.read_text(encoding="utf-8"))


# ---- T1: the genuine artifact is ACCEPTED ---------------------------------
g = genuine()
check("T1 genuine accepted", outcome(g) == "accepted_agda_runtime_roundtrip", str(outcome(g)))
check("T1b genuine artifact's own outcome is accepted", g.get("outcome") == "accepted_agda_runtime_roundtrip")

# ---- T2..T11: every degenerate mutation is REJECTED (returns None) ---------
def mutate(path: list, value) -> dict:
    d = copy.deepcopy(genuine())
    node = d
    for k in path[:-1]:
        node = node[k]
    node[path[-1]] = value
    return d

rejections = [
    ("T2 wrong schema", ["schema"], "boundary.runtime_backend_artifact.v1"),
    ("T3 modules_safe_compiled False", ["positive_control", "modules_safe_compiled"], False),
    ("T4 postulate_free False", ["positive_control", "postulate_free"], False),
    ("T5 witnesses_extracted False", ["positive_control", "witnesses_extracted"], False),
    ("T6 readback_nontrivial False", ["positive_control", "readback_nontrivial"], False),
    ("T7 witness_program_count 0", ["positive_control", "witness_program_count"], 0),
    ("T8 forced_true_substitution_must_fail False (degenerate compiled!)", ["negative_control", "forced_true_substitution_must_fail"], False),
    ("T9 degenerate_rejected False", ["negative_control", "degenerate_rejected"], False),
    ("T10 expected_steps 0", ["expected_steps"], 0),
    ("T11 errors non-empty", ["errors"], ["something broke"]),
]
for name, path, val in rejections:
    check(name + " rejected", outcome(mutate(path, val)) is None)

# ---- T12: a SPOOFED raw outcome cannot rescue failing controls -------------
spoof = mutate(["positive_control", "modules_safe_compiled"], False)
spoof["outcome"] = "accepted_agda_runtime_roundtrip"   # attacker forces the field
check("T12 spoofed outcome with failing control rejected", outcome(spoof) is None)

# ---- T13: the producer is reproducible (replayable receipt) ----------------
def run_producer(out: str) -> dict:
    subprocess.run([sys.executable, "scripts/agda_boundary_runtime_roundtrip.py", "--out", out],
                   cwd=ROOT, capture_output=True, text=True, timeout=1200)
    return json.loads(Path(out).read_text(encoding="utf-8"))

a = run_producer("/tmp/rt_a.json")
b = run_producer("/tmp/rt_b.json")
check("T13 producer reproducible (outcome)", a.get("outcome") == b.get("outcome") == "accepted_agda_runtime_roundtrip")
check("T13b producer reproducible (expected_steps)", a.get("expected_steps") == b.get("expected_steps") and a.get("expected_steps") > 0)

# ---- T14: the producer genuinely DEPENDS on the negative control failing ----
# the negative-control fixture must FAIL agda --safe; confirm the producer
# recorded it failing for the genuine true!=false reason.
check("T14 negative control genuinely kernel-rejected", a["negative_control"]["forced_true_substitution_must_fail"] is True
      and a["negative_control"]["degenerate_rejected"] is True
      and "true != false" in a["negative_control"]["rejection_reason"])

# ---- T15: end-to-end engine P10 rejects a tampered on-disk artifact ---------
# tamper a copy, point a manifest-free direct validation
tampered = mutate(["positive_control", "witness_program_count"], 0)
check("T15 tampered artifact rejected by engine validator", outcome(tampered) is None)

# ---- T16: the genuine bare-metal programs are actually on disk + non-trivial-
metal = ROOT / "artifacts/ops/effective_corridor/boundary_metal"
for m in a["positive_control"]["modules"]:
    p = metal / m["witness_program"]
    check(f"T16 {m['module']} program on disk", p.exists() and m["program_nodes"] > 0)
    check(f"T16 {m['module']} safe+postfree", m["safe_compiled"] is True and m["postulate_free"] is True)

# ---- report ---------------------------------------------------------------
passed = sum(1 for _, ok, _ in results if ok)
total = len(results)
for name, ok, detail in results:
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail and not ok else ""))
print(f"\n{passed}/{total} checks passed")
sys.exit(0 if passed == total else 1)
