#!/usr/bin/env python3
"""Oracle for Item D — three-substrate parity of the corridor bracket (Agda == Rust == Boundary).
Runs the realization lane; the gate is byte parity across the three substrates over the PM set
D∈{3,10,20}, with the Boundary readback the kernel reduction of canonicalize_reconstructs."""
import subprocess, sys, json
from pathlib import Path
HERE = Path(__file__).resolve().parents[2]
lane = HERE / "realization" / "agda_boundary_runtime_roundtrip.py"
rc = subprocess.run([sys.executable, str(lane)]).returncode
receipt = json.loads((HERE / "realization" / "corridor_boundary_lowering_receipt.json").read_text())
ok_parity = receipt["three_substrate_parity_all"]
ok_rust   = receipt["rust_self_assertion_suite_ok"]
ok_pm     = set([3,10,20]).issubset({r["rung_D"] for r in receipt["rows"] if r["three_substrate_parity"]})
print("three-substrate parity  Agda == Rust == Boundary :", "PASS" if ok_parity else "FAIL")
print("rust self-assertion suite                        :", "PASS" if ok_rust else "FAIL")
print("PM set D∈{3,10,20} all parity                    :", "PASS" if ok_pm else "FAIL")
print("ALL", "PASS" if (rc==0 and ok_parity and ok_rust and ok_pm) else "FAIL")
sys.exit(0 if (rc==0 and ok_parity and ok_rust and ok_pm) else 1)
