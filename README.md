# Every Limit a Corridor — Research Bundle

A self-contained, verifiable bundle for the paper **"Every Limit a Corridor: A
Constructive Engine for Effective Mathematics"** (Institute for Applied
Ontological Mathematics, June 2026).

The paper realizes Veselov's *spectrum-with-a-modulus* proposal — a point-free
ladder, a spectral corridor, and computability certificates — as one object in
**cohesive homotopy type theory**, measures it, and runs it on bare metal. This
bundle lets a professional **verify every claim from primitives** and **reuse** the
constructions.

## What is here

```
agda/            the genuine constructions, cubical Agda (--cubical --safe, no postulates)
  Foundations/FiniteCohesion.agda        faithful real-cohesion: shape != flat (Thm 3.1-3.2)
  Corridor/CrossingCorridor.agda         univalence that computes: the re-entry (Thm 4.1)
  Corridor/FaithfulModulus.agda          "the ladder is the rate": golden modulus (Thm 5.1-5.2)
  Corridor/GoldenAFColimit.agda          Z[phi] AF sequential colimit (Thm 6.1)
  Corridor/EntropyScreen.agda            H^1 logical-entropy screen (Thm 6.2)
  Corridor/FaithfulCorridor.agda         the two walls, unified
  Corridor/CompleteCorridor.agda         synthesis + cross-part identity (Thm 7.1)
  Corridor/negative_controls/            BadForcedTrueCollapse.agda  (kernel-REJECTED control)
  HottLane/                              supporting genuine univalence (primGlue ua, the crossing)
realization/     the bare-metal authority lane
  agda_boundary_runtime_roundtrip.py     producer: runs positive + negative controls, emits the artifact
  test_agda_runtime_roundtrip_authority.py   27 checks: genuine accepted, all degenerate/tampered REJECTED
  phase_a11_crossing_genuineness_oracle.py   compiles all 7 modules + checks discriminators + bare-metal
  agda_runtime_roundtrip.json            the executable-closure artifact (boundary.agda_runtime_roundtrip.v1)
  manifest.json                          registers the artifact as boundary_runtime authority
artifacts/
  boundary_metal/                        the 14 bare-metal Boundary programs ({decls, main} term trees)
  closure/                               the executable-with-receipt transition + fixed-point-stability receipt
paper/           paper.tex, paper.pdf, refs.bib, build.sh, figures/
```

## Dependencies

- **Agda 2.8.0** (`agda --version`).
- **The cubical Agda library** (`agda/cubical`), pin `d684d7d8`. The modules import
  `Cubical.*` (set-quotients, the circle, sequential colimits, `Bool`, `Nat`).
  Obtain it with `git clone https://github.com/agda/cubical` and check out the pin,
  then point Agda at it (see `verify.sh`).
- **Python 3** (for the realization lane).
- **pdflatex + bibtex** (only to rebuild the paper).

## Verify the mathematics (no trust required)

Every numbered theorem in the paper is the plain-mathematics image of one
kernel-checked declaration here. To re-check them:

```bash
./verify.sh /path/to/cubical          # compiles all 7 modules --safe; confirms the
                                       # negative control is kernel-REJECTED; runs the
                                       # authority test suite (27/27)
```

`verify.sh` does three independent things:

1. **Compile** each of the seven modules under `agda --cubical --safe --guardedness`
   with **no postulates** — the Agda kernel checks the proofs.
2. **The negative control**: confirms `BadForcedTrueCollapse.agda` is *rejected* by
   the kernel for the genuine reason (`true != false`) — a degenerate witness
   cannot manufacture the discriminator.
3. **The authority lane**: runs the producer (re-extracts the bare-metal programs,
   re-runs the positive and negative controls) and the 27-check test suite, which
   accepts the genuine artifact and rejects every degenerate / spoofed / tampered
   variant.

## Reuse

The seven modules are ordinary cubical-Agda modules: import them and build on the
two walls, the computing re-entry, the forced modulus, the colimit, or the screen.
The realization lane is a template for admitting any kernel-checked cubical-Agda
construction as executable closure authority, gated by a kernel-enforced negative
control.

## The paper

`paper/paper.pdf` (18 pages). Rebuild with `cd paper && ./build.sh`.

---
*The Institute for Applied Ontological Mathematics. Licensing: iaom.org/license.*
