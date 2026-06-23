# The Corridor's Observables — Logical-Entropy Provenance (Item E)

**Conjecture:** `corridor_frontier_E_entropy_provenance_20260621`
**Modules:** `Corridor/Running/General/{EntropyRing, EntropyProvenance, CorridorObservables}.agda`
(`--safe`, postulate-free). **Oracle:** `tests/external_oracles/corridor_frontier_E_observables_20260623/`.

Every number-system object in the IAOM catalogue is characterised by four observables. For the
running golden corridor they are computed below; each is a kernel reduction, not a claim.

## The catalogue row — "the corridor"

| # | Observable | Value | Witness |
|---|------------|-------|---------|
| 1 | **Algebraic behaviour** | `x² = x + 1` (golden quadratic) | `GoldenCut.φ` located law |
| 2 | **Provenance cost** `μ(D)` | `= D` (Cassini ladder depth), strictly grows | `CorridorObservables.provenanceCost`, `provenance-grows` |
| 3 | **Logical entropy** | `½` | `EntropyProvenance.entropy2-half` |
| 4 | **Bare-metal node count** | *(pending Phase D — Boundary lowering)* | — |

## Logical entropy = the H¹ screen

The corridor's exactness mechanism is the alternating **Cassini sign** `(−1)ⁿ` — a balanced
two-symbol process `{+,−}` with masses `(½, ½)`. Ellerman's logical entropy `h(π) = 1 − Σ pᵢ²`
of that partition is

```
h = 1 − ((½)² + (½)²) = 1 − ½ = ½.
```

This is **exactly** the value of the organism's H¹ cohomological screen (`Corridor.EntropyScreen`):
the corridor's distinction-content equals the screen's. Proved as the kernel equality
`entropy2-half : logicalEntropy2 ½ ≡ ½`.

## The discriminating control (HC-E): entropy is object-dependent

Logical entropy is **not** a universal constant — it genuinely measures, taking distinct values on
distinct objects:

```
trivial partition (1,0)        h = 0
the corridor       (½,½)       h = ½     ← = H¹ screen
trisection engine  (⅓,⅓,⅓)    h = ⅔
```

`entropy-discriminates-objects` proves `0 < ½ < ⅔` in the kernel, and `entropy2-zero`/`entropy2-half`
already pin two distinct values. The symmetry `h(p) = h(1−p)` (`entropy2-sym`, a ring identity
instantiated to ℚ) confirms it is a genuine partition functional, not a label. The engine's currency
for the natural number `2` is the trisection contraction `(2/3)² = 4/9` (`GeometricVanish.pow49`); the
corridor's ½ is a different value on a different object, which is the point — the catalogue
distinguishes its rows.

## Status

Observables 1–3 are computed and kernel-checked; observable 4 (the bare-metal node count) is supplied
by **Phase D**, the Boundary lowering of the bracket, and recorded as the pending fourth column. The
`EntropyScreen`-match gate is met: the corridor's computed logical entropy equals the screen value `½`.
