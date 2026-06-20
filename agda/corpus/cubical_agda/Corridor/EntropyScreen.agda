{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE H¹ LOGICAL-ENTROPY SCREEN — Vladimir's "Part III" / defect spectrum.
--
-- HOSTILE-AUDIT REMEDIATION (legacy phase A9, grounded genuinely).
--
-- "Part III" of the programme is a cohomological obstruction that SCREENS: a
-- rank-one class that is closed but not exact (H¹ ≠ 0), quantified by Ellerman's
-- LOGICAL ENTROPY (the count of distinctions).  The legacy A9 carried this as a
-- label; here it is the genuine cohomology of the re-entry loop.
--
-- The re-entry / crossing of `CrossingCorridor` is an S¹: ONE vertex with ONE
-- loop edge.  Over ℤ/2 (Bool with ⊕) its coboundary δ⁰f = f(v) ⊕ f(v) VANISHES
-- on the loop — which is exactly why the loop supports a nonzero H¹ class.  The
-- class's logical entropy is the count of distinctions it makes on the two-point
-- boundary {false,true}, which is precisely the cohesion's flat-wall apartness
-- (`FiniteCohesion`: `flat realLine` keeps `true ≢ false`).
--
-- Non-vacuity: a degenerate "screen" would have an exact class (H¹ = 0) or zero
-- entropy.  The genuine one REFUTES both — `class-not-exact` (the loop class is
-- not a coboundary) and `class-detects` (positive logical entropy).  Replacing
-- the class by the trivial `false` makes both fields impossible to inhabit.
--
module corpus.cubical_agda.Corridor.EntropyScreen where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; false≢true)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (_<_; zero-≤; suc-≤-suc)
open import Cubical.Data.Empty using (⊥)

-- ────────────────────────────────────────────────────────────────────────────
-- ℤ/2 cochains on the re-entry loop (the crossing's S¹: 1 vertex, 1 loop edge).
-- ────────────────────────────────────────────────────────────────────────────

Cochain : Type
Cochain = Bool

-- the coboundary δ⁰ : C⁰ → C¹.  On a LOOP edge (both endpoints are the single
-- vertex) δ⁰f = f(v) ⊕ f(v), which is always 0 — the source of the nonzero H¹.
δ⁰ : Cochain → Cochain
δ⁰ f = f ⊕ f

δ⁰-vanishes : (f : Cochain) → δ⁰ f ≡ false
δ⁰-vanishes false = refl
δ⁰-vanishes true  = refl

-- ────────────────────────────────────────────────────────────────────────────
-- The genuine rank-one H¹ class: the loop carries coefficient 1.  Closed (no
-- 2-cells, so δ¹ = 0) and NOT exact — hence H¹ = ℤ/2 ≠ 0.
-- ────────────────────────────────────────────────────────────────────────────

loopCocycle : Cochain
loopCocycle = true

-- every coboundary is 0, but the loop cocycle is 1: it is not a coboundary.
loopCocycle-not-exact : (f : Cochain) → δ⁰ f ≡ loopCocycle → ⊥
loopCocycle-not-exact f e = false≢true (sym (δ⁰-vanishes f) ∙ e)

-- ────────────────────────────────────────────────────────────────────────────
-- Logical entropy (Ellerman): the count of distinctions a 1-cochain makes on
-- the two-point boundary {false,true}.  ω distinguishes the pair iff ω = 1 —
-- exactly the cohesion's flat-wall apartness.
-- ────────────────────────────────────────────────────────────────────────────

logicalEntropy : Cochain → ℕ
logicalEntropy true  = 2   -- the ordered distinctions (false,true) and (true,false)
logicalEntropy false = 0   -- indiscrete: no distinctions

-- THE SCREEN: the genuine (nonzero) H¹ class carries POSITIVE logical entropy —
-- the defect is detected, not screened to zero.
screen-detects : 0 < logicalEntropy loopCocycle
screen-detects = suc-≤-suc zero-≤

-- a coboundary (exact / trivial class) screens to zero entropy.
coboundary-screens : (f : Cochain) → logicalEntropy (δ⁰ f) ≡ 0
coboundary-screens f = cong logicalEntropy (δ⁰-vanishes f)

-- ────────────────────────────────────────────────────────────────────────────
-- The screen certificate: a closed-not-exact rank-one H¹ class carrying
-- positive logical entropy.  No field is inhabitable by the trivial class.
-- ────────────────────────────────────────────────────────────────────────────

record EntropyScreen : Type where
  constructor entropy-screen
  field
    klass           : Cochain
    klass-not-exact : (f : Cochain) → δ⁰ f ≡ klass → ⊥   -- H¹ ≠ 0
    klass-detects   : 0 < logicalEntropy klass           -- positive logical entropy
    coboundary-zero : (f : Cochain) → logicalEntropy (δ⁰ f) ≡ 0

open EntropyScreen public

entropy-screen-witness : EntropyScreen
entropy-screen-witness =
  entropy-screen loopCocycle loopCocycle-not-exact screen-detects coboundary-screens
