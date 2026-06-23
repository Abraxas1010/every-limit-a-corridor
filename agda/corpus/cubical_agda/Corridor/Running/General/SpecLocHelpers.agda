{-# OPTIONS --cubical --safe --guardedness #-}
--
-- HELPERS FOR THE LOCATED CORE — 1 ≤ n² (n ≥ 1) and the level-lift of the geometric beat.
--
-- The located core decides the cut at a level where M^{2^L} is a SQUARE (so the off-diagonal bound
-- applies), i.e. at suc L.  beat-suc lifts a beat n²·a^{2^L} < b^{2^L} to n²·a^{2^{L+1}} < b^{2^{L+1}}
-- (square it; n² ≤ (n²)² since 1 ≤ n²).  1≤nSq supplies 1 ≤ n² for a nonempty matrix.
--
module corpus.cubical_agda.Corridor.Running.General.SpecLocHelpers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fz)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Tactics.CommRingSolver using (solve!)

module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  sqScaleR : (s x : ⟨ R ⟩) → ((s · x) · (s · x)) ≡ ((s · s) · (x · x))
  sqScaleR s x = solve! R

open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_; isTrans≤; isTrans≤<; <Weaken≤; ≤-·o)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (sq-mono; 0≤sq-all)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (0<1ℚ)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (sum-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.QuadLemmas using (term-le-sum)
open import corpus.cubical_agda.Corridor.Running.General.QpowMono using (0≤qpow')
open import corpus.cubical_agda.Corridor.Running.General.OneNormDiagBound using (nSq)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (qpow)

open Sum (CommRing→Ring ℚCommRing) using (∑)

-- 1 ≤ n²  for a nonempty matrix (n = suc m).
1≤nSq : (m : ℕ) → 1 ≤ nSq (suc m)
1≤nSq m =
  isTrans≤ 1 (∑ {suc m} (λ (j : Fin (suc m)) → 1))
             (nSq (suc m))
    (term-le-sum (suc m) (λ (j : Fin (suc m)) → 1) fz (λ j → <Weaken≤ 0 1 0<1ℚ))
    (term-le-sum (suc m) (λ (i : Fin (suc m)) → ∑ {suc m} (λ (j : Fin (suc m)) → 1)) fz
      (λ i → sum-nonneg (suc m) (λ (j : Fin (suc m)) → 1) (λ j → <Weaken≤ 0 1 0<1ℚ)))

-- lift the geometric beat one squaring:  s·a^{2^L} < b^{2^L}  ⟹  s·a^{2^{L+1}} < b^{2^{L+1}}.
beat-suc : (s a b : ℚ) → 1 ≤ s → 0 ≤ a → (L : ℕ)
         → (s · qpow L a) < qpow L b → (s · qpow (suc L) a) < qpow (suc L) b
beat-suc s a b 1≤s 0≤a L h =
  isTrans≤< (s · qpow (suc L) a) ((s · s) · qpow (suc L) a) (qpow (suc L) b)
    (≤-·o s (s · s) (qpow (suc L) a) (0≤qpow' (suc L) a 0≤a) s≤ss)
    (subst (_< (qpow L b · qpow L b)) (sqScaleR ℚCommRing s (qpow L a))
      (sq-mono (s · qpow L a) (qpow L b)
        (0≤·s 0≤a) h))
  where
    0≤s : 0 ≤ s
    0≤s = isTrans≤ 0 1 s (<Weaken≤ 0 1 0<1ℚ) 1≤s
    s≤ss : s ≤ (s · s)
    s≤ss = subst (_≤ (s · s)) (·IdL s) (≤-·o 1 s s 0≤s 1≤s)
    0≤·s : 0 ≤ a → 0 ≤ (s · qpow L a)
    0≤·s 0≤a' = subst (_≤ (s · qpow L a)) (·AnnihilL (qpow L a))
                  (≤-·o 0 s (qpow L a) (0≤qpow' L a 0≤a') (isTrans≤ 0 1 s (<Weaken≤ 0 1 0<1ℚ) 1≤s))
