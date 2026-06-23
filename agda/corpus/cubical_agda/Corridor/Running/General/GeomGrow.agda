{-# OPTIONS --cubical --safe --guardedness #-}
--
-- GEOMETRIC GROWTH — Bernoulli for the repeated-squaring power:  t^{2^L} ≥ 1 + 2^L·(t−1)  (t ≥ 1).
--
-- This is the rate that drives LOCATEDNESS: for t > 1 the right side grows linearly in 2^L, so by
-- the Archimedean property t^{2^L} = qpow L t exceeds every rational C (qgrow).  With t = r/q this
-- gives r^{2^L} > C·q^{2^L} eventually — exactly what refutes "(r/q)^{2^L} ≤ n² for all L".  The
-- dyadic 2^L (dyadicℚ) is the modulus.  Pure induction + ring solver, no analysis.
--
module corpus.cubical_agda.Corridor.Running.General.GeomGrow where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- ring identities for Bernoulli (before the ℚ open).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  bernBaseR : (t : ⟨ R ⟩) → (1r + (1r · (t - 1r))) ≡ t
  bernBaseR t = solve! R
  stepRingR : (d t : ⟨ R ⟩)
    → ((1r + (d · (t - 1r))) · (1r + (d · (t - 1r))))
      ≡ ((1r + ((d + d) · (t - 1r))) + ((d · (t - 1r)) · (d · (t - 1r))))
  stepRingR d t = solve! R

open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isRefl≤; isTrans≤; isTrans<≤; ≤Monotone+; ≤-·o; <-+o; <Weaken≤)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all; sq-mono-≤)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (0<1ℚ)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (qpow)

private
  0≤·0≤ : (a b : ℚ) → 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
  0≤·0≤ a b 0≤a 0≤b = subst (_≤ (a · b)) (·AnnihilL b) (≤-·o 0 a b 0≤b 0≤a)
  0≤sum : (a b : ℚ) → 0 ≤ a → 0 ≤ b → 0 ≤ (a + b)
  0≤sum a b 0≤a 0≤b = subst (_≤ (a + b)) (+IdL 0) (≤Monotone+ 0 a 0 b 0≤a 0≤b)
  le-add : (z a : ℚ) → 0 ≤ a → z ≤ (z + a)
  le-add z a 0≤a = subst (_≤ (z + a)) (+IdR z) (≤Monotone+ z z 0 a (isRefl≤ z) 0≤a)

-- 2^L as a rational.
dyadicℚ : ℕ → ℚ
dyadicℚ zero    = 1
dyadicℚ (suc L) = dyadicℚ L + dyadicℚ L

0<dyadicℚ : (L : ℕ) → 0 < dyadicℚ L
0<dyadicℚ zero    = 0<1ℚ
0<dyadicℚ (suc L) = isTrans<≤ 0 (dyadicℚ L) (dyadicℚ L + dyadicℚ L) (0<dyadicℚ L)
                      (le-add (dyadicℚ L) (dyadicℚ L) (<Weaken≤ 0 (dyadicℚ L) (0<dyadicℚ L)))

-- BERNOULLI:  for t ≥ 1,  1 + 2^L·(t−1) ≤ t^{2^L}.
bern : (t : ℚ) → 1 ≤ t → (L : ℕ) → (1 + (dyadicℚ L · (t - 1))) ≤ qpow L t
bern t 1≤t zero    = subst (_≤ t) (sym (bernBaseR ℚCommRing t)) (isRefl≤ t)
bern t 1≤t (suc L) =
  isTrans≤ (1 + (dyadicℚ (suc L) · (t - 1))) (b · b) (qpow L t · qpow L t)
    step≤
    (sq-mono-≤ b (qpow L t) 0≤b (bern t 1≤t L))
  where
    b : ℚ
    b = 1 + (dyadicℚ L · (t - 1))
    0≤t-1 : 0 ≤ (t - 1)
    0≤t-1 = subst (_≤ (t - 1)) (+InvR 1) (≤Monotone+ 1 t (- 1) (- 1) 1≤t (isRefl≤ (- 1)))
    0≤b : 0 ≤ b
    0≤b = 0≤sum 1 (dyadicℚ L · (t - 1)) (<Weaken≤ 0 1 0<1ℚ)
            (0≤·0≤ (dyadicℚ L) (t - 1) (<Weaken≤ 0 (dyadicℚ L) (0<dyadicℚ L)) 0≤t-1)
    step≤ : (1 + (dyadicℚ (suc L) · (t - 1))) ≤ (b · b)
    step≤ = subst ((1 + (dyadicℚ (suc L) · (t - 1))) ≤_)
              (sym (stepRingR ℚCommRing (dyadicℚ L) t))
              (le-add (1 + ((dyadicℚ L + dyadicℚ L) · (t - 1)))
                      ((dyadicℚ L · (t - 1)) · (dyadicℚ L · (t - 1)))
                      (0≤sq-all (dyadicℚ L · (t - 1))))
