{-# OPTIONS --cubical --safe --guardedness #-}
--
-- GEOMETRIC GROWTH, ARCHIMEDEAN FORM — for t > 1, the power t^{2^L} exceeds every rational C.
--
-- qgrow combines the Bernoulli rate (GeomGrow: 1 + 2^L(t−1) ≤ t^{2^L}) with the project's multiplicative
-- Archimedean property (Archimedean.mult-arch: ∃k, D < ε·(k+1)) and the dyadic bound k+1 ≤ 2^L
-- (dyadic-ge) to conclude ∃L, C < t^{2^L}.  This is the growth that refutes "(r/q)^{2^L} ≤ n² for all
-- L", closing LOCATEDNESS of the spectral-radius cut.  No analysis — induction + the landed Archimedean.
--
module corpus.cubical_agda.Corridor.Running.General.GeomGrowArch where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; zero)
open import Cubical.Data.Sigma using (Σ-syntax; _,_)
open import Cubical.Data.Int using (ℤ; pos; sucℤ) renaming (·IdR to ·IdRℤ; _·_ to _·ℤ_)
open import Cubical.Data.NatPlusOne using (1+_; ℕ₊₁; ℕ₊₁→ℤ)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁) renaming (map to ∥map∥)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isRefl≤; isTrans≤; isTrans<≤; <Weaken≤; ≤Monotone+; ≤-·o; <-+o)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (qpow)
open import corpus.cubical_agda.Corridor.Running.General.GeomGrow using (dyadicℚ; 0<dyadicℚ; bern)
open import corpus.cubical_agda.Corridor.Running.General.Archimedean using (mult-arch)

private
  le-add : (z a : ℚ) → 0 ≤ a → z ≤ (z + a)
  le-add z a 0≤a = subst (_≤ (z + a)) (+IdR z) (≤Monotone+ z z 0 a (isRefl≤ z) 0≤a)
  -- (k+1 as ℚ) = (k as ℚ) + 1.
  add1 : (m : ℕ) → ([ pos m / 1+ 0 ] + [ pos 1 / 1+ 0 ]) ≡ [ pos (suc m) / 1+ 0 ]
  add1 m = cong (λ z → [ z / 1+ 0 ]) (cong sucℤ (·IdRℤ (pos m)))

-- 1 ≤ 2^k.
1≤dyadic : (k : ℕ) → 1 ≤ dyadicℚ k
1≤dyadic zero    = isRefl≤ 1
1≤dyadic (suc k) = isTrans≤ 1 (dyadicℚ k) (dyadicℚ k + dyadicℚ k)
                     (1≤dyadic k) (le-add (dyadicℚ k) (dyadicℚ k) (<Weaken≤ 0 (dyadicℚ k) (0<dyadicℚ k)))

-- k+1 ≤ 2^k  (as rationals).
dyadic-ge : (k : ℕ) → [ pos (suc k) / 1+ 0 ] ≤ dyadicℚ k
dyadic-ge zero    = isRefl≤ 1
dyadic-ge (suc k) = subst (_≤ (dyadicℚ k + dyadicℚ k)) (add1 (suc k))
  (≤Monotone+ [ pos (suc k) / 1+ 0 ] (dyadicℚ k) [ pos 1 / 1+ 0 ] (dyadicℚ k)
    (dyadic-ge k) (1≤dyadic k))

-- THE GROWTH:  t > 1  ⟹  ∃L, C < t^{2^L}.
qgrow : (t : ℚ) → 1 < t → (C : ℚ) → ∥ Σ[ L ∈ ℕ ] (C < qpow L t) ∥₁
qgrow t 1<t C = ∥map∥ use (mult-arch (C - 1) (t - 1) 0<t-1)
  where
    0<t-1 : 0 < (t - 1)
    0<t-1 = subst (_< (t - 1)) (+InvR 1) (<-+o 1 t (- 1) 1<t)
    1≤t : 1 ≤ t
    1≤t = <Weaken≤ 1 t 1<t
    use : Σ[ k ∈ ℕ ] ((C - 1) < ((t - 1) · [ pos (suc k) / 1+ 0 ])) → Σ[ L ∈ ℕ ] (C < qpow L t)
    use (k , h) = k , isTrans<≤ C (1 + (dyadicℚ k · (t - 1))) (qpow k t) C<bound (bern t 1≤t k)
      where
        -- (C−1) < (t−1)·(k+1) ≤ (t−1)·2^k = 2^k·(t−1)
        step : (C - 1) < (dyadicℚ k · (t - 1))
        step = subst ((C - 1) <_) (·Comm (t - 1) (dyadicℚ k))
                 (isTrans<≤ (C - 1) ((t - 1) · [ pos (suc k) / 1+ 0 ]) ((t - 1) · dyadicℚ k)
                   h
                   (subst2 _≤_ (·Comm [ pos (suc k) / 1+ 0 ] (t - 1)) (·Comm (dyadicℚ k) (t - 1))
                     (≤-·o [ pos (suc k) / 1+ 0 ] (dyadicℚ k) (t - 1)
                       (<Weaken≤ 0 (t - 1) 0<t-1) (dyadic-ge k))))
        C<bound : C < (1 + (dyadicℚ k · (t - 1)))
        C<bound = subst2 _<_
                    (sym (+Assoc C (- 1) 1) ∙ cong (C +_) (+InvL 1) ∙ +IdR C)
                    (+Comm (dyadicℚ k · (t - 1)) 1)
                    (<-+o (C - 1) (dyadicℚ k · (t - 1)) 1 step)
