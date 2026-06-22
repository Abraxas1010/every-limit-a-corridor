{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GEOMETRIC WIDTH VANISHES — pow49 k · D → 0, the located-completion convergence.
--
-- This is the assembly the whole Archimedean + geometric-bound stack was built for:  trisect-n
-- brackets a Dedekind real with width (2/3)²ᵏ·D = (4/9)ᵏ·D = pow49 k · D, and THIS theorem says
-- that width drops below any ε.  Proof = pure wiring of three landed lemmas:
--   pow49-bound  : pow49 k ≤ 1/(k+1)            (geometric bound, ℚ level)
--   mult-arch    : ∃k, D < ε·(k+1)              (multiplicative Archimedean — the D factor)
--   <-·o + ℚ-cancelʳ : multiply through by 1/(k+1), cancel (k+1)·(1/(k+1)) = 1.
-- So pow49 k · D ≤ (1/(k+1))·D < ε.  No new mathematics — the convergence is now a theorem.
--
module corpus.cubical_agda.Corridor.Running.General.GeometricVanish where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; _·₊₁_)
open import Cubical.Data.Nat.Properties using (+-zero)
open import Cubical.Data.Int using (ℤ; pos) renaming (_·_ to _·ℤ_)
open import Cubical.Data.Int.Properties renaming (·IdL to ·IdLℤ; ·IdR to ·IdRℤ) using (·IdLℤ; ·IdRℤ)
open import Cubical.Data.Int.Order using (isRefl≤) renaming (_<_ to _<ℤ_)
open import Cubical.Data.Sigma using (Σ; _,_; Σ-syntax)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_; <-·o; ≤-·o; isTrans≤<)
open import Cubical.Data.Rationals.Properties using (·Comm; ·Assoc; ·IdR)
open import Cubical.HITs.SetQuotients using (eq/)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; map)
open import corpus.cubical_agda.Corridor.Running.General.GeometricBoundQ using (pow49; pow49-bound)
open import corpus.cubical_agda.Corridor.Running.General.Archimedean using (mult-arch)

-- 1/(k+1) > 0:  unfolds (ℚ-<) to pos 0 < pos 1.
0<recip : (k : ℕ) → 0 < [ pos 1 / 1+ k ]
0<recip k = isRefl≤

-- (k+1)·(1/(k+1)) = 1, by the cross-multiplication path (eq/): the product is
-- [pos(suc k)·pos1 / (1+0)·₊₁(1+k)] and (1+0)·₊₁(1+k) reduces to 1+(k+0), so the cross-
-- multiplication condition is pos(suc k) ≡ pos(suc (k+0)) — exactly +-zero.
recipCancel : (k : ℕ) → ([ pos (suc k) / 1+ 0 ] · [ pos 1 / 1+ k ]) ≡ [ pos 1 / 1+ 0 ]
recipCancel k = eq/ _ _
  ( cong (_·ℤ pos 1) (·IdRℤ (pos (suc k)))
  ∙ ·IdRℤ (pos (suc k))
  ∙ cong (λ n → pos (suc n)) (sym (+-zero k))
  ∙ sym (·IdLℤ (ℕ₊₁→ℤ ((1+ 0) ·₊₁ (1+ k)))) )

-- THE CONVERGENCE: the geometric width pow49 k · D drops below any ε.
pow49-vanish : (D : ℚ) → 0 ≤ D → (ε : ℚ) → 0 < ε
             → ∥ Σ[ k ∈ ℕ ] (pow49 k · D < ε) ∥₁
pow49-vanish D 0≤D ε 0<ε = map step (mult-arch D ε 0<ε)
  where
    step : Σ[ k ∈ ℕ ] (D < ε · [ pos (suc k) / 1+ 0 ])
         → Σ[ k ∈ ℕ ] (pow49 k · D < ε)
    step (k , D<ε·sk) =
      k , isTrans≤< (pow49 k · D) ([ pos 1 / 1+ k ] · D) ε bound1 strict
      where
        bound1 : (pow49 k · D) ≤ ([ pos 1 / 1+ k ] · D)
        bound1 = ≤-·o (pow49 k) [ pos 1 / 1+ k ] D 0≤D (pow49-bound k)
        -- multiply D < ε·(k+1) by 1/(k+1) > 0, then cancel on the right.
        m1 : (D · [ pos 1 / 1+ k ]) < ((ε · [ pos (suc k) / 1+ 0 ]) · [ pos 1 / 1+ k ])
        m1 = <-·o D (ε · [ pos (suc k) / 1+ 0 ]) [ pos 1 / 1+ k ] (0<recip k) D<ε·sk
        rhs≡ε : ((ε · [ pos (suc k) / 1+ 0 ]) · [ pos 1 / 1+ k ]) ≡ ε
        rhs≡ε = sym (·Assoc ε [ pos (suc k) / 1+ 0 ] [ pos 1 / 1+ k ])
              ∙ cong (ε ·_) (recipCancel k)
              ∙ ·IdR ε
        strict : ([ pos 1 / 1+ k ] · D) < ε
        strict = subst2 _<_ (·Comm D [ pos 1 / 1+ k ]) rhs≡ε m1
