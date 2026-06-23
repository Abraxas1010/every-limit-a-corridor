{-# OPTIONS --cubical --safe --guardedness #-}
--
-- ‖A‖₁ BOUNDED BY THE DIAGONAL — for A = B⋆B (B symmetric):  all Aᵢᵢ ≤ c  ⟹  ‖A‖₁ ≤ n²·c.
--
-- This is the locatedness lever: when the lower cut FAILS at level L (no diagonal entry of M^{2^L}
-- exceeds q^{2^L}, i.e. every Aᵢᵢ ≤ q^{2^L}), the off-diagonal bound forces every entry ≤ q^{2^L} in
-- absolute value, hence ‖A‖₁ ≤ n²·q^{2^L}.  Combined with the upper-cut failure r^{2^L} ≤ ‖A‖₁ this
-- gives (r/q)^{2^L} ≤ n² for all L — refuted by geometric growth.  Pure finite-sum, no eigenvalues.
--
module corpus.cubical_agda.Corridor.Running.General.OneNormDiagBound where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin; zero)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; isRefl≤; isTrans≤; ≤-·o)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (absℚ; absℚ-sq; 0≤absℚ)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫; gram-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.QuadLemmas using (sqrt-mono-≤)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.SumOrder using (∑-mono)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.OffDiagBound using (offdiag-sq; prodEntry; rowVec)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ)
open Sum (CommRing→Ring ℚCommRing) using (∑; ∑Ext; ∑Mulrdist)

oneℚ : ℚ
oneℚ = 1

-- n² as a rational:  Σᵢ Σⱼ 1.
nSq : (n : ℕ) → ℚ
nSq n = ∑ {n} (λ (_ : Fin n) → ∑ {n} (λ (_ : Fin n) → oneℚ))

private
  -- 0 ≤ a, a ≤ c, b ≤ c, 0 ≤ c  ⟹  a·b ≤ c·c.
  le-prod : (a b c : ℚ) → 0 ≤ a → 0 ≤ c → a ≤ c → b ≤ c → (a · b) ≤ (c · c)
  le-prod a b c 0≤a 0≤c a≤c b≤c =
    isTrans≤ (a · b) (a · c) (c · c)
      (subst2 _≤_ (·Comm b a) (·Comm c a) (≤-·o b c a 0≤a b≤c))
      (≤-·o a c c 0≤c a≤c)

module _ {n : ℕ} (B : Mat n n) (symB : B ᵀ ≡ B) where

  0≤diag : (i : Fin n) → 0 ≤ (B ⋆ B) i i
  0≤diag i = subst (0 ≤_) (sym (prodEntry B symB i i)) (gram-nonneg (rowVec B i))

  -- every entry of B⋆B is ≤ c in absolute value, given the diagonal bound.
  entry-bound : (c : ℚ) → 0 ≤ c → ((k : Fin n) → (B ⋆ B) k k ≤ c) → (i j : Fin n)
              → absℚ ((B ⋆ B) i j) ≤ c
  entry-bound c 0≤c diag≤ i j =
    sqrt-mono-≤ (absℚ ((B ⋆ B) i j)) c (0≤absℚ ((B ⋆ B) i j)) 0≤c
      (subst (_≤ (c · c)) (sym (absℚ-sq ((B ⋆ B) i j)))
        (isTrans≤ ((B ⋆ B) i j · (B ⋆ B) i j) ((B ⋆ B) i i · (B ⋆ B) j j) (c · c)
          (offdiag-sq B symB i j)
          (le-prod ((B ⋆ B) i i) ((B ⋆ B) j j) c (0≤diag i) 0≤c (diag≤ i) (diag≤ j))))

  -- ‖B⋆B‖₁ ≤ c·n².
  oneNorm-diag-bound : (c : ℚ) → 0 ≤ c → ((k : Fin n) → (B ⋆ B) k k ≤ c)
                     → oneNorm (B ⋆ B) ≤ (c · nSq n)
  oneNorm-diag-bound c 0≤c diag≤ =
    subst (oneNorm (B ⋆ B) ≤_) factor bounded
    where
      bounded : oneNorm (B ⋆ B) ≤ ∑ {n} (λ (i : Fin n) → ∑ {n} (λ (j : Fin n) → c))
      bounded = ∑-mono n (λ i → ∑ (λ j → absℚ ((B ⋆ B) i j))) (λ i → ∑ {n} (λ j → c))
        (λ i → ∑-mono n (λ j → absℚ ((B ⋆ B) i j)) (λ j → c)
                 (λ j → entry-bound c 0≤c diag≤ i j))
      innerFactor : ∑ {n} (λ (j : Fin n) → c) ≡ (c · ∑ {n} (λ (j : Fin n) → oneℚ))
      innerFactor = ∑Ext {n = n} {λ j → c} {λ j → c · 1} (λ j → sym (·IdR c))
                  ∙ sym (∑Mulrdist {n = n} c (λ (j : Fin n) → oneℚ))
      factor : ∑ {n} (λ (i : Fin n) → ∑ {n} (λ (j : Fin n) → c)) ≡ (c · nSq n)
      factor = ∑Ext {n = n} {λ i → ∑ {n} (λ j → c)} {λ i → c · ∑ {n} (λ j → oneℚ)} (λ i → innerFactor)
             ∙ sym (∑Mulrdist {n = n} c (λ (i : Fin n) → ∑ {n} (λ (j : Fin n) → oneℚ)))
