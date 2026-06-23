{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SPECTRAL-RADIUS CUT IS DISJOINT — no rational is both a lower and an upper bound, every dim.
--
-- Define ‖M‖ for symmetric M directly by the cut on rationals
--      lowAt L q := Σᵢ  q^{2^L} < (M^{2^L})ᵢᵢ       (some diagonal entry of M^{2^L} exceeds q^{2^L}),
--      uppAt L q :=      ‖M^{2^L}‖₁ < q^{2^L}.
-- Both conditions PERSIST under squaring (low-persist via diag-sq, upp-persist via oneNorm-submult),
-- so a lower witness at L₁ and an upper witness at L₂ both lift to the common level L₁+L₂, where
--      q^{2^{L₁+L₂}} < (M^{2^{L₁+L₂}})ᵢᵢ ≤ ‖M^{2^{L₁+L₂}}‖₁ < q^{2^{L₁+L₂}}     (entry≤oneNorm)
-- is a contradiction.  No spectral theory, no operator inequality, no matrix square root.
--
module corpus.cubical_agda.Corridor.Running.General.SpecCutDisjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; +-comm) renaming (_+_ to _+ℕ_)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_; isTrans<; isTrans<≤; isTrans≤<; isIrrefl<)
open import Cubical.Data.Empty using (⊥)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (sq-mono; 0≤sq-all; 0≤absℚ; absℚ)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (sum-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (pow2; qpow; pow2-sym)
open import corpus.cubical_agda.Corridor.Running.General.PowerMonotone using (diag-sq; entry≤oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.OneNormSubmult using (oneNorm-submult)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ)
open Sum (CommRing→Ring ℚCommRing) using (∑)

module _ {n : ℕ} (M : Mat n n) (symM : M ᵀ ≡ M) where

  -- the level predicates.
  lowAt : ℕ → ℚ → Type
  lowAt L q = Σ[ i ∈ Fin n ] (qpow L q < (pow2 L M) i i)

  uppAt : ℕ → ℚ → Type
  uppAt L q = oneNorm (pow2 L M) < qpow L q

  -- 0 ≤ q^{2^L}.
  0≤qpow : (q : ℚ) → 0 ≤ q → (L : ℕ) → 0 ≤ qpow L q
  0≤qpow q 0≤q zero    = 0≤q
  0≤qpow q 0≤q (suc L) = 0≤sq-all (qpow L q)

  -- 0 ≤ ‖A‖₁.
  0≤oneNorm : (A : Mat n n) → 0 ≤ oneNorm A
  0≤oneNorm A = sum-nonneg n (λ i → ∑ (λ j → absℚ (A i j)))
                  (λ i → sum-nonneg n (λ j → absℚ (A i j)) (λ j → 0≤absℚ (A i j)))

  -- PERSISTENCE: each condition survives one squaring.
  low-persist : (q : ℚ) → 0 ≤ q → (L : ℕ) → lowAt L q → lowAt (suc L) q
  low-persist q 0≤q L (i , q<d) = i ,
    isTrans<≤ (qpow (suc L) q) ((pow2 L M) i i · (pow2 L M) i i) ((pow2 (suc L) M) i i)
      (sq-mono (qpow L q) ((pow2 L M) i i) (0≤qpow q 0≤q L) q<d)
      (diag-sq (pow2 L M) (pow2-sym M symM L) i)

  upp-persist : (q : ℚ) → (L : ℕ) → uppAt L q → uppAt (suc L) q
  upp-persist q L ‖‖<q =
    isTrans≤< (oneNorm (pow2 (suc L) M)) (oneNorm (pow2 L M) · oneNorm (pow2 L M)) (qpow (suc L) q)
      (oneNorm-submult (pow2 L M) (pow2 L M))
      (sq-mono (oneNorm (pow2 L M)) (qpow L q) (0≤oneNorm (pow2 L M)) ‖‖<q)

  -- LIFT to a higher level (induction on the offset Δ; Δ+L = suc^Δ L definitionally).
  low-lift : (q : ℚ) → 0 ≤ q → (Δ L : ℕ) → lowAt L q → lowAt (Δ +ℕ L) q
  low-lift q 0≤q zero    L p = p
  low-lift q 0≤q (suc Δ) L p = low-persist q 0≤q (Δ +ℕ L) (low-lift q 0≤q Δ L p)

  upp-lift : (q : ℚ) → (Δ L : ℕ) → uppAt L q → uppAt (Δ +ℕ L) q
  upp-lift q zero    L p = p
  upp-lift q (suc Δ) L p = upp-persist q (Δ +ℕ L) (upp-lift q Δ L p)

  -- DISJOINTNESS: no q is both a lower and an upper bound.
  disjoint : (q : ℚ) → 0 ≤ q → (Σ[ L ∈ ℕ ] lowAt L q) → (Σ[ L ∈ ℕ ] uppAt L q) → ⊥
  disjoint q 0≤q (L₁ , lo) (L₂ , up) = isIrrefl< (qpow (L₁ +ℕ L₂) q) absurd
    where
      lo' : lowAt (L₁ +ℕ L₂) q
      lo' = subst (λ m → lowAt m q) (+-comm L₂ L₁) (low-lift q 0≤q L₂ L₁ lo)
      up' : uppAt (L₁ +ℕ L₂) q
      up' = upp-lift q L₁ L₂ up
      -- q^{2^{L₁+L₂}} < (M^{2^{L₁+L₂}})ᵢᵢ ≤ ‖M^{2^{L₁+L₂}}‖₁ < q^{2^{L₁+L₂}}.
      absurd : qpow (L₁ +ℕ L₂) q < qpow (L₁ +ℕ L₂) q
      absurd = isTrans< (qpow (L₁ +ℕ L₂) q) ((pow2 (L₁ +ℕ L₂) M) (fst lo') (fst lo'))
                         (qpow (L₁ +ℕ L₂) q)
                 (snd lo')
                 (isTrans≤< ((pow2 (L₁ +ℕ L₂) M) (fst lo') (fst lo'))
                            (oneNorm (pow2 (L₁ +ℕ L₂) M)) (qpow (L₁ +ℕ L₂) q)
                   (entry≤oneNorm (pow2 (L₁ +ℕ L₂) M) (fst lo')) up')
