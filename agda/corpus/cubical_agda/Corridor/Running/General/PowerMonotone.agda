{-# OPTIONS --cubical --safe --guardedness #-}
--
-- POWER MONOTONICITY — the lower cut PERSISTS under squaring, and a diagonal entry is ≤ ‖·‖₁.
--
-- These are the two facts that make the spectral-radius cut DISJOINT without any spectral theory.
-- Defining ‖M‖ directly by the cut
--      L q := ∃ L i,  q^{2^L} < (M^{2^L})ᵢᵢ        (a diagonal entry of a power exceeds q^{2^L}),
--      U q := ∃ L,    ‖M^{2^L}‖₁ < q^{2^L},
-- disjointness L q × U q → ⊥ follows by pushing both witnesses to a common level (each persists) and
-- using (M^{2^L})ᵢᵢ ≤ ‖M^{2^L}‖₁.  The lower persistence rests on:
--   diag-sq      — for symmetric A,  (Aᵢᵢ)² ≤ (A⋆A)ᵢᵢ   (the i-th diagonal of A² dominates Aᵢᵢ²);
--   entry≤oneNorm — Aᵢᵢ ≤ ‖A‖₁   (a single entry is ≤ the ℓ¹ entry-sum).
-- Both are elementary finite-sum facts (term-le-sum), no eigenvalues.
--
module corpus.cubical_agda.Corridor.Running.General.PowerMonotone where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin; zero)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; isTrans≤)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (absℚ; 0≤absℚ; 0≤sq-all)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (sum-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.QuadLemmas using (term-le-sum)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm; val≤abs)

open import Cubical.Algebra.CommRing using (CommRingStr)
open Coefficient ℚCommRing using (Mat; _⋆_)
open Sum (CommRing→Ring ℚCommRing) using (∑; ∑Ext)

-- transpose, to state the symmetry hypothesis.
_ᵀ : {m n : ℕ} → Mat m n → Mat n m
(A ᵀ) i j = A j i

-- LOWER PERSISTENCE: for symmetric A, (Aᵢᵢ)² ≤ (A⋆A)ᵢᵢ.
diag-sq : {n : ℕ} (A : Mat n n) → (A ᵀ ≡ A) → (i : Fin n)
        → ((A i i) · (A i i)) ≤ ((A ⋆ A) i i)
diag-sq {n} A symA i = subst (((A i i) · (A i i)) ≤_) (sym toSum)
  (term-le-sum n (λ j → A i j · A i j) i (λ j → 0≤sq-all (A i j)))
  where
    -- (A⋆A)ᵢᵢ = Σⱼ Aᵢⱼ·Aⱼᵢ = Σⱼ Aᵢⱼ²  (symmetry).
    toSum : (A ⋆ A) i i ≡ ∑ (λ j → A i j · A i j)
    toSum = ∑Ext (λ j → cong (A i j ·_) (λ t → symA t i j))

-- DISJOINTNESS BOUND: a diagonal entry is ≤ the ℓ¹ entry-sum.
entry≤oneNorm : {n : ℕ} (A : Mat n n) (i : Fin n) → (A i i) ≤ oneNorm A
entry≤oneNorm {n} A i =
  isTrans≤ (A i i) (absℚ (A i i)) (oneNorm A)
    (val≤abs (A i i))
    (isTrans≤ (absℚ (A i i)) (∑ (λ j → absℚ (A i j))) (oneNorm A)
      (term-le-sum n (λ j → absℚ (A i j)) i (λ j → 0≤absℚ (A i j)))
      (term-le-sum n (λ k → ∑ (λ j → absℚ (A k j))) i
        (λ k → sum-nonneg n (λ j → absℚ (A k j)) (λ j → 0≤absℚ (A k j)))))
