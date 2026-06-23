{-# OPTIONS --cubical --safe --guardedness #-}
--
-- ℓ¹ SUBMULTIPLICATIVITY — ‖A·B‖₁ ≤ ‖A‖₁·‖B‖₁, every dimension (the UPPER-cut persistence).
--
-- ‖A‖₁ = Σᵢⱼ|Aᵢⱼ|.  With ‖A²‖₁ ≤ ‖A‖₁² the upper cut condition ‖M^{2^L}‖₁ < q^{2^L} persists to L+1
-- (‖M^{2^{L+1}}‖₁ ≤ ‖M^{2^L}‖₁² < (q^{2^L})² = q^{2^{L+1}}), so disjointness closes at a common level.
-- Proof:  |(A·B)ᵢⱼ| = |Σₖ Aᵢₖ Bₖⱼ| ≤ Σₖ|Aᵢₖ||Bₖⱼ|  (∑-triangle + abs-mult); summing over j and exchanging
-- the j,k order (∑Exchange) factors out the k-th row-sum of B, which is ≤ ‖B‖₁ (term-le-sum); summing
-- over i and factoring gives ‖A‖₁·‖B‖₁.  Pure finite-sum algebra, no eigenvalues.
--
module corpus.cubical_agda.Corridor.Running.General.OneNormSubmult where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; FinVec) renaming (zero to fz; suc to fsuc)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix using (∑Exchange)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; isRefl≤; isTrans≤; ≤Monotone+; ≤-·o)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (absℚ; 0≤absℚ; absℚ-of-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (sum-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.QuadLemmas using (term-le-sum)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.SumOrder using (∑-mono)
open import corpus.cubical_agda.Corridor.Running.General.AbsLemmas using (abs-mult; abs-triangle)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Sum (CommRing→Ring ℚCommRing) using (∑; ∑Ext; ∑Mulrdist; ∑Mulldist)

private
  absℚ0 : absℚ 0 ≡ 0
  absℚ0 = absℚ-of-nonneg (isRefl≤ 0)

  -- |Σ f| ≤ Σ |f|.
  ∑-triangle : (n : ℕ) (f : FinVec ℚ n) → absℚ (∑ f) ≤ ∑ (λ i → absℚ (f i))
  ∑-triangle zero    f = subst (_≤ 0) (sym absℚ0) (isRefl≤ 0)
  ∑-triangle (suc n) f =
    isTrans≤ (absℚ (f fz + ∑ (λ i → f (fsuc i))))
             (absℚ (f fz) + absℚ (∑ (λ i → f (fsuc i))))
             (absℚ (f fz) + ∑ (λ i → absℚ (f (fsuc i))))
      (abs-triangle (f fz) (∑ (λ i → f (fsuc i))))
      (≤Monotone+ (absℚ (f fz)) (absℚ (f fz))
                  (absℚ (∑ (λ i → f (fsuc i)))) (∑ (λ i → absℚ (f (fsuc i))))
        (isRefl≤ (absℚ (f fz))) (∑-triangle n (λ i → f (fsuc i))))

  rowAbs : {n : ℕ} → Mat n n → Fin n → ℚ
  rowAbs B k = ∑ (λ j → absℚ (B k j))

  rowAbs≤oneNorm : {n : ℕ} (B : Mat n n) (k : Fin n) → rowAbs B k ≤ oneNorm B
  rowAbs≤oneNorm {n} B k =
    term-le-sum n (λ k' → ∑ (λ j → absℚ (B k' j))) k
      (λ k' → sum-nonneg n (λ j → absℚ (B k' j)) (λ j → 0≤absℚ (B k' j)))

-- the per-row bound:  Σⱼ|(A·B)ᵢⱼ| ≤ (rowAbsᵢ A)·‖B‖₁.
private
  inner-bound : {n : ℕ} (A B : Mat n n) (i : Fin n)
              → ∑ (λ j → absℚ ((A ⋆ B) i j)) ≤ ((∑ (λ k → absℚ (A i k))) · oneNorm B)
  inner-bound {n} A B i =
    isTrans≤ (∑ (λ j → absℚ ((A ⋆ B) i j)))
             (∑ (λ k → absℚ (A i k) · oneNorm B))
             ((∑ (λ k → absℚ (A i k))) · oneNorm B)
      (isTrans≤ (∑ (λ j → absℚ ((A ⋆ B) i j)))
                (∑ (λ k → absℚ (A i k) · rowAbs B k))
                (∑ (λ k → absℚ (A i k) · oneNorm B))
        step-ab step-d)
      (sym (∑Mulldist (oneNorm B) (λ k → absℚ (A i k))) ◁)
    where
      _◁ : {x y : ℚ} → x ≡ y → x ≤ y
      _◁ {x} {y} p = subst (x ≤_) p (isRefl≤ x)
      -- (a),(b),(c): Σⱼ|(A·B)ᵢⱼ| ≤ Σₖ |Aᵢₖ|·(rowAbsₖ B).
      step-ab : ∑ (λ j → absℚ ((A ⋆ B) i j)) ≤ ∑ (λ k → absℚ (A i k) · rowAbs B k)
      step-ab = subst (∑ (λ j → absℚ ((A ⋆ B) i j)) ≤_) factored bounded
        where
          -- per-j termwise bound, then ∑-mono.
          perj : (j : Fin n) → absℚ ((A ⋆ B) i j) ≤ ∑ (λ k → absℚ (A i k) · absℚ (B k j))
          perj j = subst (absℚ ((A ⋆ B) i j) ≤_)
                     (∑Ext (λ k → abs-mult (A i k) (B k j)))
                     (∑-triangle n (λ k → A i k · B k j))
          bounded : ∑ (λ j → absℚ ((A ⋆ B) i j)) ≤ ∑ (λ j → ∑ (λ k → absℚ (A i k) · absℚ (B k j)))
          bounded = ∑-mono n (λ j → absℚ ((A ⋆ B) i j))
                            (λ j → ∑ (λ k → absℚ (A i k) · absℚ (B k j))) perj
          factored : ∑ (λ j → ∑ (λ k → absℚ (A i k) · absℚ (B k j)))
                   ≡ ∑ (λ k → absℚ (A i k) · rowAbs B k)
          factored = ∑Exchange (CommRing→Ring ℚCommRing) (λ j k → absℚ (A i k) · absℚ (B k j))
                   ∙ ∑Ext (λ k → sym (∑Mulrdist (absℚ (A i k)) (λ j → absℚ (B k j))))
      -- (d): replace rowAbsₖ B by ‖B‖₁.
      step-d : ∑ (λ k → absℚ (A i k) · rowAbs B k) ≤ ∑ (λ k → absℚ (A i k) · oneNorm B)
      step-d = ∑-mono n (λ k → absℚ (A i k) · rowAbs B k) (λ k → absℚ (A i k) · oneNorm B)
        (λ k → subst2 _≤_ (·Comm (rowAbs B k) (absℚ (A i k))) (·Comm (oneNorm B) (absℚ (A i k)))
                 (≤-·o (rowAbs B k) (oneNorm B) (absℚ (A i k)) (0≤absℚ (A i k)) (rowAbs≤oneNorm B k)))

-- ‖A·B‖₁ ≤ ‖A‖₁·‖B‖₁.
oneNorm-submult : {n : ℕ} (A B : Mat n n) → oneNorm (A ⋆ B) ≤ (oneNorm A · oneNorm B)
oneNorm-submult {n} A B =
  subst (oneNorm (A ⋆ B) ≤_) (sym (∑Mulldist (oneNorm B) (λ i → ∑ (λ k → absℚ (A i k)))))
    (∑-mono n (λ i → ∑ (λ j → absℚ ((A ⋆ B) i j)))
             (λ i → (∑ (λ k → absℚ (A i k))) · oneNorm B)
             (λ i → inner-bound A B i))
