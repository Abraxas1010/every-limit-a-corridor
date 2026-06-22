{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GRAM FORM IS POSITIVE DEFINITE — ⟨v,v⟩ ≥ 0, and ⟨v,v⟩ = 0 ⟹ v = 0.
--
-- The operator-norm cut framework (CStarRay) quantifies over x with 0 < ⟨x,x⟩, reading that as
-- "x ≠ 0".  This module justifies that reading: the inner product ⟨v,v⟩ = Σⱼ vⱼ² is a sum of
-- squares, hence ≥ 0 (positive SEMI-definite), and vanishes only at v = 0 (positive DEFINITE).
-- So for the matrix C*-algebra over ℚ, x ≠ 0 ⟺ 0 < ⟨x,x⟩ — the cuts are well-defined, in every
-- finite dimension.  Pure finite-sum induction (the ∑ cons form) + ℚ-order; no eigenvectors.
--
module corpus.cubical_agda.Corridor.Running.General.GramPosDef where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc; FinVec)
open import Cubical.Algebra.CommRing using (CommRing; CommRing→Ring; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)

-- (−x)·(−x) ≡ x·x  over any commutative ring (placed before the ℚ open to avoid the `-_` clash).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  negSqR : (x : ⟨ R ⟩) → ((- x) · (- x)) ≡ (x · x)
  negSqR x = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_≤_; _<_; isRefl≤; ≤Monotone+; isAntisym≤; <-·o; <-+o; ≤→≯; <Weaken≤; _≟_; Trichotomy; lt; eq; gt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Sum (CommRing→Ring ℚCommRing) using (∑)

-- transpose and the inner product ⟨u,v⟩ = (uᵀ⋆v)₀₀.
_ᵀ : {m n : ℕ} → Mat m n → Mat n m
(M ᵀ) i j = M j i

⟪_,_⟫ : {n : ℕ} → Mat n 1 → Mat n 1 → ℚ
⟪ u , v ⟫ = ((u ᵀ) ⋆ v) zero zero

private
  nn+nn : (a b : ℚ) → 0 ≤ a → 0 ≤ b → 0 ≤ (a + b)
  nn+nn a b 0≤a 0≤b = subst (_≤ (a + b)) (+IdL 0) (≤Monotone+ 0 a 0 b 0≤a 0≤b)
  split0a : (a b : ℚ) → (a + b) ≡ 0 → 0 ≤ a → 0 ≤ b → a ≡ 0
  split0a a b a+b≡0 0≤a 0≤b = isAntisym≤ a 0 a≤0 0≤a
    where a≤0 : a ≤ 0
          a≤0 = subst (a ≤_) a+b≡0
                  (subst (_≤ (a + b)) (+IdR a) (≤Monotone+ a a 0 b (isRefl≤ a) 0≤b))
  split0b : (a b : ℚ) → (a + b) ≡ 0 → 0 ≤ a → 0 ≤ b → b ≡ 0
  split0b a b a+b≡0 0≤a 0≤b = split0a b a (+Comm b a ∙ a+b≡0) 0≤b 0≤a
  -- sign helpers for vanish.
  <-asym : (m n : ℚ) → m < n → ¬ (n < m)
  <-asym m n m<n = ≤→≯ m n (<Weaken≤ m n m<n)
  0<·0< : (m n : ℚ) → 0 < m → 0 < n → 0 < (m · n)
  0<·0< m n 0<m 0<n = subst (_< (m · n)) (·AnnihilL n) (<-·o 0 m n 0<n 0<m)
  neg-pos : (z : ℚ) → z < 0 → 0 < (- z)
  neg-pos z z<0 = subst2 _<_ (+Comm z (- z) ∙ +InvL z) (+IdL (- z)) (<-+o z 0 (- z) z<0)
  negSq : (x : ℚ) → ((- x) · (- x)) ≡ (x · x)
  negSq = negSqR ℚCommRing

-- x·x ≡ 0 ⟹ x ≡ 0  (squares of nonzero rationals are strictly positive).
vanish : (x : ℚ) → (x · x) ≡ 0 → x ≡ 0
vanish x xx≡0 with x ≟ 0
... | eq x≡0 = x≡0
... | gt 0<x = ⊥-rec (<-asym 0 0 0<0 0<0)
  where 0<0 = subst (0 <_) xx≡0 (0<·0< x x 0<x 0<x)
... | lt x<0 = ⊥-rec (<-asym 0 0 0<0 0<0)
  where 0<0 = subst (0 <_) (negSq x ∙ xx≡0) (0<·0< (- x) (- x) (neg-pos x x<0) (neg-pos x x<0))

-- sum of a nonnegative vector is nonnegative.
sum-nonneg : (n : ℕ) (f : FinVec ℚ n) → ((j : Fin n) → 0 ≤ f j) → 0 ≤ ∑ f
sum-nonneg zero    f h = isRefl≤ 0
sum-nonneg (suc n) f h = nn+nn (f zero) (∑ (λ j → f (suc j)))
                           (h zero) (sum-nonneg n (λ j → f (suc j)) (λ j → h (suc j)))

-- sum of a nonnegative vector vanishes ⟹ every entry vanishes.
sum-zero : (n : ℕ) (f : FinVec ℚ n) → ((j : Fin n) → 0 ≤ f j) → ∑ f ≡ 0
         → (j : Fin n) → f j ≡ 0
sum-zero (suc n) f h sf≡0 zero =
  split0a (f zero) (∑ (λ j → f (suc j))) sf≡0 (h zero)
    (sum-nonneg n (λ j → f (suc j)) (λ j → h (suc j)))
sum-zero (suc n) f h sf≡0 (suc j) =
  sum-zero n (λ k → f (suc k)) (λ k → h (suc k))
    (split0b (f zero) (∑ (λ j → f (suc j))) sf≡0 (h zero)
      (sum-nonneg n (λ k → f (suc k)) (λ k → h (suc k)))) j

-- ── THE GRAM FORM IS POSITIVE DEFINITE ───────────────────────────────────────
gram-nonneg : {n : ℕ} (v : Mat n 1) → 0 ≤ ⟪ v , v ⟫
gram-nonneg {n} v = sum-nonneg n (λ j → v j zero · v j zero) (λ j → 0≤sq-all (v j zero))

gram-def : {n : ℕ} (v : Mat n 1) → ⟪ v , v ⟫ ≡ 0 → v ≡ (λ _ _ → 0)
gram-def {n} v vv≡0 = funExt (λ i → funExt (λ { zero →
  vanish (v i zero)
    (sum-zero n (λ j → v j zero · v j zero) (λ j → 0≤sq-all (v j zero)) vv≡0 i) }))
