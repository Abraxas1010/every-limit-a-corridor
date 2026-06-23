{-# OPTIONS --cubical --safe --guardedness #-}
--
-- LEMMAS FOR THE QUADRATIC-FORM BOUND — term ≤ sum, and the AM–GM inequality.
--
-- The "spectrum has a modulus" upper bracket ⟨Ax,x⟩ ≤ ‖A‖₁·⟨x,x⟩ rests on bounding each term
-- Aᵢⱼxᵢxⱼ ≤ |Aᵢⱼ|·⟨x,x⟩, which needs (a) every coordinate square is ≤ the Gram form (a term is ≤
-- the sum of a nonnegative vector), and (b) the AM–GM inequality 2ab ≤ a²+b² (so |xᵢxⱼ| ≤ ⟨x,x⟩).
-- These are the two clean foundational lemmas; both are general-n / dimension-free.
--
module corpus.cubical_agda.Corridor.Running.General.QuadLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc; FinVec)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- (a−b)² = (a²+b²) − 2ab  over any commutative ring (placed before the ℚ open: `_-_` clash).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  amgmIdR : (a b : ⟨ R ⟩)
    → ((a - b) · (a - b)) ≡ (((a · a) + (b · b)) - ((a · b) + (a · b)))
  amgmIdR a b = solve! R

open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_≤_; _<_; isRefl≤; isTrans≤; ≤Monotone+; <-+o; ≮→≥; isIrrefl<; isTrans≤<)
open import Cubical.Relation.Nullary using (¬_)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all; sq-mono)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (sum-nonneg)

open Sum (CommRing→Ring ℚCommRing) using (∑)

-- 0 ≤ Y − X  ⟹  X ≤ Y.
private
  0≤sub→≤ : (X Y : ℚ) → 0 ≤ (Y - X) → X ≤ Y
  0≤sub→≤ X Y 0≤Y-X = subst2 _≤_ (+IdL X)
                        (sym (+Assoc Y (- X) X) ∙ cong (Y +_) (+InvL X) ∙ +IdR Y)
                        (≤Monotone+ 0 (Y - X) X X 0≤Y-X (isRefl≤ X))

-- a term of a nonnegative vector is ≤ its sum.
term-le-sum : (n : ℕ) (f : FinVec ℚ n) (i : Fin n) → ((k : Fin n) → 0 ≤ f k) → f i ≤ ∑ f
term-le-sum (suc n) f zero h =
  subst (_≤ (f zero + ∑ (λ k → f (suc k)))) (+IdR (f zero))
    (≤Monotone+ (f zero) (f zero) 0 (∑ (λ k → f (suc k)))
      (isRefl≤ (f zero)) (sum-nonneg n (λ k → f (suc k)) (λ k → h (suc k))))
term-le-sum (suc n) f (suc i) h =
  isTrans≤ (f (suc i)) (∑ (λ k → f (suc k))) (f zero + ∑ (λ k → f (suc k)))
    (term-le-sum n (λ k → f (suc k)) i (λ k → h (suc k)))
    (subst (_≤ (f zero + ∑ (λ k → f (suc k)))) (+IdL (∑ (λ k → f (suc k))))
      (≤Monotone+ 0 (f zero) (∑ (λ k → f (suc k))) (∑ (λ k → f (suc k)))
        (h zero) (isRefl≤ (∑ (λ k → f (suc k))))))

-- AM–GM:  2ab ≤ a² + b²   (from 0 ≤ (a−b)²).
amgm : (a b : ℚ) → ((a · b) + (a · b)) ≤ ((a · a) + (b · b))
amgm a b = 0≤sub→≤ ((a · b) + (a · b)) ((a · a) + (b · b))
             (subst (0 ≤_) (amgmIdR ℚCommRing a b) (0≤sq-all (a - b)))

-- squares reflect order on the nonnegatives:  a² ≤ b²  ⟹  a ≤ b.
sqrt-mono-≤ : (a b : ℚ) → 0 ≤ a → 0 ≤ b → (a · a) ≤ (b · b) → a ≤ b
sqrt-mono-≤ a b 0≤a 0≤b aa≤bb = ≮→≥ b a ¬b<a
  where ¬b<a : ¬ (b < a)
        ¬b<a b<a = isIrrefl< (a · a)
                     (isTrans≤< (a · a) (b · b) (a · a) aa≤bb (sq-mono b a 0≤b b<a))
