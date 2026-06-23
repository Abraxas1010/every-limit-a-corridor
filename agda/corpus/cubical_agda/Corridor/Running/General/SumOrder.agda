{-# OPTIONS --cubical --safe --guardedness #-}
--
-- FINITE-SUM ORDER TOOLKIT — monotonicity and constant-bounding of ∑ over ℚ.
--
-- The "spectrum has a modulus" route needs the Gershgorin/Cauchy–Schwarz bound ⟨Ax,x⟩ ≤ R·⟨x,x⟩,
-- which rests on bounding a finite sum termwise.  These are the reusable order lemmas for ∑ (the
-- Ring big-operator), companions to GramPosDef.sum-nonneg, proved by Fin-induction on the ∑ cons
-- form (∑{suc n}f = f zero + ∑(f∘suc), the foldrFin definition):
--   ∑-mono     — termwise ≤ lifts to ∑ ≤ ∑;
--   ∑-≤-const  — every term ≤ c  ⟹  ∑ f ≤ ∑ (constant c) = "n·c".
--
module corpus.cubical_agda.Corridor.Running.General.SumOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc; FinVec)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; isRefl≤; ≤Monotone+; isTrans≤)

open Sum (CommRing→Ring ℚCommRing) using (∑)

-- termwise ≤ lifts to ∑.
∑-mono : (n : ℕ) (f g : FinVec ℚ n) → ((i : Fin n) → f i ≤ g i) → ∑ f ≤ ∑ g
∑-mono zero    f g h = isRefl≤ 0
∑-mono (suc n) f g h =
  ≤Monotone+ (f zero) (g zero) (∑ (λ i → f (suc i))) (∑ (λ i → g (suc i)))
    (h zero) (∑-mono n (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

-- the constant vector and its sum (= "n · c").
constVec : (n : ℕ) → ℚ → FinVec ℚ n
constVec n c = λ _ → c

-- every term ≤ c  ⟹  ∑ f ≤ ∑ (constant c).
∑-≤-const : (n : ℕ) (f : FinVec ℚ n) (c : ℚ) → ((i : Fin n) → f i ≤ c)
          → ∑ f ≤ ∑ (constVec n c)
∑-≤-const n f c h = ∑-mono n f (constVec n c) h

-- chaining: termwise ≤ g and ∑ g ≤ B gives ∑ f ≤ B.
∑-mono-≤ : (n : ℕ) (f g : FinVec ℚ n) (B : ℚ) → ((i : Fin n) → f i ≤ g i) → ∑ g ≤ B → ∑ f ≤ B
∑-mono-≤ n f g B h sg≤B = isTrans≤ (∑ f) (∑ g) B (∑-mono n f g h) sg≤B
