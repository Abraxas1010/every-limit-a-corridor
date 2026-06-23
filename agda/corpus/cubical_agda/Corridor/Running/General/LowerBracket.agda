{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE LOWER BRACKET — the standard basis vector eᵢ realizes the diagonal entry as a Rayleigh value.
--
-- For the "spectrum has a modulus" route the spectral radius needs a computable LOWER bound to pair
-- with the ℓ¹ upper bound (QuadBound).  The diagonal does it: ⟨A·eᵢ, eᵢ⟩ = Aᵢᵢ and ⟨eᵢ,eᵢ⟩ = 1, so
-- the Rayleigh quotient at eᵢ equals Aᵢᵢ.  Hence maxᵢ Aᵢᵢ ≤ ρ(A): the largest diagonal entry is a
-- rational lower bound on the spectral radius, in every dimension.  Pure Kronecker-delta collapse
-- (∑Mulr1) + reflexivity of Fin equality; no eigenvectors.
--
module corpus.cubical_agda.Corridor.Running.General.LowerBracket where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc; _==_)
open import Cubical.Data.Bool using (Bool; true; if_then_else_)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum; module KroneckerDelta)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Sum (CommRing→Ring ℚCommRing) using (∑; ∑Ext; ∑Mulr1)
open KroneckerDelta (CommRing→Ring ℚCommRing) using (δ)

-- the i-th standard basis vector as a column.
eVec : {n : ℕ} → Fin n → Mat n 1
eVec i = λ k _ → δ k i

-- Fin equality is reflexive, so the diagonal delta is 1.
==refl : {n : ℕ} (i : Fin n) → (i == i) ≡ true
==refl zero    = refl
==refl (suc i) = ==refl i

δ-refl : {n : ℕ} (i : Fin n) → δ i i ≡ 1
δ-refl i = cong (λ b → if b then 1 else 0) (==refl i)

-- ⟨eᵢ,eᵢ⟩ = 1.
eNorm : {n : ℕ} (i : Fin n) → ⟪ eVec i , eVec i ⟫ ≡ 1
eNorm {n} i = ∑Mulr1 n (λ k → δ k i) i ∙ δ-refl i

-- ⟨A·eᵢ, eᵢ⟩ = Aᵢᵢ  (the Rayleigh value at eᵢ is the i-th diagonal entry).
eRayleigh : {n : ℕ} (A : Mat n n) (i : Fin n) → ⟪ eVec i , A ⋆ eVec i ⟫ ≡ A i i
eRayleigh {n} A i =
    ∑Ext (λ k → cong (δ k i ·_) (∑Mulr1 n (λ j → A k j) i))
  ∙ ∑Ext (λ k → ·Comm (δ k i) (A k i))
  ∙ ∑Mulr1 n (λ k → A k i) i
