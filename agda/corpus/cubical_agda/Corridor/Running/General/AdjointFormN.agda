{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE ADJOINT BRIDGE FOR ALL n — ‖Mx‖² = ⟨M*M·x, x⟩ in every finite dimension.
--
-- AdjointForm proved the C*-axiom's pointwise bridge for n=2 by hand.  This module
-- proves it for ARBITRARY n×n matrices over any commutative ring, as clean matrix
-- algebra: writing the inner product ⟨u,v⟩ as the 1×1 matrix product uᵀ⋆v, the bridge
--      (M⋆x)ᵀ ⋆ (M⋆x)  ≡  xᵀ ⋆ ((Mᵀ⋆M) ⋆ x)
-- follows from transpose-of-product (M⋆x)ᵀ=xᵀ⋆Mᵀ (just ·Comm inside the sum, NO Fubini)
-- and associativity ⋆Assoc of the cubical Matrix library (whose own associativity proof
-- carries the finite-sum exchange ∑Exchange).  For symmetric M (Mᵀ≡M) this is
-- ‖Mx‖²=⟨M²x,x⟩ in EVERY dimension — the keystone of the constructive spectral theorem's
-- algebraic foundation (the one remaining piece being the operator-norm located
-- supremum over the unit sphere, genuinely deep constructive analysis).
--
module corpus.cubical_agda.Corridor.Running.General.AdjointFormN where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient

module Adjoint (𝓡 : CommRing ℓ-zero) where
  open Coefficient 𝓡
  open CommRingStr (snd 𝓡) using (·Comm)
  open Sum (CommRing→Ring 𝓡) using (∑Ext)

  -- transpose.
  _ᵀ : {m n : ℕ} → Mat m n → Mat n m
  (M ᵀ) i j = M j i

  -- transpose of a product:  (M⋆N)ᵀ ≡ Nᵀ⋆Mᵀ.  Pure commutativity inside the sum.
  ⋆ᵀ : {m n k : ℕ} (M : Mat m n) (N : Mat n k) → (M ⋆ N) ᵀ ≡ (N ᵀ) ⋆ (M ᵀ)
  ⋆ᵀ M N = funExt (λ i → funExt (λ j → ∑Ext (λ l → ·Comm (M j l) (N l i))))

  -- THE ADJOINT BRIDGE, any n: (M⋆x)ᵀ⋆(M⋆x) ≡ xᵀ⋆((Mᵀ⋆M)⋆x) = ⟨M*M·x, x⟩.
  adjointBridge : {n : ℕ} (M : Mat n n) (x : Mat n 1)
    → ((M ⋆ x) ᵀ) ⋆ (M ⋆ x) ≡ (x ᵀ) ⋆ (((M ᵀ) ⋆ M) ⋆ x)
  adjointBridge M x =
      cong (_⋆ (M ⋆ x)) (⋆ᵀ M x)
    ∙ sym (⋆Assoc (x ᵀ) (M ᵀ) (M ⋆ x))
    ∙ cong ((x ᵀ) ⋆_) (⋆Assoc (M ᵀ) M x)

  -- symmetric specialisation: Mᵀ≡M ⟹ ‖Mx‖² = ⟨M²x, x⟩ in every dimension.
  adjointBridgeSym : {n : ℕ} (M : Mat n n) (x : Mat n 1) → (M ᵀ ≡ M)
    → ((M ⋆ x) ᵀ) ⋆ (M ⋆ x) ≡ (x ᵀ) ⋆ ((M ⋆ M) ⋆ x)
  adjointBridgeSym M x symM =
    adjointBridge M x ∙ cong (λ A → (x ᵀ) ⋆ ((A ⋆ M) ⋆ x)) symM
