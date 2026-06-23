{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE OFF-DIAGONAL BOUND — for a square A = B⋆B (B symmetric):  (Aᵢⱼ)² ≤ Aᵢᵢ·Aⱼⱼ, every dimension.
--
-- This is the entry-wise control that drives LOCATEDNESS of the spectral-radius cut: if every diagonal
-- entry of A = M^{2^L} is ≤ q^{2^L}, then so is every off-diagonal entry (in absolute value), hence
-- ‖A‖₁ ≤ n²·q^{2^L}.  The bound is NOT a new Cauchy–Schwarz: writing rowᵢ := (k ↦ Bᵢₖ), symmetry gives
--      Aᵢⱼ = (B⋆B)ᵢⱼ = Σₖ BᵢₖBₖⱼ = Σₖ BᵢₖBⱼₖ = ⟨rowᵢ, rowⱼ⟩,
-- so (Aᵢⱼ)² = ⟨rowᵢ,rowⱼ⟩² ≤ ⟨rowᵢ,rowᵢ⟩⟨rowⱼ,rowⱼ⟩ = Aᵢᵢ·Aⱼⱼ is exactly the landed CauchySchwarz on
-- the rows of B.  No PSD-form Cauchy–Schwarz, no eigenvalues.
--
module corpus.cubical_agda.Corridor.Running.General.OffDiagBound where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin; zero)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫)
open import corpus.cubical_agda.Corridor.Running.General.CauchySchwarz using (cauchy-schwarz)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ)
open Sum (CommRing→Ring ℚCommRing) using (∑Ext)

-- the i-th row of B as a column vector.
rowVec : {n : ℕ} → Mat n n → Fin n → Mat n 1
rowVec B i = λ k _ → B i k

-- (B⋆B)ₚᵩ = ⟨rowₚ, rowᵩ⟩  (using symmetry to turn Bₖᵩ into Bᵩₖ).
prodEntry : {n : ℕ} (B : Mat n n) → (B ᵀ ≡ B) → (p r : Fin n)
          → (B ⋆ B) p r ≡ ⟪ rowVec B p , rowVec B r ⟫
prodEntry B symB p r = ∑Ext (λ k → cong (B p k ·_) (λ t → symB (~ t) k r))

-- (Aᵢⱼ)² ≤ Aᵢᵢ·Aⱼⱼ  for A = B⋆B, B symmetric.
offdiag-sq : {n : ℕ} (B : Mat n n) → (B ᵀ ≡ B) → (i j : Fin n)
           → ((B ⋆ B) i j · (B ⋆ B) i j) ≤ ((B ⋆ B) i i · (B ⋆ B) j j)
offdiag-sq B symB i j =
  subst2 _≤_
    (cong₂ _·_ (sym (prodEntry B symB i j)) (sym (prodEntry B symB i j)))
    (cong₂ _·_ (sym (prodEntry B symB i i)) (sym (prodEntry B symB j j)))
    (cauchy-schwarz (rowVec B i) (rowVec B j))
