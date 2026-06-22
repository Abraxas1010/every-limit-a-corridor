{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE C*-IDENTITY AT THE CUT LEVEL, FOR ALL n — ‖M²‖ = ‖M‖² via the adjoint bridge.
--
-- CStarLocated proved ‖M²‖=‖M‖² for 2×2 via the decidable Sylvester cut.  For GENERAL n there is
-- no closed-form cut, but the C*-identity AT THE CUT LEVEL needs neither determinants nor Sylvester:
-- both the cut of ‖M²‖ and the cut of ‖M‖² unfold to the SAME Rayleigh condition
--      ∀ x ≠ 0,  ⟨M²x,x⟩ < r²·⟨x,x⟩,
-- because ⟨M²x,x⟩ = ⟨Mx,Mx⟩ = ‖Mx‖²  (AdjointFormN.adjointBridgeSym, proved for every dimension).
-- So the two located reals ‖M²‖ and ‖M‖² have the SAME upper cut — they are EQUAL.  This is the
-- C*-identity in its purest form (‖M²‖=‖M‖² ⟺ M²=M*M), holding in every finite dimension, with no
-- eigenvectors, no √, no determinant theory, no trisect-n — only the adjoint matrix identity.
-- (The cut here is the Rayleigh cut; its decidability/locatedness is the separate Sylvester/LDLᵀ
-- concern, settled for 2×2 in SpecRadiusCut.)
--
module corpus.cubical_agda.Corridor.Running.General.CStarRay where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin; zero)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_)
open import Cubical.Algebra.CommRing using (CommRing)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ; adjointBridgeSym)

-- the inner product ⟨u,v⟩ as the single entry of the 1×1 matrix uᵀ⋆v.
⟪_,_⟫ : {n : ℕ} → Mat n 1 → Mat n 1 → ℚ
⟪ u , v ⟫ = ((u ᵀ) ⋆ v) zero zero

-- the cut of ‖M‖² at r²:  r > ‖M‖  ⟺  ‖Mx‖² < r²‖x‖² for all x ≠ 0.
normUp : {n : ℕ} → Mat n n → ℚ → Type
normUp M r = (x : Mat _ 1) → 0 < ⟪ x , x ⟫ → ⟪ M ⋆ x , M ⋆ x ⟫ < ((r · r) · ⟪ x , x ⟫)

-- the cut of ‖A‖ (A PSD) at q:  q > λmax(A)  ⟺  ⟨Ax,x⟩ < q⟨x,x⟩ for all x ≠ 0.
rayUp : {n : ℕ} → Mat n n → ℚ → Type
rayUp A q = (x : Mat _ 1) → 0 < ⟪ x , x ⟫ → ⟪ x , A ⋆ x ⟫ < (q · ⟪ x , x ⟫)

-- THE C*-IDENTITY, all n:  the cut of ‖M²‖ and the cut of ‖M‖² coincide (so ‖M²‖ = ‖M‖²).
cstar-ray : {n : ℕ} (M : Mat n n) → (M ᵀ ≡ M) → (r : ℚ)
          → (normUp M r → rayUp (M ⋆ M) (r · r))
          × (rayUp (M ⋆ M) (r · r) → normUp M r)
cstar-ray M symM r = (fwd , bwd)
  where
    adjEq : (x : Mat _ 1) → ⟪ M ⋆ x , M ⋆ x ⟫ ≡ ⟪ x , (M ⋆ M) ⋆ x ⟫
    adjEq x = cong (λ K → K zero zero) (adjointBridgeSym M x symM)
    fwd : normUp M r → rayUp (M ⋆ M) (r · r)
    fwd nu x 0<xx = subst (_< ((r · r) · ⟪ x , x ⟫)) (adjEq x) (nu x 0<xx)
    bwd : rayUp (M ⋆ M) (r · r) → normUp M r
    bwd ru x 0<xx = subst (_< ((r · r) · ⟪ x , x ⟫)) (sym (adjEq x)) (ru x 0<xx)
