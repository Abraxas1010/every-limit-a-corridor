{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE POWER SCAFFOLD — the upper cut with the dyadic modulus, every dimension.
--
-- pow2 L M = M^{2^L} by repeated squaring.  Each pow2 (suc L) M is a SQUARE (B⋆B), hence symmetric
-- and PSD, so the squaring-refinement (SquareRefine) applies at every level.  Chaining the refinement
-- down to L = 1 and finishing with the C*-identity (cstar-ray) gives
--      rayUp (M^{2^L}) (q^{2^L})  ⟹  normUp M q        (= ‖M‖ < q),
-- and with the ℓ¹ bracket (QuadBound, via SpecBracket) the COMPUTABLE upper cut with the modulus:
--      ‖M^{2^L}‖₁ < q^{2^L}       ⟹  normUp M q.
-- As L grows ‖M^{2^L}‖₁^{1/2^L} → ρ(M), so this captures every q > ρ(M).  No spectral theory.
--
module corpus.cubical_agda.Corridor.Running.General.PowerScaffold where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using () renaming (zero to fz)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; _<_)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫; gram-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.CStarRay using (normUp; cstar-ray)
open import corpus.cubical_agda.Corridor.Running.General.SquareRefine using (square-refine)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.SpecBracket using (rayUp; rayUp-oneNorm)

open import Cubical.Data.Sigma using (fst; snd)
open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ; ⋆ᵀ; adjointBridge)

-- repeated squaring:  pow2 L M = M^{2^L};   qpow L q = q^{2^L}.
pow2 : {n : ℕ} → ℕ → Mat n n → Mat n n
pow2 zero    M = M
pow2 (suc L) M = pow2 L M ⋆ pow2 L M

qpow : ℕ → ℚ → ℚ
qpow zero    q = q
qpow (suc L) q = qpow L q · qpow L q

-- powers of a symmetric matrix are symmetric.
pow2-sym : {n : ℕ} (M : Mat n n) → (M ᵀ ≡ M) → (L : ℕ) → (pow2 L M) ᵀ ≡ pow2 L M
pow2-sym M symM zero    = symM
pow2-sym M symM (suc L) =
    ⋆ᵀ (pow2 L M) (pow2 L M)
  ∙ cong₂ _⋆_ (pow2-sym M symM L) (pow2-sym M symM L)

-- pow2 (suc L) M = B⋆B is positive semidefinite:  ⟨x,(B⋆B)x⟩ = ⟨Bx,Bx⟩ ≥ 0.
pow2-psd : {n : ℕ} (M : Mat n n) → (M ᵀ ≡ M) → (L : ℕ) (x : Mat n 1)
         → 0 ≤ ⟪ x , (pow2 (suc L) M) ⋆ x ⟫
pow2-psd M symM L x = subst (0 ≤_) bridge (gram-nonneg ((pow2 L M) ⋆ x))
  where
    bridge : ⟪ (pow2 L M) ⋆ x , (pow2 L M) ⋆ x ⟫ ≡ ⟪ x , (pow2 (suc L) M) ⋆ x ⟫
    bridge = cong (λ K → K fz fz) (adjointBridge (pow2 L M) x)
           ∙ cong (λ C → ⟪ x , (C ⋆ pow2 L M) ⋆ x ⟫) (pow2-sym M symM L)

-- chaining the refinement down to the C*-identity:  rayUp(M^{2^{L+1}})(q^{2^{L+1}}) ⟹ ‖M‖ < q.
toNormUp : {n : ℕ} (M : Mat n n) → (M ᵀ ≡ M) → (q : ℚ) → (L : ℕ)
         → rayUp (pow2 (suc L) M) (qpow (suc L) q) → normUp M q
toNormUp M symM q zero    h = snd (cstar-ray M symM q) h
toNormUp M symM q (suc L) h = toNormUp M symM q L
  (square-refine (pow2 (suc L) M) (pow2-sym M symM (suc L)) (pow2-psd M symM L)
     (qpow (suc L) q) (0≤sq-all (qpow L q)) h)

-- THE UPPER CUT WITH THE DYADIC MODULUS:  ‖M^{2^{L+1}}‖₁ < q^{2^{L+1}} ⟹ ‖M‖ < q.
normUp-from-pow : {n : ℕ} (M : Mat n n) → (M ᵀ ≡ M) → (q : ℚ) → (L : ℕ)
                → oneNorm (pow2 (suc L) M) < qpow (suc L) q → normUp M q
normUp-from-pow M symM q L h =
  toNormUp M symM q L (rayUp-oneNorm (pow2 (suc L) M) (qpow (suc L) q) h)
