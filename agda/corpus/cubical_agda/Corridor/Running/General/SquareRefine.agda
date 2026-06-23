{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SQUARING-REFINEMENT STEP — rayUp(A²)(s²) ⟹ rayUp A s, for PSD A, every dimension.
--
-- This is the iteration engine of the dyadic modulus: a cut bound on the SQUARE A² at the SQUARE s²
-- transfers to a (sharper) bound on A at s.  Composed with the C*-identity it gives the modulus —
-- bounding M^{2^L} at q^{2^L} bounds M at q, and the M^{2^L} bound (QuadBound) tightens with L.
-- Proof = Cauchy–Schwarz: for PSD A, ⟨Ax,x⟩ ≥ 0 and
--      ⟨Ax,x⟩²  ≤  ⟨Ax,Ax⟩·⟨x,x⟩  =  ⟨A²x,x⟩·⟨x,x⟩  <  s²⟨x,x⟩·⟨x,x⟩  =  (s⟨x,x⟩)²,
-- so ⟨Ax,x⟩ < s⟨x,x⟩ by the strict square-root monotonicity.  Uses the landed CauchySchwarz and the
-- adjoint bridge ⟨Ax,Ax⟩ = ⟨A²x,x⟩ (A symmetric).  No spectral theory.
--
module corpus.cubical_agda.Corridor.Running.General.SquareRefine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (zero)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- ((s·s)·c)·c ≡ (s·c)·(s·c)  over any commutative ring (before the ℚ open).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  sqUbR : (s c : ⟨ R ⟩) → (((s · s) · c) · c) ≡ ((s · c) · (s · c))
  sqUbR s c = solve! R

open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_≤_; _<_; isTrans≤<; isTrans<; isIrrefl<; <Weaken≤; ≤-·o; <-·o; _≟_; Trichotomy; lt; eq; gt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (sq-mono)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫)
open import corpus.cubical_agda.Corridor.Running.General.CauchySchwarz using (cauchy-schwarz)
open import corpus.cubical_agda.Corridor.Running.General.SpecBracket using (rayUp)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ; adjointBridge)
open Sum (CommRing→Ring ℚCommRing) using (∑Ext)

private
  0≤·0≤ : (a b : ℚ) → 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
  0≤·0≤ a b 0≤a 0≤b = subst (_≤ (a · b)) (·AnnihilL b) (≤-·o 0 a b 0≤b 0≤a)

-- strict square-root monotonicity:  a² < b²  ⟹  a < b  on the nonnegatives.
sqrt-mono-< : (a b : ℚ) → 0 ≤ a → 0 ≤ b → (a · a) < (b · b) → a < b
sqrt-mono-< a b 0≤a 0≤b aa<bb with a ≟ b
... | lt a<b = a<b
... | eq a≡b = ⊥-rec (isIrrefl< (a · a) (subst (λ z → (a · a) < (z · z)) (sym a≡b) aa<bb))
... | gt b<a = ⊥-rec (isIrrefl< (a · a) (isTrans< (a · a) (b · b) (a · a) aa<bb (sq-mono b a 0≤b b<a)))

-- inner-product symmetry.
⟪⟫-sym : {n : ℕ} (u v : Mat n 1) → ⟪ u , v ⟫ ≡ ⟪ v , u ⟫
⟪⟫-sym u v = ∑Ext (λ i → ·Comm (u i zero) (v i zero))

-- THE REFINEMENT STEP.
square-refine : {n : ℕ} (A : Mat n n) → (A ᵀ ≡ A) → ((y : Mat n 1) → 0 ≤ ⟪ y , A ⋆ y ⟫)
              → (s : ℚ) → 0 ≤ s → rayUp (A ⋆ A) (s · s) → rayUp A s
square-refine {n} A symA psd s 0≤s h x 0<xx =
  sqrt-mono-< (⟪ x , A ⋆ x ⟫) (s · ⟪ x , x ⟫) (psd x)
    (0≤·0≤ s ⟪ x , x ⟫ 0≤s (<Weaken≤ 0 ⟪ x , x ⟫ 0<xx)) sq<
  where
    adjEq : ⟪ A ⋆ x , A ⋆ x ⟫ ≡ ⟪ x , (A ⋆ A) ⋆ x ⟫
    adjEq = cong (λ K → K zero zero) (adjointBridge A x)
          ∙ cong (λ B → ⟪ x , (B ⋆ A) ⋆ x ⟫) symA
    csIneq : (⟪ x , A ⋆ x ⟫ · ⟪ x , A ⋆ x ⟫) ≤ (⟪ A ⋆ x , A ⋆ x ⟫ · ⟪ x , x ⟫)
    csIneq = subst (λ z → (z · z) ≤ (⟪ A ⋆ x , A ⋆ x ⟫ · ⟪ x , x ⟫))
               (sym (⟪⟫-sym x (A ⋆ x))) (cauchy-schwarz (A ⋆ x) x)
    step1 : ⟪ A ⋆ x , A ⋆ x ⟫ < ((s · s) · ⟪ x , x ⟫)
    step1 = subst (_< ((s · s) · ⟪ x , x ⟫)) (sym adjEq) (h x 0<xx)
    ub : (⟪ A ⋆ x , A ⋆ x ⟫ · ⟪ x , x ⟫) < ((s · ⟪ x , x ⟫) · (s · ⟪ x , x ⟫))
    ub = subst (λ z → (⟪ A ⋆ x , A ⋆ x ⟫ · ⟪ x , x ⟫) < z) (sqUbR ℚCommRing s ⟪ x , x ⟫)
           (<-·o (⟪ A ⋆ x , A ⋆ x ⟫) ((s · s) · ⟪ x , x ⟫) ⟪ x , x ⟫ 0<xx step1)
    sq< : (⟪ x , A ⋆ x ⟫ · ⟪ x , A ⋆ x ⟫) < ((s · ⟪ x , x ⟫) · (s · ⟪ x , x ⟫))
    sq< = isTrans≤< (⟪ x , A ⋆ x ⟫ · ⟪ x , A ⋆ x ⟫) (⟪ A ⋆ x , A ⋆ x ⟫ · ⟪ x , x ⟫)
            ((s · ⟪ x , x ⟫) · (s · ⟪ x , x ⟫)) csIneq ub
