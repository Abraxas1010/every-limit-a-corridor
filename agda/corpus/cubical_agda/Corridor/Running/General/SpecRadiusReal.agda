{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SPECTRAL RADIUS AS A DEDEKIND REAL — specRadius M : ℝ, for symmetric M, every dimension.
--
-- The capstone of the "spectrum has a modulus" route.  ρ(M) = ‖M‖ is packaged as a located Dedekind
-- real on ℚ.  The raw cut is L = {q | q below ρ}, U = {q | q above ρ}, witnessed by the running
-- power conditions q^{2^L} < (M^{2^L})ᵢᵢ and ‖M^{2^L}‖₁ < q^{2^L}.  We ROUND it
--      L q := ∃ q' > q, Lcore q' ;   U q := ∃ q' < q, Ucore q',
-- which makes the open/closed cut laws automatic.  Inhabitation is explicit; disjointness is
-- SpecCutDisjoint + qpow-mono; locatedness is dense + the located core (SpecLocated.coreLoc).  Every
-- ingredient is elementary finite-sum algebra + the Archimedean property — NO spectral theory.
--
module corpus.cubical_agda.Corridor.Running.General.SpecRadiusReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥; isProp⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isTrans<; isTrans<≤; isTrans≤<; isAsym<; ≮→≥; <Weaken≤; <Dec)
open import corpus.cubical_agda.RealCohesion.DedekindReal
  using (ℝ; Pred; ⟦_⟧; IsCut; dense; 0<1ℚ; x<x+1; neg1<0; x-1<x)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.QpowMono using (qpow-mono)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (pow2; qpow)
open import corpus.cubical_agda.Corridor.Running.General.SpecCutDisjoint using (0≤oneNorm; disjoint)
open import corpus.cubical_agda.Corridor.Running.General.SpecLocated using (LowRaw; UppRaw; coreLoc)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ)

module _ {n' : ℕ} (M : Mat (suc n') (suc n')) (symM : M ᵀ ≡ M) where

  Lcore Ucore : ℚ → Type₀
  Lcore q = (q < 0) ⊎ LowRaw M symM q
  Ucore q = (0 < q) × UppRaw M symM q

  Lp Up : Pred
  Lp q = (∥ Σ[ q' ∈ ℚ ] (q < q') × Lcore q' ∥₁) , squash₁
  Up q = (∥ Σ[ q' ∈ ℚ ] (q' < q) × Ucore q' ∥₁) , squash₁

  specRadius : ℝ
  specRadius = Lp , Up ,
    (Linhab , Uinhab , Lopen , Uopen , Ldown , Uup , disj , loc)
    where
      Linhab : ∥ Σ[ q ∈ ℚ ] ⟦ Lp ⟧ q ∥₁
      Linhab = ∣ ((- 1) - 1) , ∣ (- 1) , x-1<x (- 1) , inl neg1<0 ∣₁ ∣₁

      Uinhab : ∥ Σ[ q ∈ ℚ ] ⟦ Up ⟧ q ∥₁
      Uinhab = ∣ ((oneNorm M + 1) + 1)
              , ∣ (oneNorm M + 1) , x<x+1 (oneNorm M + 1)
                , (isTrans≤< 0 (oneNorm M) (oneNorm M + 1) (0≤oneNorm M symM M) (x<x+1 (oneNorm M)))
                  , (0 , x<x+1 (oneNorm M)) ∣₁ ∣₁

      Lopen : (q : ℚ) → ⟦ Lp ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ Lp ⟧ r ∥₁
      Lopen q = PT.map (λ { (q' , q<q' , lc) →
        let (c , q<c , c<q') = dense q q' q<q'
        in c , q<c , ∣ q' , c<q' , lc ∣₁ })

      Uopen : (q : ℚ) → ⟦ Up ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ Up ⟧ r ∥₁
      Uopen q = PT.map (λ { (q' , q'<q , uc) →
        let (c , q'<c , c<q) = dense q' q q'<q
        in c , c<q , ∣ q' , q'<c , uc ∣₁ })

      Ldown : (q r : ℚ) → q < r → ⟦ Lp ⟧ r → ⟦ Lp ⟧ q
      Ldown q r q<r = PT.map (λ { (q' , r<q' , lc) → q' , isTrans< q r q' q<r r<q' , lc })

      Uup : (q r : ℚ) → q < r → ⟦ Up ⟧ q → ⟦ Up ⟧ r
      Uup q r q<r = PT.map (λ { (q' , q'<q , uc) → q' , isTrans< q' q r q'<q q<r , uc })

      disj : (q : ℚ) → ⟦ Lp ⟧ q → ⟦ Up ⟧ q → ⊥
      disj q lq uq = PT.rec isProp⊥
        (λ { (q' , q<q' , lc) → PT.rec isProp⊥
          (λ { (q'' , q''<q , (0<q'' , ur)) →
            contra q' q<q' lc q'' q''<q 0<q'' ur }) uq }) lq
        where
          contra : (q' : ℚ) → q < q' → Lcore q' → (q'' : ℚ) → q'' < q → 0 < q''
                 → UppRaw M symM q'' → ⊥
          contra q' q<q' (inl q'<0) q'' q''<q 0<q'' ur =
            isAsym< 0 q'' 0<q'' (isTrans< q'' q' 0 (isTrans< q'' q q' q''<q q<q') q'<0)
          contra q' q<q' (inr lr) q'' q''<q 0<q'' (L2 , uA) =
            disjoint M symM q' (<Weaken≤ 0 q' (isTrans< 0 q'' q' 0<q'' q''<q')) lr
              (L2 , isTrans<≤ (oneNorm (pow2 L2 M)) (qpow L2 q'') (qpow L2 q') uA
                      (qpow-mono L2 q'' q' (<Weaken≤ 0 q'' 0<q'') (<Weaken≤ q'' q' q''<q')))
            where q''<q' = isTrans< q'' q q' q''<q q<q'

      loc : (q r : ℚ) → q < r → ∥ ⟦ Lp ⟧ q ⊎ ⟦ Up ⟧ r ∥₁
      loc q r q<r with <Dec q 0
      ... | yes q<0 =
        let (c , q<c , c<0) = dense q 0 q<0
        in ∣ inl ∣ c , q<c , inl c<0 ∣₁ ∣₁
      ... | no ¬q<0 =
        let 0≤q = ≮→≥ q 0 ¬q<0
            (m1 , q<m1 , m1<r) = dense q r q<r
            (m2 , m1<m2 , m2<r) = dense m1 r m1<r
            0<m1 = isTrans≤< 0 q m1 0≤q q<m1
        in PT.map (λ { (inl lr) → inl ∣ m1 , q<m1 , inr lr ∣₁
                     ; (inr (0<m2 , ur)) → inr ∣ m2 , m2<r , (0<m2 , ur) ∣₁ })
                  (coreLoc M symM m1 m2 0<m1 m1<m2)
