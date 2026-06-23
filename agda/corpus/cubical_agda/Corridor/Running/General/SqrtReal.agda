{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE CONSTRUCTIVE SQUARE ROOT AS A LOCATED DEDEKIND REAL — sqrtReal x : ℝ for any 0 ≤ x : ℚ.
--
-- √x is the Dedekind cut L = {q | q<0 ∨ q²<x}, U = {q | q>0 ∧ q²>x}.  We ROUND it (L q := ∃q'>q,
-- Lcore q') so the four open/closed cut laws are automatic; the remaining laws are elementary, and
-- LOCATEDNESS is fully DECIDABLE — the comparison q²<x is decided by ℚ's trichotomy (<Dec), no
-- bisection or convergence needed.  This is the foundation under both the quadratic-irrational
-- corridors (√D) and the certified spectral edges (√Δ).  Same packaging as SpecRadiusReal, but the
-- located core needs no analysis at all.
--
module corpus.cubical_agda.Corridor.Running.General.SqrtReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isTrans<; isTrans≤; isTrans<≤; isTrans≤<; isAsym<; ≮→≥; <Weaken≤; ≤-·o; ≤-+o; <Dec)
open import corpus.cubical_agda.RealCohesion.DedekindReal
  using (ℝ; Pred; ⟦_⟧; IsCut; dense; 0<1ℚ; x<x+1; neg1<0; x-1<x)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (sq-mono)

module _ (x : ℚ) (0≤x : 0 ≤ x) where

  Lcore Ucore : ℚ → Type₀
  Lcore q = (q < 0) ⊎ ((q · q) < x)
  Ucore q = (0 < q) × (x < (q · q))

  Lp Up : Pred
  Lp q = (∥ Σ[ q' ∈ ℚ ] (q < q') × Lcore q' ∥₁) , squash₁
  Up q = (∥ Σ[ q' ∈ ℚ ] (q' < q) × Ucore q' ∥₁) , squash₁

  -- the decidable located core:  a < b ⟹ a is a (raw) lower bound or b a (raw) upper bound.
  coreLoc : (a b : ℚ) → 0 ≤ a → a < b → Lcore a ⊎ Ucore b
  coreLoc a b 0≤a a<b with <Dec (a · a) x
  ... | yes a²<x = inl (inr a²<x)
  ... | no ¬a²<x = inr (0<b , x<b²)
    where
      0<b : 0 < b
      0<b = isTrans≤< 0 a b 0≤a a<b
      x<b² : x < (b · b)
      x<b² = isTrans≤< x (a · a) (b · b) (≮→≥ (a · a) x ¬a²<x) (sq-mono a b 0≤a a<b)

  sqrtReal : ℝ
  sqrtReal = Lp , Up ,
    (Linhab , Uinhab , Lopen , Uopen , Ldown , Uup , disj , loc)
    where
      0≤x+1 : 0 ≤ (x + 1)
      0≤x+1 = isTrans≤ 0 x (x + 1) 0≤x (<Weaken≤ x (x + 1) (x<x+1 x))
      1≤x+1 : 1 ≤ (x + 1)
      1≤x+1 = subst (_≤ (x + 1)) (+IdL 1) (≤-+o 0 x 1 0≤x)
      x<x+1·x+1 : x < ((x + 1) · (x + 1))
      x<x+1·x+1 = isTrans<≤ x (x + 1) ((x + 1) · (x + 1)) (x<x+1 x)
                    (subst (_≤ ((x + 1) · (x + 1))) (·IdL (x + 1))
                      (≤-·o 1 (x + 1) (x + 1) 0≤x+1 1≤x+1))

      Linhab : ∥ Σ[ q ∈ ℚ ] ⟦ Lp ⟧ q ∥₁
      Linhab = ∣ ((- 1) - 1) , ∣ (- 1) , x-1<x (- 1) , inl neg1<0 ∣₁ ∣₁

      Uinhab : ∥ Σ[ q ∈ ℚ ] ⟦ Up ⟧ q ∥₁
      Uinhab = ∣ ((x + 1) + 1)
              , ∣ (x + 1) , x<x+1 (x + 1)
                , (isTrans≤< 0 x (x + 1) 0≤x (x<x+1 x) , x<x+1·x+1) ∣₁ ∣₁

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
          (λ { (q'' , q''<q , (0<q'' , x<q''²)) →
            contra q' q<q' lc q'' q''<q 0<q'' x<q''² }) uq }) lq
        where
          contra : (q' : ℚ) → q < q' → Lcore q' → (q'' : ℚ) → q'' < q → 0 < q''
                 → x < (q'' · q'') → ⊥
          contra q' q<q' (inl q'<0) q'' q''<q 0<q'' _ =
            isAsym< 0 q'' 0<q'' (isTrans< q'' q' 0 (isTrans< q'' q q' q''<q q<q') q'<0)
          contra q' q<q' (inr q'²<x) q'' q''<q 0<q'' x<q''² =
            isAsym< (q'' · q'') x
              (isTrans< (q'' · q'') (q' · q') x
                (sq-mono q'' q' (<Weaken≤ 0 q'' 0<q'') (isTrans< q'' q q' q''<q q<q')) q'²<x)
              x<q''²

      loc : (q r : ℚ) → q < r → ∥ ⟦ Lp ⟧ q ⊎ ⟦ Up ⟧ r ∥₁
      loc q r q<r with <Dec q 0
      ... | yes q<0 =
        let (c , q<c , c<0) = dense q 0 q<0
        in ∣ inl ∣ c , q<c , inl c<0 ∣₁ ∣₁
      ... | no ¬q<0 = decide (dense q r q<r)
        where
          0≤q : 0 ≤ q
          0≤q = ≮→≥ q 0 ¬q<0
          decide : Σ[ m1 ∈ ℚ ] (q < m1) × (m1 < r) → ∥ ⟦ Lp ⟧ q ⊎ ⟦ Up ⟧ r ∥₁
          decide (m1 , q<m1 , m1<r) = decide2 (dense m1 r m1<r)
            where
              0≤m1 : 0 ≤ m1
              0≤m1 = <Weaken≤ 0 m1 (isTrans≤< 0 q m1 0≤q q<m1)
              decide2 : Σ[ m2 ∈ ℚ ] (m1 < m2) × (m2 < r) → ∥ ⟦ Lp ⟧ q ⊎ ⟦ Up ⟧ r ∥₁
              decide2 (m2 , m1<m2 , m2<r) with coreLoc m1 m2 0≤m1 m1<m2
              ... | inl lc = ∣ inl ∣ m1 , q<m1 , lc ∣₁ ∣₁
              ... | inr uc = ∣ inr ∣ m2 , m2<r , uc ∣₁ ∣₁
