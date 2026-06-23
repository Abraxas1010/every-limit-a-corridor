{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SQUARE ROOT OF A LOCATED REAL — sqrtRealℝ x : ℝ for x : ℝ with a positive upper bound.
--
-- sqrtReal took a RATIONAL radicand and decided q²<x by ℚ trichotomy.  This lifts the radicand to a
-- located real: √x is the cut L = {q | q<0 ∨ q²∈L(x)}, U = {q | q>0 ∧ q²∈U(x)}, where "q²∈L(x)" means
-- q² lies in x's lower cut (i.e. q² < x as reals).  ROUNDED, so the open/closed laws are automatic;
-- disjointness is x's own disjointness at q²; and LOCATEDNESS comes FOR FREE from x's located law:
-- given q<r, x.located applied at (q², r²) decides q²∈L(x) ⊎ r²∈U(x) — no new analysis.  This is the
-- square root as an endofunction on the located reals, the missing piece for the general operator norm.
--
module corpus.cubical_agda.Corridor.Running.General.SqrtRealR where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isTrans<; isTrans<≤; isTrans≤<; isAsym<; ≮→≥; <Weaken≤)
open import corpus.cubical_agda.RealCohesion.DedekindReal
  using (ℝ; Pred; ⟦_⟧; IsCut; lowerCut; upperCut; dense; x<x+1; neg1<0; x-1<x)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (sq-mono)

-- a positive upper bound of x:  some 0 < b with x < b  (b in x's upper cut).
PosUpper : ℝ → Type₀
PosUpper x = Σ[ b ∈ ℚ ] (0 < b) × ⟦ upperCut x ⟧ b

module _ (x : ℝ) (pu : PosUpper x) where

  private
    Lx Ux : Pred
    Lx = lowerCut x
    Ux = upperCut x
    -- x's eight cut laws.
    cut : IsCut Lx Ux
    cut = snd (snd x)
    x-disj : (q : ℚ) → ⟦ Lx ⟧ q → ⟦ Ux ⟧ q → ⊥
    x-disj = fst (snd (snd (snd (snd (snd (snd cut))))))
    x-loc : (q r : ℚ) → q < r → ∥ ⟦ Lx ⟧ q ⊎ ⟦ Ux ⟧ r ∥₁
    x-loc = snd (snd (snd (snd (snd (snd (snd cut))))))
    x-up : (q r : ℚ) → q < r → ⟦ Ux ⟧ q → ⟦ Ux ⟧ r
    x-up = fst (snd (snd (snd (snd (snd cut)))))

  Lcore Ucore : ℚ → Type₀
  Lcore q = (q < 0) ⊎ ⟦ Lx ⟧ (q · q)
  Ucore q = (0 < q) × ⟦ Ux ⟧ (q · q)

  Lp Up : Pred
  Lp q = (∥ Σ[ q' ∈ ℚ ] (q < q') × Lcore q' ∥₁) , squash₁
  Up q = (∥ Σ[ q' ∈ ℚ ] (q' < q) × Ucore q' ∥₁) , squash₁

  -- the located core, FOR FREE from x's located law at the squares.
  coreLoc : (a b : ℚ) → 0 ≤ a → a < b → ∥ Lcore a ⊎ Ucore b ∥₁
  coreLoc a b 0≤a a<b = PT.map
    (λ { (inl a²∈L) → inl (inr a²∈L)
       ; (inr b²∈U) → inr (isTrans≤< 0 a b 0≤a a<b , b²∈U) })
    (x-loc (a · a) (b · b) (sq-mono a b 0≤a a<b))

  sqrtRealℝ : ℝ
  sqrtRealℝ = Lp , Up ,
    (Linhab , Uinhab , Lopen , Uopen , Ldown , Uup , disj , loc)
    where
      Linhab : ∥ Σ[ q ∈ ℚ ] ⟦ Lp ⟧ q ∥₁
      Linhab = ∣ ((- 1) - 1) , ∣ (- 1) , x-1<x (- 1) , inl neg1<0 ∣₁ ∣₁

      -- positive upper bound b ⟹ (b+1)² > b is above x, and b+1 > 0.
      Uinhab : ∥ Σ[ q ∈ ℚ ] ⟦ Up ⟧ q ∥₁
      Uinhab = ∣ ((b + 1) + 1)
              , ∣ (b + 1) , x<x+1 (b + 1)
                , (isTrans< 0 b (b + 1) 0<b (x<x+1 b)
                  , x-up b ((b + 1) · (b + 1)) b<sq b∈U) ∣₁ ∣₁
        where
          b = fst pu
          0<b = fst (snd pu)
          b∈U = snd (snd pu)
          -- b < (b+1)·(b+1):  b < b+1 ≤ (b+1)² (since 1 ≤ b+1, as 0<b).
          b<b+1 : b < (b + 1)
          b<b+1 = x<x+1 b
          b+1≤sq : (b + 1) ≤ ((b + 1) · (b + 1))
          b+1≤sq = subst (_≤ ((b + 1) · (b + 1))) (·IdL (b + 1))
                     (≤-·o 1 (b + 1) (b + 1)
                       (<Weaken≤ 0 (b + 1) (isTrans< 0 b (b + 1) 0<b b<b+1))
                       (subst (_≤ (b + 1)) (+IdL 1) (≤-+o 0 b 1 (<Weaken≤ 0 b 0<b))))
            where open import Cubical.Data.Rationals.Order using (≤-·o; ≤-+o)
          b<sq : b < ((b + 1) · (b + 1))
          b<sq = isTrans<≤ b (b + 1) ((b + 1) · (b + 1)) b<b+1 b+1≤sq

      Lopen : (q : ℚ) → ⟦ Lp ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ Lp ⟧ r ∥₁
      Lopen q = PT.map (λ { (q' , q<q' , lc) →
        let (c , q<c , c<q') = dense q q' q<q' in c , q<c , ∣ q' , c<q' , lc ∣₁ })

      Uopen : (q : ℚ) → ⟦ Up ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ Up ⟧ r ∥₁
      Uopen q = PT.map (λ { (q' , q'<q , uc) →
        let (c , q'<c , c<q) = dense q' q q'<q in c , c<q , ∣ q' , q'<c , uc ∣₁ })

      Ldown : (q r : ℚ) → q < r → ⟦ Lp ⟧ r → ⟦ Lp ⟧ q
      Ldown q r q<r = PT.map (λ { (q' , r<q' , lc) → q' , isTrans< q r q' q<r r<q' , lc })

      Uup : (q r : ℚ) → q < r → ⟦ Up ⟧ q → ⟦ Up ⟧ r
      Uup q r q<r = PT.map (λ { (q' , q'<q , uc) → q' , isTrans< q' q r q'<q q<r , uc })

      disj : (q : ℚ) → ⟦ Lp ⟧ q → ⟦ Up ⟧ q → ⊥
      disj q lq uq = PT.rec isProp⊥
        (λ { (q' , q<q' , lc) → PT.rec isProp⊥
          (λ { (q'' , q''<q , (0<q'' , q''²∈U)) →
            contra q' q<q' lc q'' q''<q 0<q'' q''²∈U }) uq }) lq
        where
          contra : (q' : ℚ) → q < q' → Lcore q' → (q'' : ℚ) → q'' < q → 0 < q''
                 → ⟦ Ux ⟧ (q'' · q'') → ⊥
          contra q' q<q' (inl q'<0) q'' q''<q 0<q'' _ =
            isAsym< 0 q'' 0<q'' (isTrans< q'' q' 0 (isTrans< q'' q q' q''<q q<q') q'<0)
          contra q' q<q' (inr q'²∈L) q'' q''<q 0<q'' q''²∈U =
            x-disj (q' · q') q'²∈L
              (x-up (q'' · q'') (q' · q')
                (sq-mono q'' q' (<Weaken≤ 0 q'' 0<q'') (isTrans< q'' q q' q''<q q<q')) q''²∈U)

      loc : (q r : ℚ) → q < r → ∥ ⟦ Lp ⟧ q ⊎ ⟦ Up ⟧ r ∥₁
      loc q r q<r with q-sign
        where
          q-sign : (q < 0) ⊎ (0 ≤ q)
          q-sign = lt-or-ge
            where open import Cubical.Data.Rationals.Order using (<Dec)
                  open import Cubical.Relation.Nullary using (yes; no)
                  lt-or-ge : (q < 0) ⊎ (0 ≤ q)
                  lt-or-ge with <Dec q 0
                  ... | yes p = inl p
                  ... | no ¬p = inr (≮→≥ q 0 ¬p)
      ... | inl q<0 =
        let (c , q<c , c<0) = dense q 0 q<0 in ∣ inl ∣ c , q<c , inl c<0 ∣₁ ∣₁
      ... | inr 0≤q = PT.map
        (λ { (inl lc) → inl ∣ m1 , q<m1 , lc ∣₁
           ; (inr uc) → inr ∣ m2 , m2<r , uc ∣₁ })
        (coreLoc m1 m2 0≤m1 m1<m2)
        where
          m1 = fst (dense q r q<r)
          q<m1 = fst (snd (dense q r q<r))
          m1<r = snd (snd (dense q r q<r))
          m2 = fst (dense m1 r m1<r)
          m1<m2 = fst (snd (dense m1 r m1<r))
          m2<r = snd (snd (dense m1 r m1<r))
          0≤m1 = <Weaken≤ 0 m1 (isTrans≤< 0 q m1 0≤q q<m1)
