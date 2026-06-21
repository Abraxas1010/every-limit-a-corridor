{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5 / D1: φ AS A LOCATED REAL.  The golden spectral value, presented as a
-- genuine Dedekind cut of ℚ:  L_φ = {q : q<0 ∨ q²<q+1},  U_φ = {q : 1<q ∧ q+1<q²}.
-- The LOCATED law -- the crux of "located spectrum" -- is exactly the quadratic
-- monotonicity (GoldenValue.quad-mono) plus ℚ-order decidability.  No postulates.

module corpus.cubical_agda.RealCohesion.GoldenCut where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥; isProp⊥; rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; _≥_; <Dec; <-o+; <-+o; <-·o; <-·o-cancel; <-o+-cancel
        ; ≤-+o; ≤-o+; ≤-·o; ≤Monotone+; isTrans<; isIrrefl<; isTrans<≤; isTrans≤<
        ; ≮→≥; <Weaken≤; isProp<)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁; ∣_∣₁; isPropPropTrunc)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; Pred; ⟦_⟧; dense)
open import corpus.cubical_agda.RealCohesion.GoldenValue using (quad-mono; quad-id)
open import corpus.cubical_agda.RealCohesion.RealApprox using (0<·d; -Dist)
open import corpus.cubical_agda.RealCohesion.RealNegation using (neg-flip)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _  = a
  getYes (no  _) ()

0<1ℚ : 0 < 1
0<1ℚ = getYes (<Dec 0 1) tt

-- φ's two cuts.
φL φU : Pred
φL q = ∥ (q < 0) ⊎ (q · q < q + 1) ∥₁ , isPropPropTrunc
φU q = ((1 < q) × ((q + 1) < (q · q)))
     , isProp× (isProp< 1 q) (isProp< (q + 1) (q · q))

-- 0≤q and q<1 ⟹ q²<q+1   (since q²≤q<q+1).
small-quad : (q : ℚ) → 0 ≤ q → q < 1 → (q · q) < (q + 1)
small-quad q 0≤q q<1 = isTrans≤< (q · q) q (q + 1) q²≤q q<q+1
  where
    q²≤q : (q · q) ≤ q
    q²≤q = subst ((q · q) ≤_) (·IdL q) (≤-·o q 1 q 0≤q (<Weaken≤ q 1 q<1))
    q<q+1 : q < (q + 1)
    q<q+1 = subst (_< (q + 1)) (+IdR q) (<-o+ 0 1 q 0<1ℚ)

-- (q²−q) < 1 ⟹ q² < q+1   (add q to both sides).
quad-sub→ : (q : ℚ) → ((q · q) + (- q)) < 1 → (q · q) < (q + 1)
quad-sub→ q h = subst2 _<_ lhs≡ (+Comm 1 q) (<-+o ((q · q) + (- q)) 1 q h)
  where
    lhs≡ : ((q · q) + (- q)) + q ≡ q · q
    lhs≡ = sym (+Assoc (q · q) (- q) q) ∙ cong ((q · q) +_) (+InvL q) ∙ +IdR (q · q)

-- THE LOCATED LAW: for q < r, either q is below φ or r is above φ.  The crux of
-- "located spectrum": φ is genuinely located, decided by the quadratic.
φ-located : (q r : ℚ) → q < r → ∥ ⟦ φL ⟧ q ⊎ ⟦ φU ⟧ r ∥₁
φ-located q r q<r with <Dec q 0
... | yes q<0 = ∣ inl ∣ inl q<0 ∣₁ ∣₁
... | no ¬q<0 with <Dec 1 r
...   | no ¬1<r = ∣ inl ∣ inr (small-quad q 0≤q q<1) ∣₁ ∣₁
        where 0≤q : 0 ≤ q
              0≤q = ≮→≥ q 0 ¬q<0
              q<1 : q < 1
              q<1 = isTrans<≤ q r 1 q<r (≮→≥ 1 r ¬1<r)
...   | yes 1<r with <Dec (r + 1) (r · r)
...     | yes r+1<r² = ∣ inr (1<r , r+1<r²) ∣₁
...     | no ¬r+1<r² = ∣ inl ∣ inr (quad-sub→ q q²−q<1) ∣₁ ∣₁
        where
          0≤q : 0 ≤ q
          0≤q = ≮→≥ q 0 ¬q<0
          r≤q+r : r ≤ (q + r)
          r≤q+r = subst (_≤ (q + r)) (+IdL r) (≤-+o 0 q r 0≤q)
          1<q+r : 1 < (q + r)
          1<q+r = isTrans<≤ 1 r (q + r) 1<r r≤q+r
          r²≤r+1 : (r · r) ≤ (r + 1)
          r²≤r+1 = ≮→≥ (r + 1) (r · r) ¬r+1<r²
          r²−r≤1 : ((r · r) + (- r)) ≤ 1
          r²−r≤1 = subst (((r · r) + (- r)) ≤_) shift1 (≤-+o (r · r) (r + 1) (- r) r²≤r+1)
            where shift1 : (r + 1) + (- r) ≡ 1
                  shift1 = cong (_+ (- r)) (+Comm r 1) ∙ sym (+Assoc 1 r (- r))
                         ∙ cong (1 +_) (+InvR r) ∙ +IdR 1
          q²−q<1 : ((q · q) + (- q)) < 1
          q²−q<1 = isTrans<≤ ((q · q) + (- q)) ((r · r) + (- r)) 1
                     (quad-mono q r 1<q+r q<r) r²−r≤1

-- ── reusable shift identities ──────────────────────────────────────────────
+1-shift : (x : ℚ) → (x + 1) + (- x) ≡ 1
+1-shift x = cong (_+ (- x)) (+Comm x 1) ∙ sym (+Assoc 1 x (- x))
           ∙ cong (1 +_) (+InvR x) ∙ +IdR 1
+neg-cancel : (a x : ℚ) → (a + (- x)) + x ≡ a
+neg-cancel a x = sym (+Assoc a (- x) x) ∙ cong (a +_) (+InvL x) ∙ +IdR a

-- 1 < (a − x) ⟹ x+1 < a   (the dual of quad-sub→).
add-r→ : (a x : ℚ) → 1 < (a + (- x)) → (x + 1) < a
add-r→ a x h = subst2 _<_ (+Comm 1 x) (+neg-cancel a x) (<-+o 1 (a + (- x)) x h)

-- ── the remaining seven cut laws (the eighth, located, is above) ───────────
φL-inhab : ∥ Σ[ q ∈ ℚ ] ⟦ φL ⟧ q ∥₁
φL-inhab = ∣ 0 , ∣ inr (getYes (<Dec (0 · 0) (0 + 1)) tt) ∣₁ ∣₁

φU-inhab : ∥ Σ[ q ∈ ℚ ] ⟦ φU ⟧ q ∥₁
φU-inhab = ∣ 2 , (getYes (<Dec 1 2) tt , getYes (<Dec (2 + 1) (2 · 2)) tt) ∣₁

φL-down : (q r : ℚ) → q < r → ⟦ φL ⟧ r → ⟦ φL ⟧ q
φL-down q r q<r = PT.rec isPropPropTrunc from-r
  where
    from-r : (r < 0) ⊎ (r · r < r + 1) → ⟦ φL ⟧ q
    from-r (inl r<0)    = ∣ inl (isTrans< q r 0 q<r r<0) ∣₁
    from-r (inr r²<r+1) with <Dec q 0
    ... | yes q<0 = ∣ inl q<0 ∣₁
    ... | no ¬q<0 with <Dec 1 r
    ...   | no ¬1<r = ∣ inr (small-quad q 0≤q (isTrans<≤ q r 1 q<r (≮→≥ 1 r ¬1<r))) ∣₁
            where 0≤q = ≮→≥ q 0 ¬q<0
    ...   | yes 1<r = ∣ inr (quad-sub→ q q²−q<1) ∣₁
            where
              0≤q = ≮→≥ q 0 ¬q<0
              1<q+r = isTrans<≤ 1 r (q + r) 1<r
                        (subst (_≤ (q + r)) (+IdL r) (≤-+o 0 q r 0≤q))
              r²−r<1 = subst (((r · r) + (- r)) <_) (+1-shift r)
                         (<-+o (r · r) (r + 1) (- r) r²<r+1)
              q²−q<1 = isTrans< ((q · q) + (- q)) ((r · r) + (- r)) 1
                         (quad-mono q r 1<q+r q<r) r²−r<1

φU-up : (q r : ℚ) → q < r → ⟦ φU ⟧ q → ⟦ φU ⟧ r
φU-up q r q<r (1<q , q+1<q²) = 1<r , r+1<r²
  where
    1<r : 1 < r
    1<r = isTrans< 1 q r 1<q q<r
    0<r : 0 < r
    0<r = isTrans< 0 1 r 0<1ℚ 1<r
    1<q+r : 1 < (q + r)
    1<q+r = isTrans<≤ 1 q (q + r) 1<q
              (subst (_≤ (q + r)) (+IdR q) (≤-o+ 0 r q (<Weaken≤ 0 r 0<r)))
    1<q²−q : 1 < ((q · q) + (- q))
    1<q²−q = subst (_< ((q · q) + (- q))) (+1-shift q) (<-+o (q + 1) (q · q) (- q) q+1<q²)
    r+1<r² : (r + 1) < (r · r)
    r+1<r² = add-r→ (r · r) r
               (isTrans< 1 ((q · q) + (- q)) ((r · r) + (- r)) 1<q²−q
                  (quad-mono q r 1<q+r q<r))

φ-disjoint : (q : ℚ) → ⟦ φL ⟧ q → ⟦ φU ⟧ q → ⊥
φ-disjoint q hL (1<q , q+1<q²) = PT.rec isProp⊥ from-L hL
  where
    from-L : (q < 0) ⊎ (q · q < q + 1) → ⊥
    from-L (inl q<0)    = isIrrefl< 0 (isTrans< 0 1 0 0<1ℚ (isTrans< 1 q 0 1<q q<0))
    from-L (inr q²<q+1) = isIrrefl< (q · q) (isTrans< (q · q) (q + 1) (q · q) q²<q+1 q+1<q²)

-- ── bound lemmas for the rounded laws ──────────────────────────────────────
0≤sq : (q : ℚ) → 0 ≤ q → 0 ≤ (q · q)
0≤sq q 0≤q = subst (_≤ (q · q)) (·AnnihilL q) (≤-·o 0 q q 0≤q 0≤q)

1<2ℚ : 1 < 2
1<2ℚ = getYes (<Dec 1 2) tt

-- q²<q+1 (with 0≤q) bounds q below 2.
q<2-lem : (q : ℚ) → 0 ≤ q → (q · q) < (q + 1) → q < 2
q<2-lem q 0≤q q²<q+1 with <Dec q 1
... | yes q<1 = isTrans< q 1 2 q<1 1<2ℚ
... | no ¬q<1 = <-·o-cancel q 2 q 0<q q·q<2·q
      where
        1≤q : 1 ≤ q
        1≤q = ≮→≥ q 1 ¬q<1
        0<q : 0 < q
        0<q = isTrans<≤ 0 1 q 0<1ℚ 1≤q
        q+1≤q+q : (q + 1) ≤ (q + q)
        q+1≤q+q = ≤-o+ 1 q q 1≤q
        q·q<q+q : (q · q) < (q + q)
        q·q<q+q = isTrans<≤ (q · q) (q + 1) (q + q) q²<q+1 q+1≤q+q
        q+q≡2·q : (q + q) ≡ 2 · q
        q+q≡2·q = sym (cong (_· q) (getYes (discreteℚ 2 (1 + 1)) tt)
                       ∙ ·DistR+ 1 1 q ∙ cong₂ _+_ (·IdL q) (·IdL q))
        q·q<2·q : (q · q) < (2 · q)
        q·q<2·q = subst ((q · q) <_) q+q≡2·q q·q<q+q

-- ── the ε-nudge: a rational strictly inside the cut, just above q ───────────
⅕ : ℚ
⅕ = [ pos 1 / 1+ 4 ]
0<⅕ : 0 < ⅕
0<⅕ = getYes (<Dec 0 ⅕) tt
0<2ℚ : 0 < 2
0<2ℚ = getYes (<Dec 0 2) tt

dbl : (q : ℚ) → q + q ≡ 2 · q
dbl q = sym (cong (_· q) (getYes (discreteℚ 2 (1 + 1)) tt)
             ∙ ·DistR+ 1 1 q ∙ cong₂ _+_ (·IdL q) (·IdL q))

-- for q with 0≤q and q²<q+1, the point r = q + δ/5 (δ = q+1−q²) still lies in
-- the cut: q < r and r² < r+1.  This is roundedness's witness.
nudge : (q : ℚ) → 0 ≤ q → (q · q) < (q + 1)
      → Σ[ r ∈ ℚ ] (q < r) × ((r · r) < (r + 1))
nudge q 0≤q q²<q+1 = r , q<r , r²<r+1
  where
    δ ε r : ℚ
    δ = (q + 1) + (- (q · q))
    ε = δ · ⅕
    r = q + ε
    0<δ : 0 < δ
    0<δ = subst (_< δ) (+InvR (q · q)) (<-+o (q · q) (q + 1) (- (q · q)) q²<q+1)
    0<ε : 0 < ε
    0<ε = 0<·d δ ⅕ 0<δ 0<⅕
    0≤ε : 0 ≤ ε
    0≤ε = <Weaken≤ 0 ε 0<ε
    q<r : q < r
    q<r = subst (_< r) (+IdR q) (<-o+ 0 ε q 0<ε)
    -- ε < 1
    0≤q² : 0 ≤ (q · q)
    0≤q² = 0≤sq q 0≤q
    -neg≤0 : (- (q · q)) ≤ 0
    -neg≤0 = subst2 _≤_ (+IdL (- (q · q))) (+InvR (q · q))
               (≤-+o 0 (q · q) (- (q · q)) 0≤q²)
    δ≤q+1 : δ ≤ (q + 1)
    δ≤q+1 = subst (δ ≤_) (+IdR (q + 1)) (≤-o+ (- (q · q)) 0 (q + 1) -neg≤0)
    q+1<3 : (q + 1) < 3
    q+1<3 = subst ((q + 1) <_) (getYes (discreteℚ (2 + 1) 3) tt)
              (<-+o q 2 1 (q<2-lem q 0≤q q²<q+1))
    δ<3 : δ < 3
    δ<3 = isTrans≤< δ (q + 1) 3 δ≤q+1 q+1<3
    ε<1 : ε < 1
    ε<1 = isTrans< ε (3 · ⅕) 1 (<-·o δ 3 ⅕ 0<⅕ δ<3) (getYes (<Dec (3 · ⅕) 1) tt)
    ε≤1 : ε ≤ 1
    ε≤1 = <Weaken≤ ε 1 ε<1
    -- STRICT bound: (r−q)·((r+q)−1) < δ
    r-q≡ε : (q + ε) + (- q) ≡ ε
    r-q≡ε = cong (_+ (- q)) (+Comm q ε) ∙ sym (+Assoc ε q (- q))
          ∙ cong (ε +_) (+InvR q) ∙ +IdR ε
    rq≡ : (r + q) ≡ (2 · q) + ε
    rq≡ = sym (+Assoc q ε q) ∙ cong (q +_) (+Comm ε q) ∙ +Assoc q q ε
        ∙ cong (_+ ε) (dbl q)
    F = (r + q) + (- 1)
    F≡ : F ≡ (2 · q) + (ε + (- 1))
    F≡ = cong (_+ (- 1)) rq≡ ∙ sym (+Assoc (2 · q) ε (- 1))
    ε-1≤0 : (ε + (- 1)) ≤ 0
    ε-1≤0 = subst ((ε + (- 1)) ≤_) (+InvR 1) (≤-+o ε 1 (- 1) ε≤1)
    F≤2q : F ≤ (2 · q)
    F≤2q = subst (_≤ (2 · q)) (sym F≡)
             (subst (((2 · q) + (ε + (- 1))) ≤_) (+IdR (2 · q))
               (≤-o+ (ε + (- 1)) 0 (2 · q) ε-1≤0))
    εF≤ε2q : ε · F ≤ ε · (2 · q)
    εF≤ε2q = subst2 _≤_ (·Comm F ε) (·Comm (2 · q) ε) (≤-·o F (2 · q) ε 0≤ε F≤2q)
    2q<5 : (2 · q) < 5
    2q<5 = isTrans< (2 · q) 4 5
             (subst (_< 4) (·Comm q 2)
               (subst ((q · 2) <_) (getYes (discreteℚ (2 · 2) 4) tt)
                 (<-·o q 2 2 0<2ℚ (q<2-lem q 0≤q q²<q+1))))
             (getYes (<Dec 4 5) tt)
    ⅕2q<1 : ⅕ · (2 · q) < 1
    ⅕2q<1 = subst2 _<_ (·Comm (2 · q) ⅕) (getYes (discreteℚ (5 · ⅕) 1) tt)
              (<-·o (2 · q) 5 ⅕ 0<⅕ 2q<5)
    ε2q<δ : ε · (2 · q) < δ
    ε2q<δ = subst (ε · (2 · q) <_) (·IdR δ)
              (subst (_< (δ · 1)) (·Assoc δ ⅕ (2 · q))
                (subst2 _<_ (·Comm (⅕ · (2 · q)) δ) (·Comm 1 δ)
                  (<-·o (⅕ · (2 · q)) 1 δ 0<δ ⅕2q<1)))
    εF<δ : ε · F < δ
    εF<δ = isTrans≤< (ε · F) (ε · (2 · q)) δ εF≤ε2q ε2q<δ
    STRICT : ((q + ε) + (- q)) · F < δ
    STRICT = subst (λ z → z · F < δ) (sym r-q≡ε) εF<δ
    -- assembly via quad-id and quad-sub→
    A B : ℚ
    A = (r · r) + (- r)
    B = (q · q) + (- q)
    A-B<δ : A + (- B) < δ
    A-B<δ = subst (_< δ) (sym (quad-id q r)) STRICT
    δ+B≡1 : δ + B ≡ 1
    δ+B≡1 = sym (+Assoc (q + 1) (- (q · q)) B)
          ∙ cong ((q + 1) +_) (+Assoc (- (q · q)) (q · q) (- q))
          ∙ cong (λ z → (q + 1) + (z + (- q))) (+InvL (q · q))
          ∙ cong ((q + 1) +_) (+IdL (- q))
          ∙ cong (_+ (- q)) (+Comm q 1) ∙ sym (+Assoc 1 q (- q))
          ∙ cong (1 +_) (+InvR q) ∙ +IdR 1
    A<1 : A < 1
    A<1 = subst (A <_) δ+B≡1
            (subst (_< (δ + B)) (+neg-cancel A B) (<-+o (A + (- B)) δ B A-B<δ))
    r²<r+1 : (r · r) < (r + 1)
    r²<r+1 = quad-sub→ r A<1

-- L OPEN ABOVE (rounded): every q∈L has a larger q'∈L.
φL-rounded : (q : ℚ) → ⟦ φL ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ φL ⟧ r ∥₁
φL-rounded q hL with <Dec q 0
... | yes q<0 = ∣ fst dq , (fst (snd dq) , ∣ inl (snd (snd dq)) ∣₁) ∣₁
      where dq = dense q 0 q<0
... | no ¬q<0 = PT.rec isPropPropTrunc handle hL
      where
        0≤q = ≮→≥ q 0 ¬q<0
        handle : (q < 0) ⊎ (q · q < q + 1) → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ φL ⟧ r ∥₁
        handle (inl q<0)    = rec (¬q<0 q<0)
        handle (inr q²<q+1) = ∣ fst nq , (fst (snd nq) , ∣ inr (snd (snd nq)) ∣₁) ∣₁
          where nq = nudge q 0≤q q²<q+1

-- ── the dual nudge (downward): a point strictly inside the UPPER cut, below q ─
-- for q∈(φ,2], r = q − η/5 (η = q²−q−1) still lies above φ: r<q, 1<r, r+1<r².
nudge-down : (q : ℚ) → q ≤ 2 → 1 < q → (q + 1) < (q · q)
           → Σ[ r ∈ ℚ ] (r < q) × ((1 < r) × ((r + 1) < (r · r)))
nudge-down q q≤2 1<q q+1<q² = r , r<q , (1<r , r+1<r²)
  where
    η ε r : ℚ
    η = (q · q) + (- (q + 1))
    ε = η · ⅕
    r = q + (- ε)
    0<η : 0 < η
    0<η = subst (_< η) (+InvR (q + 1)) (<-+o (q + 1) (q · q) (- (q + 1)) q+1<q²)
    0<ε : 0 < ε
    0<ε = 0<·d η ⅕ 0<η 0<⅕
    0≤ε : 0 ≤ ε
    0≤ε = <Weaken≤ 0 ε 0<ε
    -ε<0 : (- ε) < 0
    -ε<0 = subst2 _<_ (+IdL (- ε)) (+InvR ε) (<-+o 0 ε (- ε) 0<ε)
    r<q : r < q
    r<q = subst (r <_) (+IdR q) (<-o+ (- ε) 0 q -ε<0)
    0<q : 0 < q
    0<q = isTrans< 0 1 q 0<1ℚ 1<q
    0≤q : 0 ≤ q
    0≤q = <Weaken≤ 0 q 0<q
    -- STRICT-down: (q−r)·((q+r)−1) < η
    q-r≡ε : (q + (- r)) ≡ ε
    q-r≡ε = cong (q +_) (-Dist q (- ε) ∙ cong ((- q) +_) (-Invol ε))
          ∙ +Assoc q (- q) ε ∙ cong (_+ ε) (+InvR q) ∙ +IdL ε
    rq≡ : (q + r) ≡ (2 · q) + (- ε)
    rq≡ = +Assoc q q (- ε) ∙ cong (_+ (- ε)) (dbl q)
    F = (q + r) + (- 1)
    F≡ : F ≡ (2 · q) + ((- ε) + (- 1))
    F≡ = cong (_+ (- 1)) rq≡ ∙ sym (+Assoc (2 · q) (- ε) (- 1))
    -ε≤0 : (- ε) ≤ 0
    -ε≤0 = subst2 _≤_ (+IdL (- ε)) (+InvR ε) (≤-+o 0 ε (- ε) 0≤ε)
    -1≤0 : (- 1) ≤ 0
    -1≤0 = <Weaken≤ (- 1) 0 (subst2 _<_ (+IdL (- 1)) (+InvR 1) (<-+o 0 1 (- 1) 0<1ℚ))
    -ε-1≤0 : ((- ε) + (- 1)) ≤ 0
    -ε-1≤0 = subst (((- ε) + (- 1)) ≤_) (+IdR 0) (≤Monotone+ (- ε) 0 (- 1) 0 -ε≤0 -1≤0)
    F≤2q : F ≤ (2 · q)
    F≤2q = subst (_≤ (2 · q)) (sym F≡)
             (subst (((2 · q) + ((- ε) + (- 1))) ≤_) (+IdR (2 · q))
               (≤-o+ ((- ε) + (- 1)) 0 (2 · q) -ε-1≤0))
    εF≤ε2q : ε · F ≤ ε · (2 · q)
    εF≤ε2q = subst2 _≤_ (·Comm F ε) (·Comm (2 · q) ε) (≤-·o F (2 · q) ε 0≤ε F≤2q)
    2q<5 : (2 · q) < 5
    2q<5 = isTrans≤< (2 · q) 4 5
             (subst (_≤ 4) (·Comm q 2)
               (subst ((q · 2) ≤_) (getYes (discreteℚ (2 · 2) 4) tt)
                 (≤-·o q 2 2 (<Weaken≤ 0 2 0<2ℚ) q≤2)))
             (getYes (<Dec 4 5) tt)
    ⅕2q<1 : ⅕ · (2 · q) < 1
    ⅕2q<1 = subst2 _<_ (·Comm (2 · q) ⅕) (getYes (discreteℚ (5 · ⅕) 1) tt)
              (<-·o (2 · q) 5 ⅕ 0<⅕ 2q<5)
    ε2q<η : ε · (2 · q) < η
    ε2q<η = subst (ε · (2 · q) <_) (·IdR η)
              (subst (_< (η · 1)) (·Assoc η ⅕ (2 · q))
                (subst2 _<_ (·Comm (⅕ · (2 · q)) η) (·Comm 1 η)
                  (<-·o (⅕ · (2 · q)) 1 η 0<η ⅕2q<1)))
    εF<η : ε · F < η
    εF<η = isTrans≤< (ε · F) (ε · (2 · q)) η εF≤ε2q ε2q<η
    STRICT : ((q + (- r)) · F) < η
    STRICT = subst (λ z → z · F < η) (sym q-r≡ε) εF<η
    -- assembly: 1 < (r²−r), hence r+1<r²
    A' B' : ℚ
    A' = (q · q) + (- q)
    B' = (r · r) + (- r)
    A'-B'<η : (A' + (- B')) < η
    A'-B'<η = subst (_< η) (sym (quad-id r q)) STRICT
    η≡A'-1 : η ≡ (A' + (- 1))
    η≡A'-1 = cong ((q · q) +_) (-Dist q 1) ∙ +Assoc (q · q) (- q) (- 1)
    1<B' : 1 < B'
    1<B' = subst2 _<_ (-Invol 1) (-Invol B')
             (neg-flip (- B') (- 1)
               (<-o+-cancel (- B') (- 1) A'
                 (subst ((A' + (- B')) <_) η≡A'-1 A'-B'<η)))
    r+1<r² : (r + 1) < (r · r)
    r+1<r² = add-r→ (r · r) r 1<B'
    -- 1<r, via ε < q−1  (η ≤ q−1 since q ≤ 2, so ε = η/5 < q−1)
    0<q-1 : 0 < (q + (- 1))
    0<q-1 = subst (_< (q + (- 1))) (+InvR 1) (<-+o 1 q (- 1) 1<q)
    q²≤2q : (q · q) ≤ (2 · q)
    q²≤2q = ≤-·o q 2 q 0≤q q≤2
    2q-q≡q : (2 · q) + (- q) ≡ q
    2q-q≡q = cong (_+ (- q)) (sym (dbl q)) ∙ sym (+Assoc q q (- q))
           ∙ cong (q +_) (+InvR q) ∙ +IdR q
    η≤q-1 : η ≤ (q + (- 1))
    η≤q-1 = subst (η ≤_) e2 (≤-+o (q · q) (2 · q) (- (q + 1)) q²≤2q)
      where e2 : (2 · q) + (- (q + 1)) ≡ (q + (- 1))
            e2 = cong ((2 · q) +_) (-Dist q 1) ∙ +Assoc (2 · q) (- q) (- 1)
               ∙ cong (_+ (- 1)) 2q-q≡q
    ε≤q-1·⅕ : ε ≤ (q + (- 1)) · ⅕
    ε≤q-1·⅕ = ≤-·o η (q + (- 1)) ⅕ (<Weaken≤ 0 ⅕ 0<⅕) η≤q-1
    q-1·⅕<q-1 : (q + (- 1)) · ⅕ < (q + (- 1))
    q-1·⅕<q-1 = subst2 _<_ (·Comm ⅕ (q + (- 1))) (·IdL (q + (- 1)))
                  (<-·o ⅕ 1 (q + (- 1)) 0<q-1 (getYes (<Dec ⅕ 1) tt))
    ε<q-1 : ε < (q + (- 1))
    ε<q-1 = isTrans≤< ε ((q + (- 1)) · ⅕) (q + (- 1)) ε≤q-1·⅕ q-1·⅕<q-1
    1<r : 1 < r
    1<r = subst (_< r) (sym (+Assoc 1 ε (- ε)) ∙ cong (1 +_) (+InvR ε) ∙ +IdR 1)
            (<-+o (1 + ε) q (- ε) 1+ε<q)
      where e4 : (q + (- 1)) + 1 ≡ q
            e4 = sym (+Assoc q (- 1) 1) ∙ cong (q +_) (+InvL 1) ∙ +IdR q
            1+ε<q : (1 + ε) < q
            1+ε<q = subst (_< q) (+Comm ε 1)
                      (subst ((ε + 1) <_) e4 (<-+o ε (q + (- 1)) 1 ε<q-1))

-- U OPEN BELOW (rounded): every q∈U has a smaller q'∈U.
φU-rounded : (q : ℚ) → ⟦ φU ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ φU ⟧ r ∥₁
φU-rounded q (1<q , q+1<q²) with <Dec 2 q
... | yes 2<q = ∣ 2 , (2<q , (getYes (<Dec 1 2) tt , getYes (<Dec (2 + 1) (2 · 2)) tt)) ∣₁
... | no ¬2<q = ∣ fst nd , (fst (snd nd) , snd (snd nd)) ∣₁
      where nd = nudge-down q (≮→≥ 2 q ¬2<q) 1<q q+1<q²

-- ════════════════════════════════════════════════════════════════════════════
-- φ AS A LOCATED REAL: the golden spectral value, a genuine Dedekind cut of ℚ.
-- This is the ORGANISM of disclaimer D1 -- the spectrum is no longer a germ.
-- ════════════════════════════════════════════════════════════════════════════
φ : ℝ
φ = φL , φU ,
    ( φL-inhab , φU-inhab
    , φL-rounded , φU-rounded
    , φL-down , φU-up
    , φ-disjoint , φ-located )
