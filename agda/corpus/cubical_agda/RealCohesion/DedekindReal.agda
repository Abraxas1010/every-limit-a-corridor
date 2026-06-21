{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 1 of the germ->organism programme (conjecture
-- every_limit_corridor_organism_20260620): the genuine analytic real line as
-- Dedekind cuts over the cubical rationals.  This is the shared substrate that
-- overcomes Disclaimer 3 (shape!=flat on the real line, Sprint 2) and feeds the
-- located spectrum (Disclaimer 1).  --cubical --safe, no postulates.
--
-- A real is a pair of cuts (L,U) on Q satisfying inhabitation, roundedness,
-- disjointness, and locatedness (HoTT book Def. 11.2.1).  ℚ's decidable
-- trichotomy supplies locatedness for the rational embedding for free.

module corpus.cubical_agda.RealCohesion.DedekindReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; isProp<; isTrans<; isAsym<; _≟_; lt; eq; gt; <-+o; <-o+; <-·o; <Dec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

private
  variable ℓ : Level

-- A predicate valued in propositions (a "cut side").
Pred : Type₁
Pred = ℚ → hProp ℓ-zero

⟦_⟧ : Pred → ℚ → Type₀
⟦ P ⟧ q = ⟨ P q ⟩

-- The four Dedekind-cut laws, packaged as a single proposition.
IsCut : Pred → Pred → Type₀
IsCut L U =
    ∥ Σ[ q ∈ ℚ ] ⟦ L ⟧ q ∥₁
  × ∥ Σ[ q ∈ ℚ ] ⟦ U ⟧ q ∥₁
  × ((q : ℚ) → ⟦ L ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ L ⟧ r ∥₁)   -- L open above
  × ((q : ℚ) → ⟦ U ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ U ⟧ r ∥₁)   -- U open below
  × ((q r : ℚ) → q < r → ⟦ L ⟧ r → ⟦ L ⟧ q)                    -- L down-closed
  × ((q r : ℚ) → q < r → ⟦ U ⟧ q → ⟦ U ⟧ r)                    -- U up-closed
  × ((q : ℚ) → ⟦ L ⟧ q → ⟦ U ⟧ q → ⊥)                          -- disjoint
  × ((q r : ℚ) → q < r → ∥ ⟦ L ⟧ q ⊎ ⟦ U ⟧ r ∥₁)               -- located

isPropIsCut : (L U : Pred) → isProp (IsCut L U)
isPropIsCut L U =
  isProp× squash₁
  (isProp× squash₁
  (isProp× (isPropΠ2 λ _ _ → squash₁)
  (isProp× (isPropΠ2 λ _ _ → squash₁)
  (isProp× (isPropΠ λ q → isPropΠ3 λ r _ _ → snd (L q))
  (isProp× (isPropΠ λ q → isPropΠ3 λ r _ _ → snd (U r))
  (isProp× (isPropΠ3 λ _ _ _ → ⊥.isProp⊥)
           (isPropΠ3 λ _ _ _ → squash₁)))))))

-- The analytic real line.
ℝ : Type₁
ℝ = Σ[ L ∈ Pred ] Σ[ U ∈ Pred ] IsCut L U

isSetℝ : isSet ℝ
isSetℝ =
  isSetΣ (isSet→ isSetHProp) λ L →
  isSetΣ (isSet→ isSetHProp) λ U →
  isProp→isSet (isPropIsCut L U)

-- projections
lowerCut : ℝ → Pred
lowerCut x = x .fst

upperCut : ℝ → Pred
upperCut x = x .snd .fst

-- ─────────────────────────────────────────────────────────────────────────
-- Sprint 1 M1b: the rational embedding, 0/1, and the apartness 0#1.
-- ─────────────────────────────────────────────────────────────────────────

-- Extract a proof from a decision that computes to `yes` on closed literals.
private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _  = a
  getYes (no  _) ()

half : ℚ
half = [ pos 1 / 1+ 1 ]

0<half : 0 < half
0<half = getYes (<Dec 0 half) tt

half<1 : half < 1
half<1 = getYes (<Dec half 1) tt

-- Density: between any a < b lies (a + (b-a)·½).  The cut roundedness laws need it.
dense : (a b : ℚ) → a < b → Σ[ c ∈ ℚ ] (a < c) × (c < b)
dense a b a<b = c , a<c , c<b
  where
    d : ℚ
    d = b - a
    a+d≡b : a + d ≡ b
    a+d≡b =
      a + (b + (- a))   ≡⟨ +Assoc a b (- a) ⟩
      (a + b) + (- a)   ≡⟨ cong (_+ (- a)) (+Comm a b) ⟩
      (b + a) + (- a)   ≡⟨ sym (+Assoc b a (- a)) ⟩
      b + (a + (- a))   ≡⟨ cong (b +_) (+InvR a) ⟩
      b + 0             ≡⟨ +IdR b ⟩
      b ∎
    0<d : 0 < d
    0<d = subst (_< d) (+InvR a) (<-+o a b (- a) a<b)
    c : ℚ
    c = a + d · half
    0<dh : 0 < d · half
    0<dh = subst (_< (d · half)) (·AnnihilL half) (<-·o 0 d half 0<half 0<d)
    a<c : a < c
    a<c = subst (_< c) (+IdR a) (<-o+ 0 (d · half) a 0<dh)
    dh<d : d · half < d
    dh<d = subst2 _<_ (·Comm half d) (·IdL d) (<-·o half 1 d 0<d half<1)
    c<b : c < b
    c<b = subst (c <_) a+d≡b (<-o+ (d · half) d a dh<d)

-- unboundedness helpers (for cut inhabitation)
0<1ℚ : 0 < 1
0<1ℚ = getYes (<Dec 0 1) tt

neg1<0 : (- 1) < 0
neg1<0 = getYes (<Dec (- 1) 0) tt

x<x+1 : (x : ℚ) → x < x + 1
x<x+1 x = subst (_< (x + 1)) (+IdR x) (<-o+ 0 1 x 0<1ℚ)

x-1<x : (x : ℚ) → x - 1 < x
x-1<x x = subst ((x + (- 1)) <_) (+IdR x) (<-o+ (- 1) 0 x neg1<0)

-- The rational embedding ι : ℚ → ℝ.  L = {p | p<q}, U = {p | q<p}.
ι : ℚ → ℝ
ι q = L , U , (Linhab , Uinhab , Lopen , Uopen , Ldown , Uup , disj , loc)
  where
    L : Pred
    L p = (p < q) , isProp< p q
    U : Pred
    U p = (q < p) , isProp< q p
    Linhab = ∣ (q - 1) , x-1<x q ∣₁
    Uinhab = ∣ (q + 1) , x<x+1 q ∣₁
    Lopen : (p : ℚ) → ⟦ L ⟧ p → ∥ Σ[ r ∈ ℚ ] (p < r) × ⟦ L ⟧ r ∥₁
    Lopen p p<q = ∣ dense p q p<q ∣₁
    Uopen : (p : ℚ) → ⟦ U ⟧ p → ∥ Σ[ r ∈ ℚ ] (r < p) × ⟦ U ⟧ r ∥₁
    Uopen p q<p = let (c , q<c , c<p) = dense q p q<p in ∣ c , c<p , q<c ∣₁
    Ldown : (p r : ℚ) → p < r → ⟦ L ⟧ r → ⟦ L ⟧ p
    Ldown p r p<r r<q = isTrans< p r q p<r r<q
    Uup : (p r : ℚ) → p < r → ⟦ U ⟧ p → ⟦ U ⟧ r
    Uup p r p<r q<p = isTrans< q p r q<p p<r
    disj : (p : ℚ) → ⟦ L ⟧ p → ⟦ U ⟧ p → ⊥
    disj p p<q q<p = isAsym< p q p<q q<p
    loc : (p r : ℚ) → p < r → ∥ ⟦ L ⟧ p ⊎ ⟦ U ⟧ r ∥₁
    loc p r p<r with p ≟ q
    ... | lt p<q = ∣ inl p<q ∣₁
    ... | eq p≡q = ∣ inr (subst (_< r) p≡q p<r) ∣₁
    ... | gt q<p = ∣ inr (isTrans< q p r q<p p<r) ∣₁

-- ─────────────────────────────────────────────────────────────────────────
-- 0, 1, the strict real order, and the apartness 0#1 — the witness that
-- ♭ℝ is not contractible (the input Sprint 2 needs to separate shape from flat).
-- ─────────────────────────────────────────────────────────────────────────

0ℝ : ℝ
0ℝ = ι 0

1ℝ : ℝ
1ℝ = ι 1

-- x <ℝ y  ⟺  some rational sits in the upper cut of x and the lower cut of y.
_<ℝ_ : ℝ → ℝ → Type₀
x <ℝ y = ∥ Σ[ q ∈ ℚ ] ⟦ upperCut x ⟧ q × ⟦ lowerCut y ⟧ q ∥₁

isProp-<ℝ : (x y : ℝ) → isProp (x <ℝ y)
isProp-<ℝ x y = squash₁

-- apartness of reals
_#ℝ_ : ℝ → ℝ → Type₀
x #ℝ y = (x <ℝ y) ⊎ (y <ℝ x)

0<ℝ1 : 0ℝ <ℝ 1ℝ
0<ℝ1 = ∣ half , 0<half , half<1 ∣₁

-- THE KEY WITNESS: 0 and 1 are apart in ℝ (so ♭ℝ has ≥2 distinct points).
0#1 : 0ℝ #ℝ 1ℝ
0#1 = inl 0<ℝ1
