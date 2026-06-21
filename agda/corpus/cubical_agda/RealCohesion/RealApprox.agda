{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5 / real arithmetic: the constructive-completeness ENGINE.  The
-- trisection step narrows a bracketing interval [a,c] of a real x (a∈xL, c∈xU)
-- to EXACTLY 2/3 of its width using a single `located` call -- the geometric
-- contraction whose iteration gives arbitrarily precise rational bounds (the
-- approximation lemma), the keystone of Dedekind addition and φ-as-a-real.

module corpus.cubical_agda.RealCohesion.RealApprox where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <-+o; <-o+; <-·o; <Dec; isTrans<)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

open import corpus.cubical_agda.RealCohesion.DedekindReal

-- concrete-inequality extractor (the Sprint-1 idiom)
private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _  = a
  getYes (no  _) ()

⅓ : ℚ
⅓ = [ pos 1 / 1+ 2 ]

-- the only concrete fraction facts (the rest is ring algebra via solve!).
0<⅓   : 0 < ⅓        ;  0<⅓   = getYes (<Dec 0 ⅓) tt
⅓<1   : ⅓ < 1        ;  ⅓<1   = getYes (<Dec ⅓ 1) tt
⅓<1-⅓ : ⅓ < 1 - ⅓    ;  ⅓<1-⅓ = getYes (<Dec ⅓ (1 - ⅓)) tt
0<1-⅓ : 0 < 1 - ⅓    ;  0<1-⅓ = getYes (<Dec 0 (1 - ⅓)) tt

-- positivity of a width, by the dense-technique.
0<width : (a c : ℚ) → a < c → 0 < c - a
0<width a c a<c = subst (_< (c - a)) (+InvR a) (<-+o a c (- a) a<c)

-- positivity of a product (top-level so the motive elaborates cleanly).
0<·d : (f y : ℚ) → 0 < f → 0 < y → 0 < f · y
0<·d f y 0<f 0<y = subst (_< (f · y)) (·AnnihilL y) (<-·o 0 f y 0<y 0<f)

open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)

-- x's located law (the 8th cut conjunct).
locOf : (x : ℝ) (q r : ℚ) → q < r → ∥ ⟦ lowerCut x ⟧ q ⊎ ⟦ upperCut x ⟧ r ∥₁
locOf x = x .snd .snd .snd .snd .snd .snd .snd .snd .snd

-- THE TRISECTION STEP: narrow a bracket [a,c] of x to EXACTLY (1+(-⅓))=2/3 of
-- its width, via one located call at the two interior trisection points.
-- (widths written with + (- ·) since the ring solver recognizes unary minus only.)
open import corpus.cubical_agda.RealCohesion.RealNegation using (neg-flip)

W : ℚ
W = 1 + (- ⅓)               -- = 2/3
W<1 : W < 1
W<1 = getYes (<Dec W 1) tt

-- the one manual ℚ identity (the solver chokes on ℚ's SetQuotient structure).
a+d≡c : (a c : ℚ) → a + (c + (- a)) ≡ c
a+d≡c a c =
  a + (c + (- a))   ≡⟨ +Assoc a c (- a) ⟩
  (a + c) + (- a)   ≡⟨ cong (_+ (- a)) (+Comm a c) ⟩
  (c + a) + (- a)   ≡⟨ sym (+Assoc c a (- a)) ⟩
  c + (a + (- a))   ≡⟨ cong (c +_) (+InvR a) ⟩
  c + 0             ≡⟨ +IdR c ⟩
  c ∎

-- negation distributes over + and pulls out of · (since - x = -1 · x).
-Dist : (x y : ℚ) → - (x + y) ≡ (- x) + (- y)
-Dist x y = ·DistL+ -1 x y
neg-mult : (x y : ℚ) → (- x) · y ≡ - (x · y)
neg-mult x y = sym (·Assoc -1 x y)
shift-cancel : (a e : ℚ) → (a + e) + (- a) ≡ e
shift-cancel a e =
  (a + e) + (- a)   ≡⟨ cong (_+ (- a)) (+Comm a e) ⟩
  (e + a) + (- a)   ≡⟨ sym (+Assoc e a (- a)) ⟩
  e + (a + (- a))   ≡⟨ cong (e +_) (+InvR a) ⟩
  e + 0             ≡⟨ +IdR e ⟩
  e ∎

-- the EXACT 2/3 width identities (W = 1 + (-⅓)), hand-proved (solve! fails on ℚ).
wL-lem : (a c : ℚ) → c + (- (a + ⅓ · (c + (- a)))) ≡ (1 + (- ⅓)) · (c + (- a))
wL-lem a c =
  c + (- (a + ⅓ · d))                  ≡⟨ cong (c +_) (-Dist a (⅓ · d)) ⟩
  c + ((- a) + (- (⅓ · d)))            ≡⟨ +Assoc c (- a) (- (⅓ · d)) ⟩
  (c + (- a)) + (- (⅓ · d))            ≡⟨ sym Weq ⟩
  (1 + (- ⅓)) · d ∎
  where
    d = c + (- a)
    Weq : (1 + (- ⅓)) · d ≡ d + (- (⅓ · d))
    Weq = (1 + (- ⅓)) · d            ≡⟨ ·DistR+ 1 (- ⅓) d ⟩
          (1 · d) + ((- ⅓) · d)      ≡⟨ cong (_+ ((- ⅓) · d)) (·IdL d) ⟩
          d + ((- ⅓) · d)            ≡⟨ cong (d +_) (neg-mult ⅓ d) ⟩
          d + (- (⅓ · d)) ∎
wR-lem : (a c : ℚ) → (a + (1 + (- ⅓)) · (c + (- a))) + (- a) ≡ (1 + (- ⅓)) · (c + (- a))
wR-lem a c = shift-cancel a ((1 + (- ⅓)) · (c + (- a)))

-- THE TRISECTION STEP: one located call at the interior trisection points
-- m₁=a+⅓(c−a), m₂=a+⅔(c−a) narrows a bracket [a,c] of x to [a',c'] still
-- containing x, with EXACTLY 2/3 the width -- the geometric contraction.
trisect : (x : ℝ) (a c : ℚ) → ⟦ lowerCut x ⟧ a → ⟦ upperCut x ⟧ c → a < c →
  ∥ Σ[ a' ∈ ℚ ] Σ[ c' ∈ ℚ ]
      ⟦ lowerCut x ⟧ a' × ⟦ upperCut x ⟧ c' × (a' < c') × ((c' + (- a')) ≡ W · (c + (- a))) ∥₁
trisect x a c xLa xUc a<c = PT.map decide (locOf x m₁ m₂ m₁<m₂)
  where
    d  = c + (- a)
    m₁ m₂ : ℚ
    m₁ = a + ⅓ · d
    m₂ = a + W · d
    0<d : 0 < d
    0<d = 0<width a c a<c
    m₁<m₂ : m₁ < m₂
    m₁<m₂ = <-o+ (⅓ · d) (W · d) a (<-·o ⅓ W d 0<d ⅓<1-⅓)
    a<m₁ : a < m₁
    a<m₁ = subst (_< m₁) (+IdR a) (<-o+ 0 (⅓ · d) a (0<·d ⅓ d 0<⅓ 0<d))
    m₂<c : m₂ < c
    m₂<c = subst (m₂ <_) (cong (a +_) (·IdL d) ∙ a+d≡c a c) (<-o+ (W · d) (1 · d) a Wd<1d)
      where Wd<1d : W · d < 1 · d
            Wd<1d = <-·o W 1 d 0<d W<1
    decide : ⟦ lowerCut x ⟧ m₁ ⊎ ⟦ upperCut x ⟧ m₂ →
             Σ[ a' ∈ ℚ ] Σ[ c' ∈ ℚ ]
               ⟦ lowerCut x ⟧ a' × ⟦ upperCut x ⟧ c' × (a' < c') × ((c' + (- a')) ≡ W · d)
    decide (inl xLm₁) = m₁ , c  , xLm₁ , xUc  , isTrans< m₁ m₂ c m₁<m₂ m₂<c , wL-lem a c
    decide (inr xUm₂) = a  , m₂ , xLa  , xUm₂ , isTrans< a m₁ m₂ a<m₁ m₁<m₂ , wR-lem a c

-- ── iterate the contraction n times: width becomes (2/3)ⁿ·(c−a) ──────────
infixr 8 _^ℚ_
_^ℚ_ : ℚ → ℕ → ℚ
x ^ℚ zero    = 1
x ^ℚ (suc n) = x · (x ^ℚ n)

pow-step : (n : ℕ) (d : ℚ) → (W ^ℚ n) · (W · d) ≡ (W ^ℚ (suc n)) · d
pow-step n d =
  (W ^ℚ n) · (W · d)    ≡⟨ ·Assoc (W ^ℚ n) W d ⟩
  ((W ^ℚ n) · W) · d    ≡⟨ cong (_· d) (·Comm (W ^ℚ n) W) ⟩
  (W · (W ^ℚ n)) · d ∎

-- n-fold trisection: a bracket of x of width EXACTLY (2/3)ⁿ·(c−a).
trisect-n : (n : ℕ) (x : ℝ) (a c : ℚ) → ⟦ lowerCut x ⟧ a → ⟦ upperCut x ⟧ c → a < c →
  ∥ Σ[ a' ∈ ℚ ] Σ[ c' ∈ ℚ ]
      ⟦ lowerCut x ⟧ a' × ⟦ upperCut x ⟧ c' × (a' < c')
      × ((c' + (- a')) ≡ (W ^ℚ n) · (c + (- a))) ∥₁
trisect-n zero x a c xLa xUc a<c =
  ∣ a , c , xLa , xUc , a<c , sym (·IdL (c + (- a))) ∣₁
trisect-n (suc n) x a c xLa xUc a<c =
  PT.rec PT.squash₁
    (λ { (a₁ , c₁ , xLa₁ , xUc₁ , a₁<c₁ , w₁) →
      PT.map
        (λ { (a' , c' , xLa' , xUc' , a'<c' , w') →
          a' , c' , xLa' , xUc' , a'<c' ,
            (w' ∙ cong ((W ^ℚ n) ·_) w₁ ∙ pow-step n (c + (- a))) })
        (trisect-n n x a₁ c₁ xLa₁ xUc₁ a₁<c₁) })
    (trisect x a c xLa xUc a<c)
