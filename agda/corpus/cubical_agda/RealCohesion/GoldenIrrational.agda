{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 6 capstone: φ is IRRATIONAL.  The heart is that no positive integers a,b
-- satisfy a² = ab + b² (= φ is not a ratio of positive integers), proved by
-- INFINITE DESCENT: writing a = b+c additively (no truncated subtraction), the
-- equation reduces to b² = bc + c², a strictly smaller solution (a > b > c > …),
-- killed by the well-foundedness of < on ℕ.  No postulates.

module corpus.cubical_agda.RealCohesion.GoldenIrrational where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma using (Σ-syntax; _,_; _×_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Induction.WellFounded using (Acc; acc)

-- the golden Diophantine relation.
golden-eq : ℕ → ℕ → Type
golden-eq a b = a · a ≡ a · b + b · b

-- left distributivity (from ·-comm + ·-distribʳ).
·-dl : (m n o : ℕ) → m · (n + o) ≡ m · n + m · o
·-dl m n o = ·-comm m (n + o) ∙ sym (·-distribʳ n o m)
           ∙ cong₂ _+_ (·-comm n m) (·-comm o m)

-- THE DESCENT EQUATION: a = b+c with golden-eq (b+c) b ⟹ golden-eq b c.
descent-eq : (b c : ℕ) → golden-eq (b + c) b → golden-eq b c
descent-eq b c h = sym (inj-m+ {m = b · b + c · b} (sym chain ∙ h ∙ rhs))
  where
    -- expand (b+c)·(b+c) ≡ (b·b + c·b) + (b·c + c·c)
    chain : (b + c) · (b + c)
          ≡ (b · b + c · b) + (b · c + c · c)
    chain = sym (·-distribʳ b c (b + c))
          ∙ cong₂ _+_ (·-dl b b c) (·-dl c b c)
          ∙ cong₂ (λ u v → (b · b + u) + (v + c · c)) (·-comm b c) (·-comm c b)
    -- expand (b+c)·b + b·b ≡ (b·b + c·b) + b·b
    rhs : (b + c) · b + b · b ≡ (b · b + c · b) + b · b
    rhs = cong (_+ b · b) (sym (·-distribʳ b c b))

-- y·y < x·x ⟹ y < x  (squaring reflects order on ℕ).
sqlt→lt : (x y : ℕ) → y · y < x · x → y < x
sqlt→lt x y yy<xx with y ≟ x
... | lt y<x = y<x
... | eq y≡x = ⊥.rec (¬m<m (subst (λ z → z · z < x · x) y≡x yy<xx))
... | gt x<y = ⊥.rec (¬m<m (<≤-trans yy<xx xx≤yy))
  where
    x≤y : x ≤ y
    x≤y = <-weaken x<y
    xx≤yy : x · x ≤ y · y
    xx≤yy = ≤-trans (≤-·k {m = x} {n = y} {k = x} x≤y)
                    (subst (_≤ y · y) (·-comm x y) (≤-·k {m = x} {n = y} {k = y} x≤y))

-- from golden-eq with 1≤y, the larger value dominates: y < x.
golden-gt : (x y : ℕ) → 1 ≤ y → golden-eq x y → y < x
golden-gt x y 1≤y h = sqlt→lt x y yy<xx
  where
    1≤yy : 1 ≤ y · y
    1≤yy = ≤-trans 1≤y (subst (_≤ y · y) (·-identityˡ y) (≤-·k {m = 1} {n = y} {k = y} 1≤y))
    yy≤xx : y · y ≤ x · x
    yy≤xx = subst (y · y ≤_) (sym h) (≤-+k {m = 0} {n = x · y} {k = y · y} zero-≤)
    0<x : 0 < x
    0<x = sqlt→lt x 0 (≤-trans 1≤yy yy≤xx)
    0<xy : 1 ≤ x · y
    0<xy = ≤-trans 1≤y (subst (_≤ x · y) (·-identityˡ y) (≤-·k {m = 1} {n = x} {k = y} 0<x))
    yy<xx : y · y < x · x
    yy<xx = subst (y · y <_) (sym h) (≤-+k {m = 1} {n = x · y} {k = y · y} 0<xy)

-- b < a gives the additive witness a = b + c with c ≥ 1.
split : (b a : ℕ) → b < a → Σ[ c ∈ ℕ ] (a ≡ b + c) × (1 ≤ c)
split b a (k , p) = suc k , (aeq , suc-≤-suc zero-≤)
  where aeq : a ≡ b + suc k
        aeq = sym p ∙ +-suc k b ∙ cong suc (+-comm k b) ∙ sym (+-suc b k)

-- THE INFINITE DESCENT: any positive solution yields a strictly smaller one.
descent : (a : ℕ) → Acc _<_ a → (b : ℕ) → 1 ≤ b → b < a → golden-eq a b → ⊥
descent a (acc rec) b 1≤b b<a h with split b a b<a
... | (c , a≡b+c , 1≤c) = descent b (rec b b<a) c 1≤c c<b h'
  where
    h' : golden-eq b c
    h' = descent-eq b c (subst (λ z → golden-eq z b) a≡b+c h)
    c<b : c < b
    c<b = golden-gt b c 1≤c h'

-- φ IS NOT A RATIO OF POSITIVE INTEGERS: no a,b ≥ 1 with a² = ab + b².
golden-no-pos : (a b : ℕ) → 1 ≤ a → 1 ≤ b → golden-eq a b → ⊥
golden-no-pos a b 1≤a 1≤b h = descent a (<-wellfounded a) b 1≤b (golden-gt a b 1≤b h) h
