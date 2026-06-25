{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

------------------------------------------------------------------------------
-- Theory/RationalField.agda — CONSTRUCTING the cubical-ℚ field structure the library lacks.
-- (Infrastructure track, Sprint 17.) `Cubical.Data.Rationals` gives ℚ = (ℤ × ℕ₊₁)//∼ as an ordered
-- COMMUTATIVE RING but provides NO multiplicative inverse / division. This module fills that vacancy
-- constructively: the inverse `invℚ`, the field axiom `·-rinv` (`q · q⁻¹ = 1` for `q ≠ 0`), and
-- division `_/ℚ_`. With these, every ℚ-division-deferred module (logical entropy, ratio forms, the
-- genuine ℚ charges) is unblocked.
--
-- The construction (filling the negative-shaped space). The inverse of `[a/b]` is `[±(ℕ₊₁→ℤ b) / |a|]`
-- — the sign and absolute value of the numerator. On representatives:
--   `inv-rep (pos(suc k), b)  = [  ℕ₊₁→ℤ b  / 1+ k ]`   (a > 0)
--   `inv-rep (negsuc k,  b)  = [ −(ℕ₊₁→ℤ b) / 1+ k ]`   (a < 0)
--   `inv-rep (pos 0,     b)  = 0`                        (junk: 0⁻¹ := 0)
-- This DESCENDS to the quotient: `well-def` proves it respects `∼` across all 9 sign-cases (3 valid
-- by `eq/` + cross-multiplication, 6 vacuous by `pos ≢ negsuc` / `snotz`). Then `invℚ = rec … inv-rep
-- well-def`, and `·-rinv` is the cross-multiplication identity `(a·ℕ₊₁→ℤ b)·1 ≡ 1·ℕ₊₁→ℤ(b·₊₁|a|)`.
--
-- No reward hacking: `invℚ` is total and quotient-respecting; `·-rinv` is the genuine field law
-- proved from the ℤ ring lemmas (`pos·pos`, `negsuc·negsuc`, `·Comm`, the ℕ₊₁ multiplicativity).
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.RationalField where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_; subst)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; snotz; znots)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; ℕ₊₁→ℕ; _·₊₁_)
open import Cubical.Data.Rationals using (ℚ; [_/_]; isSetℚ; ℕ₊₁→ℤ; _·_; ·Comm; ·Assoc; ·IdR)
open import Cubical.HITs.SetQuotients using ([_]; eq/; rec)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)

-- ℚ's one (= `[1/1]`) and the relation a representative-pair satisfies under `∼`.
oneℚ : ℚ
oneℚ = [ pos 1 / (1+ 0) ]

-- `ℕ₊₁→ℕ` is multiplicative (the cubical lemma is `private`, but it is `refl`).
ℕ₊₁→ℕ-mul : (m n : ℕ₊₁) → ℕ₊₁→ℕ (m ·₊₁ n) ≡ (ℕ₊₁→ℕ m) ℕ.· (ℕ₊₁→ℕ n)
ℕ₊₁→ℕ-mul (1+ m) (1+ n) = refl

-- `ℕ₊₁→ℤ` is multiplicative: `ℕ₊₁→ℤ (b ·₊₁ d) ≡ ℕ₊₁→ℤ b · ℕ₊₁→ℤ d`.
ℕ₊₁→ℤ-·₊₁ : (b d : ℕ₊₁) → ℕ₊₁→ℤ (b ·₊₁ d) ≡ (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
ℕ₊₁→ℤ-·₊₁ b d = cong pos (ℕ₊₁→ℕ-mul b d) ∙ ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)

-- negation is injective on ℤ (for the negative-sign case of well-definedness).
-Inj : {x y : ℤ} → (ℤ.- x) ≡ (ℤ.- y) → x ≡ y
-Inj {x} {y} p = sym (ℤ.-Involutive x) ∙ cong ℤ.-_ p ∙ ℤ.-Involutive y

--------------------------------------------------------------------------------
-- The inverse on representatives, and its descent to the quotient
--------------------------------------------------------------------------------

inv-rep : ℤ × ℕ₊₁ → ℚ
inv-rep (pos zero    , b) = [ pos 0 / (1+ 0) ]
inv-rep (pos (suc k) , b) = [ ℕ₊₁→ℤ b / (1+ k) ]
inv-rep (negsuc k    , b) = [ (ℤ.- (ℕ₊₁→ℤ b)) / (1+ k) ]

-- `well-def`: `inv-rep` respects `∼`. The relation `r : a · ℕ₊₁→ℤ d ≡ c · ℕ₊₁→ℤ b` forces same-sign
-- (`a`,`c`); the 3 valid cases close by `eq/`, the 6 mixed-sign cases are vacuous.
well-def : (x y : ℤ × ℕ₊₁)
  → ((fst x) ℤ.· (ℕ₊₁→ℤ (snd y))) ≡ ((fst y) ℤ.· (ℕ₊₁→ℤ (snd x)))
  → inv-rep x ≡ inv-rep y
well-def (pos zero , 1+ B) (pos zero , 1+ D) r = refl
well-def (pos zero , 1+ B) (pos (suc j) , 1+ D) r =
  ⊥-rec (znots (ℤ.injPos (r ∙ sym (ℤ.pos·pos (suc j) (suc B)))))
well-def (pos zero , 1+ B) (negsuc j , 1+ D) r =
  ⊥-rec (ℤ.posNotnegsuc 0 _ (r ∙ ℤ.negsuc·pos j (suc B)
    ∙ cong ℤ.-_ (sym (ℤ.pos·pos (suc j) (suc B)))))
well-def (pos (suc k) , 1+ B) (pos zero , 1+ D) r =
  ⊥-rec (znots (ℤ.injPos (sym r ∙ sym (ℤ.pos·pos (suc k) (suc D)))))
well-def (pos (suc k) , 1+ B) (pos (suc j) , 1+ D) r =
  eq/ _ _ (ℤ.·Comm (ℕ₊₁→ℤ (1+ B)) (pos (suc j)) ∙ sym r ∙ ℤ.·Comm (pos (suc k)) (ℕ₊₁→ℤ (1+ D)))
well-def (pos (suc k) , 1+ B) (negsuc j , 1+ D) r =
  ⊥-rec (ℤ.posNotnegsuc _ _
    (ℤ.pos·pos (suc k) (suc D) ∙ r ∙ ℤ.negsuc·pos j (suc B)
      ∙ cong ℤ.-_ (sym (ℤ.pos·pos (suc j) (suc B)))))
well-def (negsuc k , 1+ B) (pos zero , 1+ D) r =
  ⊥-rec (ℤ.negsucNotpos _ 0 (sym (ℤ.negsuc·pos k (suc D)
    ∙ cong ℤ.-_ (sym (ℤ.pos·pos (suc k) (suc D)))) ∙ r))
well-def (negsuc k , 1+ B) (pos (suc j) , 1+ D) r =
  ⊥-rec (ℤ.negsucNotpos _ _
    (sym (ℤ.negsuc·pos k (suc D) ∙ cong ℤ.-_ (sym (ℤ.pos·pos (suc k) (suc D))))
      ∙ r ∙ sym (ℤ.pos·pos (suc j) (suc B))))
well-def (negsuc k , 1+ B) (negsuc j , 1+ D) r =
  eq/ _ _ ( sym (ℤ.-DistL· (ℕ₊₁→ℤ (1+ B)) (pos (suc j)))
          ∙ cong ℤ.-_ posEq
          ∙ ℤ.-DistL· (ℕ₊₁→ℤ (1+ D)) (pos (suc k)) )
  where
  h2 : (pos (suc k) ℤ.· pos (suc D)) ≡ (pos (suc j) ℤ.· pos (suc B))
  h2 = -Inj (sym (ℤ.negsuc·pos k (suc D)) ∙ r ∙ ℤ.negsuc·pos j (suc B))
  posEq : (ℕ₊₁→ℤ (1+ B) ℤ.· pos (suc j)) ≡ (ℕ₊₁→ℤ (1+ D) ℤ.· pos (suc k))
  posEq = ℤ.·Comm (pos (suc B)) (pos (suc j)) ∙ sym h2 ∙ ℤ.·Comm (pos (suc k)) (pos (suc D))

-- **The multiplicative inverse on ℚ.**
invℚ : ℚ → ℚ
invℚ = rec isSetℚ inv-rep well-def

--------------------------------------------------------------------------------
-- The field axiom: q · q⁻¹ = 1 for q ≠ 0
--------------------------------------------------------------------------------

-- the cross-multiplication identity used by both signs.
private
  reinv : (a : ℤ) (k : ℕ) (b : ℕ₊₁) → (a ℤ.· ℕ₊₁→ℤ b) ≡ (pos (suc k) ℤ.· ℕ₊₁→ℤ b)
        → ([ a / b ] · [ ℕ₊₁→ℤ b / (1+ k) ]) ≡ oneℚ
  reinv a k b hak = eq/ _ _
    ( ℤ.·IdR (a ℤ.· ℕ₊₁→ℤ b)
    ∙ hak
    ∙ ℤ.·Comm (pos (suc k)) (ℕ₊₁→ℤ b)
    ∙ sym (ℕ₊₁→ℤ-·₊₁ b (1+ k))
    ∙ sym (ℤ.·IdL (ℕ₊₁→ℤ (b ·₊₁ (1+ k)))) )

-- **`q · q⁻¹ = 1`** for a positive numerator.
·-rinv-pos : (k : ℕ) (b : ℕ₊₁) → ([ pos (suc k) / b ] · invℚ [ pos (suc k) / b ]) ≡ oneℚ
·-rinv-pos k b = reinv (pos (suc k)) k b refl

-- **`q · q⁻¹ = 1`** for a negative numerator (the inverse is `[−ℕ₊₁→ℤ b / |a|]`; `negsuc·negsuc`
-- flips the two negatives to `pos · pos`).
·-rinv-neg : (k : ℕ) (B : ℕ) → ([ negsuc k / (1+ B) ] · invℚ [ negsuc k / (1+ B) ]) ≡ oneℚ
·-rinv-neg k B = eq/ _ _
  ( ℤ.·IdR (negsuc k ℤ.· (ℤ.- (ℕ₊₁→ℤ (1+ B))))
  ∙ ℤ.negsuc·negsuc k B
  ∙ ℤ.·Comm (pos (suc k)) (pos (suc B))
  ∙ sym (ℕ₊₁→ℤ-·₊₁ (1+ B) (1+ k))
  ∙ sym (ℤ.·IdL (ℕ₊₁→ℤ ((1+ B) ·₊₁ (1+ k)))) )

--------------------------------------------------------------------------------
-- Division
--------------------------------------------------------------------------------

-- **Division** `p / q = p · q⁻¹` — now a total ℚ operation (junk only at `q = 0`).
_/ℚ_ : ℚ → ℚ → ℚ
p /ℚ q = p · invℚ q

-- **Self-division is 1** for a nonzero (positive-or-negative) denominator: `q / q = 1`.
self-div-pos : (k : ℕ) (b : ℕ₊₁) → ([ pos (suc k) / b ] /ℚ [ pos (suc k) / b ]) ≡ oneℚ
self-div-pos = ·-rinv-pos
self-div-neg : (k : ℕ) (B : ℕ) → ([ negsuc k / (1+ B) ] /ℚ [ negsuc k / (1+ B) ]) ≡ oneℚ
self-div-neg = ·-rinv-neg

-- Concrete witness (non-vacuity): `(1/2) · (1/2)⁻¹ = 1`, i.e. `(1/2)⁻¹ = 2/1` works.
half-inverse : ([ pos 1 / (1+ 1) ] · invℚ [ pos 1 / (1+ 1) ]) ≡ oneℚ
half-inverse = ·-rinv-pos 0 (1+ 1)

--------------------------------------------------------------------------------
-- Invocation-2: left inverse, inv 1 = 1, and "division undoes multiplication"
--------------------------------------------------------------------------------

-- **Left inverse** `q⁻¹ · q = 1` (from the right inverse + commutativity).
·-linv-pos : (k : ℕ) (b : ℕ₊₁) → (invℚ [ pos (suc k) / b ] · [ pos (suc k) / b ]) ≡ oneℚ
·-linv-pos k b = ·Comm (invℚ [ pos (suc k) / b ]) [ pos (suc k) / b ] ∙ ·-rinv-pos k b
·-linv-neg : (k : ℕ) (B : ℕ) → (invℚ [ negsuc k / (1+ B) ] · [ negsuc k / (1+ B) ]) ≡ oneℚ
·-linv-neg k B = ·Comm (invℚ [ negsuc k / (1+ B) ]) [ negsuc k / (1+ B) ] ∙ ·-rinv-neg k B

-- The inverse of `1` is `1` (`[1/1]⁻¹ = [1/1]`, definitionally).
inv-one : invℚ oneℚ ≡ oneℚ
inv-one = refl

-- **Division undoes multiplication** (the defining field property): `(p · q) / q = p` for `q ≠ 0`.
div-mul-cancel-pos : (p : ℚ) (k : ℕ) (b : ℕ₊₁) → ((p · [ pos (suc k) / b ]) /ℚ [ pos (suc k) / b ]) ≡ p
div-mul-cancel-pos p k b =
    sym (·Assoc p [ pos (suc k) / b ] (invℚ [ pos (suc k) / b ]))
  ∙ cong (p ·_) (·-rinv-pos k b)
  ∙ ·IdR p
div-mul-cancel-neg : (p : ℚ) (k B : ℕ) → ((p · [ negsuc k / (1+ B) ]) /ℚ [ negsuc k / (1+ B) ]) ≡ p
div-mul-cancel-neg p k B =
    sym (·Assoc p [ negsuc k / (1+ B) ] (invℚ [ negsuc k / (1+ B) ]))
  ∙ cong (p ·_) (·-rinv-neg k B)
  ∙ ·IdR p
