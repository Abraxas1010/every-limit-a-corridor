{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE BRACKET IS NON-DEGENERATE FOR EVERY RUNG — `lo n < hi n` for all n.
--
-- `Bracket.agda` shows the bracket *runs* on concrete inputs (reduction certs).
-- This module promotes that to a GENERAL theorem: for every precision rung n the
-- interval is genuinely ordered, `lo n < hi n`.  This is exactly where Cassini
-- pays off — the signed gap between the two convergents is +1, so the strict
-- inequality is `sucℤ P ≡ Q`.  It is the substitution-test-passing non-vacuity
-- the landed corridor lacked: true for all n, not just the rungs checked by refl.
--
module corpus.cubical_agda.Corridor.Running.Ordered where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; +-suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; _+₁_; ℕ₊₁→ℕ)
open import Cubical.Data.Int
  using (ℤ; pos; negsuc; sucℤ; predℤ)
  renaming (_+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)
open import Cubical.Data.Int.Properties using (pos+; -Involutive; sucPred; ·Comm)
open import Cubical.Data.Int.Order using (_≤_; _<_)
open import Cubical.Data.Rationals.Order renaming (_<_ to _<ℚ_)

open import corpus.cubical_agda.Corridor.Running.Bracket
  using (lo; hi; fibN; fibP; dbl)
open import corpus.cubical_agda.Corridor.Running.Cassini
  using (fibℤ; altSign; cassini)

-- ────────────────────────────────────────────────────────────────────────────
-- Bridge: the bracket's ℕ₊₁-ladder agrees with Cassini's ℤ-ladder (shifted by 1)
--   fibN m = F_{m+1} = fibℤ (suc m)
-- ────────────────────────────────────────────────────────────────────────────

n→ℕ+₁ : (x y : ℕ₊₁) → ℕ₊₁→ℕ (x +₁ y) ≡ ℕ₊₁→ℕ x +ℕ ℕ₊₁→ℕ y
n→ℕ+₁ (1+ p) (1+ q) = cong suc (sym (+-suc p q))

fibNrec : (m : ℕ) → fibN (suc (suc m)) ≡ fibN (suc m) +ℤ fibN m
fibNrec m = cong pos (n→ℕ+₁ (fibP (suc m)) (fibP m))
          ∙ pos+ (ℕ₊₁→ℕ (fibP (suc m))) (ℕ₊₁→ℕ (fibP m))

bridge : (m : ℕ) → fibN m ≡ fibℤ (suc m)
bridge zero          = refl
bridge (suc zero)    = refl
bridge (suc (suc m)) = fibNrec m ∙ cong₂ _+ℤ_ (bridge (suc m)) (bridge m)

-- ────────────────────────────────────────────────────────────────────────────
-- The Cassini sign at an even index is +1; at the odd successor it is −1.
-- ────────────────────────────────────────────────────────────────────────────

altSignEven : (n : ℕ) → altSign (dbl n) ≡ pos 1
altSignEven zero    = refl
altSignEven (suc n) = -Involutive (altSign (dbl n)) ∙ altSignEven n

altSignOdd : (n : ℕ) → altSign (suc (dbl n)) ≡ negsuc 0
altSignOdd n = cong -ℤ_ (altSignEven n)

-- ────────────────────────────────────────────────────────────────────────────
-- The key equation: sucℤ P ≡ Q, with
--   P = fibN(2n+1)·fibN(2n+1)   (lo's cross term)
--   Q = fibN(2n+2)·fibN(2n)     (hi's cross term)
-- i.e. the convergent gap is exactly +1 — the Cassini payoff.
-- ────────────────────────────────────────────────────────────────────────────

keyEq : (n : ℕ)
      → sucℤ (fibN (suc (dbl n)) ·ℤ fibN (suc (dbl n)))
      ≡ fibN (suc (suc (dbl n))) ·ℤ fibN (dbl n)
keyEq n =
    cong sucℤ ( cong₂ _·ℤ_ B B
              ∙ cassini (suc i)
              ∙ cong (M +ℤ_) (altSignOdd n) )
  ∙ sucPred M
  ∙ sym Q≡M
  where
    i : ℕ
    i = dbl n
    A = bridge i
    B = bridge (suc i)
    C = bridge (suc (suc i))
    M : ℤ
    M = fibℤ (suc i) ·ℤ fibℤ (suc (suc (suc i)))
    Q≡M : fibN (suc (suc i)) ·ℤ fibN i ≡ M
    Q≡M = cong₂ _·ℤ_ C A ∙ ·Comm (fibℤ (suc (suc (suc i)))) (fibℤ (suc i))

-- ────────────────────────────────────────────────────────────────────────────
-- The general non-vacuity theorem.  `lo n < hi n` unfolds (ℚ order on the two
-- `[_/_]` points) to the ℤ inequality `sucℤ P ≤ Q = Σ k, sucℤ P +pos k ≡ Q`;
-- the witness is k = 0 and `keyEq`.
-- ────────────────────────────────────────────────────────────────────────────

lo<hi : (n : ℕ) → lo n <ℚ hi n
lo<hi n = 0 , keyEq n
