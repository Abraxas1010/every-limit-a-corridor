{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE RUNNING CORRIDOR — a certified rational bracket that EXECUTES.
--
-- The landed corridor (`Corridor/FaithfulModulus.agda`) carries a modulus over ℕ
-- (`width n = fib (n+2)`) but never a *real* bracket: no ℚ interval, no target.
-- This module fills that negative space.  For a precision rung `n` it returns a
-- genuine rational interval `[ lo n , hi n ] ⊆ ℚ` of consecutive golden
-- convergents bracketing the golden ratio φ, and — the whole point of an
-- *effective* limit — the interval **reduces in the kernel** to a concrete pair
-- of rationals.  The reduction certificates at the bottom (`lo-1`, `hi-1`, …)
-- are proved by `refl`: they are the in-kernel evidence that "a limit you can
-- run" is literal, not rhetorical.
--
-- Indexing (even Cassini, no parity branching):
--   lo n = F_{2n+2} / F_{2n+1}   (a lower convergent, < φ)
--   hi n = F_{2n+3} / F_{2n+2}   (an upper convergent, > φ)
-- so the signed width hi n − lo n is always +1/(F_{2n+1}·F_{2n+2}) > 0, and
-- n = 1 gives [3/2, 5/3] of width 1/(F₃·F₄) = 1/6 — exactly the paper's value.
--
module corpus.cubical_agda.Corridor.Running.Bracket where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; _+₁_; ℕ₊₁→ℕ; one)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.Rationals using (ℚ; [_/_]; _-_)

-- ────────────────────────────────────────────────────────────────────────────
-- Fibonacci built directly in ℕ₊₁ (positive by construction — these are the
-- bracket denominators, which must never be zero).  fibP m represents F_{m+1}:
--   fibP 0 = F₁ = 1, fibP 1 = F₂ = 1, fibP 2 = F₃ = 2, fibP 3 = F₄ = 3, …
-- ────────────────────────────────────────────────────────────────────────────

fibP : ℕ → ℕ₊₁
fibP zero          = one
fibP (suc zero)    = one
fibP (suc (suc m)) = fibP (suc m) +₁ fibP m

-- the numerator view of the same ladder (one source of truth ⇒ no mismatch)
fibN : ℕ → ℤ
fibN m = pos (ℕ₊₁→ℕ (fibP m))

-- double, kept structural so the brackets reduce
dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

-- ────────────────────────────────────────────────────────────────────────────
-- The running certified bracket.
-- ────────────────────────────────────────────────────────────────────────────

-- lo n = F_{2n+2}/F_{2n+1} = fibN (suc (dbl n)) / fibP (dbl n)
lo : ℕ → ℚ
lo n = [ fibN (suc (dbl n)) / fibP (dbl n) ]

-- hi n = F_{2n+3}/F_{2n+2} = fibN (suc (suc (dbl n))) / fibP (suc (dbl n))
hi : ℕ → ℚ
hi n = [ fibN (suc (suc (dbl n))) / fibP (suc (dbl n)) ]

-- ────────────────────────────────────────────────────────────────────────────
-- KERNEL-REDUCTION CERTIFICATES (HC5: "it runs").  Each is proved by `refl`,
-- i.e. the bracket genuinely computes to the stated concrete rational in the
-- Agda kernel — the constructive content a classical `ℝ` cannot deliver.
-- ────────────────────────────────────────────────────────────────────────────

-- rung 0 : [1, 2]
lo-0 : lo 0 ≡ [ pos 1 / one ]
lo-0 = refl

hi-0 : hi 0 ≡ [ pos 2 / one ]
hi-0 = refl

-- rung 1 : [3/2, 5/3]  — the paper's bracket, width 1/6
lo-1 : lo 1 ≡ [ pos 3 / (1+ 1) ]
lo-1 = refl

hi-1 : hi 1 ≡ [ pos 5 / (1+ 2) ]
hi-1 = refl

-- rung 2 : [8/5, 13/8]
lo-2 : lo 2 ≡ [ pos 8 / (1+ 4) ]
lo-2 = refl

hi-2 : hi 2 ≡ [ pos 13 / (1+ 7) ]
hi-2 = refl

-- ────────────────────────────────────────────────────────────────────────────
-- THE CASSINI-EXACT WIDTH, COMPUTING.  width n = hi n − lo n reduces in the
-- kernel to exactly 1/(F_{2n+1}·F_{2n+2}) — the paper's claimed value, run.
-- ────────────────────────────────────────────────────────────────────────────

width : ℕ → ℚ
width n = hi n - lo n

-- width 0 = 1/(F₁·F₂) = 1/1
width-0 : width 0 ≡ [ pos 1 / one ]
width-0 = refl

-- width 1 = 1/(F₃·F₄) = 1/6   — the paper's value, kernel-reduced
width-1 : width 1 ≡ [ pos 1 / (1+ 5) ]
width-1 = refl

-- width 2 = 1/(F₅·F₆) = 1/40
width-2 : width 2 ≡ [ pos 1 / (1+ 39) ]
width-2 = refl
