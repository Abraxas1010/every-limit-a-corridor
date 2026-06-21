{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GOLDEN RATIO AS A LOCATED REAL — the brackets tighten, and φ is the value
-- they pin.
--
-- `Ordered.agda` proves each bracket is non-degenerate (`lo n < hi n`).  This
-- module adds the *tightening* direction: the lower convergents strictly
-- increase (`lo n < lo (suc n)`), so the family genuinely narrows from below —
-- the structural content of "the ladder is the rate" that a constant rate
-- provably fails.  Together they present φ as a `RunningGoldenBracket`: a value
-- defined by a family of certified, non-degenerate, strictly-tightening rational
-- brackets that *run* in the kernel.
--
-- The tightening gap is again +1 — a d'Ocagne identity that reduces to
-- even-Cassini; proved here by distributivity (no ring solver, since the ℤ
-- solver mishandles the `+1` that reduces to sucℤ).
--
module corpus.cubical_agda.Corridor.Running.Located where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int
  using (ℤ; pos; negsuc; sucℤ)
  renaming (_+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)
open import Cubical.Data.Int.Properties
  using (sucPred; ·Comm; +Comm; +Assoc; ·DistR+; ·DistL+; plusMinus)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Rationals.Order renaming (_<_ to _<ℚ_)

open import corpus.cubical_agda.Corridor.Running.Bracket using (lo; hi; width; fibN; fibP; dbl)
open import corpus.cubical_agda.Corridor.Running.Cassini using (fibℤ; altSign; cassini)
open import corpus.cubical_agda.Corridor.Running.Ordered using (bridge; altSignOdd; lo<hi)

-- ────────────────────────────────────────────────────────────────────────────
-- The lower convergents strictly increase: `lo n < lo (suc n)`.
-- Unfolds (ℚ order) to `sucℤ P ≡ Q` with
--   P = F_{2n+2}·F_{2n+3},  Q = F_{2n+4}·F_{2n+1}.
-- ────────────────────────────────────────────────────────────────────────────

keyEqLo : (n : ℕ)
        → sucℤ (fibN (suc (dbl n)) ·ℤ fibN (suc (suc (dbl n))))
        ≡ fibN (suc (suc (suc (dbl n)))) ·ℤ fibN (dbl n)
keyEqLo n = cong sucℤ (cong₂ _·ℤ_ br1 br2) ∙ core ∙ sym (cong₂ _·ℤ_ br3 br0)
  where
    i : ℕ
    i = dbl n
    a x : ℤ
    a = fibℤ (suc i)      -- F_{2n+2}, a genuine neutral atom
    x = fibℤ i            -- F_{2n+1}, a genuine neutral atom
    y z w : ℤ
    y = a +ℤ x            -- F_{2n+3} = fibℤ (suc (suc i))
    z = y +ℤ a            -- F_{2n+4} = fibℤ (suc (suc (suc i)))
    w = z +ℤ y            -- F_{2n+5} = fibℤ (suc (suc (suc (suc i))))

    br0 : fibN i ≡ a
    br0 = bridge i
    br1 : fibN (suc i) ≡ y
    br1 = bridge (suc i)
    br2 : fibN (suc (suc i)) ≡ z
    br2 = bridge (suc (suc i))
    br3 : fibN (suc (suc (suc i))) ≡ w
    br3 = bridge (suc (suc (suc i)))

    -- Cassini at the odd index:  y² = a·z − 1.
    casEq : y ·ℤ y ≡ a ·ℤ z +ℤ negsuc 0
    casEq = cassini (suc i) ∙ cong (a ·ℤ z +ℤ_) (altSignOdd n)

    -- Q distributes: w·a = (z+y)·a = a·z + y·a.
    QdistA : w ·ℤ a ≡ a ·ℤ z +ℤ (y ·ℤ a)
    QdistA = ·DistL+ z y a ∙ cong (_+ℤ (y ·ℤ a)) (·Comm z a)

    rearr : (a ·ℤ z +ℤ negsuc 0) +ℤ (y ·ℤ a) ≡ (a ·ℤ z +ℤ (y ·ℤ a)) +ℤ negsuc 0
    rearr = sym (+Assoc (a ·ℤ z) (negsuc 0) (y ·ℤ a))
          ∙ cong (a ·ℤ z +ℤ_) (+Comm (negsuc 0) (y ·ℤ a))
          ∙ +Assoc (a ·ℤ z) (y ·ℤ a) (negsuc 0)

    -- P = y·z = y·(y+a) = y² + y·a = (a·z − 1) + y·a = (a·z + y·a) − 1 = w·a − 1.
    P'≡ : y ·ℤ z ≡ (w ·ℤ a) +ℤ negsuc 0
    P'≡ = ·DistR+ y y a
        ∙ cong (_+ℤ (y ·ℤ a)) casEq
        ∙ rearr
        ∙ cong (_+ℤ negsuc 0) (sym QdistA)

    -- sucℤ(w·a − 1) = w·a  (the `+ negsuc 0` reduces to predℤ, killed by sucPred).
    core : sucℤ (y ·ℤ z) ≡ w ·ℤ a
    core = cong sucℤ P'≡ ∙ sucPred (w ·ℤ a)

lo↗ : (n : ℕ) → lo n <ℚ lo (suc n)
lo↗ n = 0 , keyEqLo n

-- ────────────────────────────────────────────────────────────────────────────
-- The upper convergents strictly decrease: `hi (suc n) < hi n`.
-- Unfolds to `sucℤ P ≡ Q` with P = F_{2n+5}·F_{2n+2}, Q = F_{2n+3}·F_{2n+4}.
-- The d'Ocagne gap is again +1: z·w − v·y = a·z − y² = +1 (Cassini, odd index).
-- ────────────────────────────────────────────────────────────────────────────

keyEqHi : (n : ℕ)
        → sucℤ (fibN (suc (suc (suc (suc (dbl n))))) ·ℤ fibN (suc (dbl n)))
        ≡ fibN (suc (suc (dbl n))) ·ℤ fibN (suc (suc (suc (dbl n))))
keyEqHi n = cong sucℤ (cong₂ _·ℤ_ brV brY) ∙ core ∙ sym (cong₂ _·ℤ_ brZ brW)
  where
    i : ℕ
    i = dbl n
    a x : ℤ
    a = fibℤ (suc i)
    x = fibℤ i
    y z w v : ℤ
    y = a +ℤ x            -- F_{2n+3}
    z = y +ℤ a            -- F_{2n+4}
    w = z +ℤ y            -- F_{2n+5}
    v = w +ℤ z            -- F_{2n+6}  (numerator of hi (suc n))

    brY : fibN (suc i) ≡ y
    brY = bridge (suc i)
    brZ : fibN (suc (suc i)) ≡ z
    brZ = bridge (suc (suc i))
    brW : fibN (suc (suc (suc i))) ≡ w
    brW = bridge (suc (suc (suc i)))
    brV : fibN (suc (suc (suc (suc i)))) ≡ v
    brV = bridge (suc (suc (suc (suc i))))

    casEq : y ·ℤ y ≡ a ·ℤ z +ℤ negsuc 0
    casEq = cassini (suc i) ∙ cong (a ·ℤ z +ℤ_) (altSignOdd n)

    -- pure ring:  v·y = z·w + (y² − a·z)
    ringHi : v ·ℤ y ≡ z ·ℤ w +ℤ (y ·ℤ y +ℤ (-ℤ (a ·ℤ z)))
    ringHi = solve! ℤCommRing

    -- (M + k) + (−M) = k
    cancelL : (M k : ℤ) → (M +ℤ k) +ℤ (-ℤ M) ≡ k
    cancelL M k = cong (_+ℤ (-ℤ M)) (+Comm M k) ∙ plusMinus M k

    cancel : y ·ℤ y +ℤ (-ℤ (a ·ℤ z)) ≡ negsuc 0
    cancel = cong (_+ℤ (-ℤ (a ·ℤ z))) casEq ∙ cancelL (a ·ℤ z) (negsuc 0)

    P'hi : v ·ℤ y ≡ z ·ℤ w +ℤ negsuc 0
    P'hi = ringHi ∙ cong (z ·ℤ w +ℤ_) cancel

    core : sucℤ (v ·ℤ y) ≡ z ·ℤ w
    core = cong sucℤ P'hi ∙ sucPred (z ·ℤ w)

hi↘ : (n : ℕ) → hi (suc n) <ℚ hi n
hi↘ n = 0 , keyEqHi n

-- ────────────────────────────────────────────────────────────────────────────
-- φ as a running located golden bracket.
-- ────────────────────────────────────────────────────────────────────────────

record RunningGoldenBracket : Type where
  constructor running-golden-bracket
  field
    lower upper : ℕ → ℚ
    -- every rung is genuinely non-degenerate (Cassini gap +1):
    nondegenerate : (n : ℕ) → lower n <ℚ upper n
    -- the lower convergents strictly increase and the upper strictly decrease —
    -- the family is genuinely NESTED and tightens (a constant rate fails this):
    tightening    : (n : ℕ) → lower n <ℚ lower (suc n)
    narrowing     : (n : ℕ) → upper (suc n) <ℚ upper n

open RunningGoldenBracket public

φ : RunningGoldenBracket
φ = running-golden-bracket lo hi lo<hi lo↗ hi↘
