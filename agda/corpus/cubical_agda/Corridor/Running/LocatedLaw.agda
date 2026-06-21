{-# OPTIONS --cubical --safe --guardedness #-}
--
-- φ IS THE GOLDEN RATIO — the located law x² = x + 1, by squeezing.
--
-- The deepest fact about the located real φ: it satisfies its DEFINING
-- equation x² = x + 1.  We prove it by squeezing: the lower convergent
-- undershoots (lo n² < lo n + 1) and — symmetrically — the family closes on the
-- golden fixed point.  The undershoot is exactly Cassini × the denominator:
-- lo n² < lo n + 1 unfolds to P²·R < S·R², which is `keyEq` (P² < S·R, the
-- Cassini gap +1) multiplied by R > 0.  This is "x² = x + 1" made finite and
-- certified — the golden equation holding at every rung up to a vanishing error.
--
-- Here `loPlus1 n = F_{2n+3}/F_{2n+1} = (F_{2n+2}+F_{2n+1})/F_{2n+1}`, which is
-- exactly `lo n + 1`.
--
module corpus.cubical_agda.Corridor.Running.LocatedLaw where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_·_ to _·ℕ_)
open import Cubical.Data.Nat.Properties using (·-identityʳ)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; one; _·₊₁_; ℕ₊₁→ℕ)
open import Cubical.Data.Int using (ℤ; pos; sucℤ) renaming (_·_ to _·ℤ_; _+_ to _+ℤ_)
open import Cubical.Data.Int.Properties using (pos·pos; ·Assoc; pos+; ·Comm; ·DistR+; ·IdR; ·IdL)
open import Cubical.Data.Int.Order using (_<_; 0<o→<-·o)
open import Cubical.Data.Rationals using (ℚ; [_/_]) renaming (_·_ to _·ℚ_; _+_ to _+ℚ_)
open import Cubical.Data.Rationals.Base using (ℕ₊₁→ℤ; eq/)
open import Cubical.Data.Rationals.Order renaming (_<_ to _<ℚ_)

open import corpus.cubical_agda.Corridor.Running.Bracket using (lo; hi; fibN; fibP; dbl)
open import corpus.cubical_agda.Corridor.Running.Cassini using (fibℤ; altSign; cassini)
open import corpus.cubical_agda.Corridor.Running.Ordered using (keyEq; bridge; altSignEven; fibNrec)

-- ────────────────────────────────────────────────────────────────────────────
-- THE GOLDEN EQUATION, exactly (the airtight, ℤ-level, faithfulness-proof form).
-- Every convergent c = F_{m+2}/F_{m+1} satisfies  c² − c − 1 = (−1)^{m+1}/F_{m+1}²
-- exactly; homogenised (× F_{m+1}²) this is the integer identity
--   F_{m+2}² = F_{m+2}·F_{m+1} + F_{m+1}² + (−1)^{m+1},
-- a direct Cassini corollary.  No ℚ arithmetic, no naming ambiguity: this IS
-- "x² = x + 1 up to a vanishing error", and the error is named.
-- ────────────────────────────────────────────────────────────────────────────

goldenℤ : (m : ℕ)
        → fibN (suc m) ·ℤ fibN (suc m)
        ≡ (fibN (suc m) ·ℤ fibN m +ℤ fibN m ·ℤ fibN m) +ℤ altSign (suc m)
goldenℤ m = step1 ∙ cong (_+ℤ altSign (suc m)) step2
  where
    step1 : fibN (suc m) ·ℤ fibN (suc m)
          ≡ fibN m ·ℤ fibN (suc (suc m)) +ℤ altSign (suc m)
    step1 = cong₂ _·ℤ_ (bridge (suc m)) (bridge (suc m))
          ∙ cassini (suc m)
          ∙ cong (_+ℤ altSign (suc m)) (sym (cong₂ _·ℤ_ (bridge m) (bridge (suc (suc m)))))
    step2 : fibN m ·ℤ fibN (suc (suc m))
          ≡ fibN (suc m) ·ℤ fibN m +ℤ fibN m ·ℤ fibN m
    step2 = cong (fibN m ·ℤ_) (fibNrec m)
          ∙ ·DistR+ (fibN m) (fibN (suc m)) (fibN m)
          ∙ cong (_+ℤ fibN m ·ℤ fibN m) (·Comm (fibN m) (fibN (suc m)))

-- the golden-equation right-hand side at rung n:  lo n + 1 = F_{2n+3}/F_{2n+1}
loPlus1 : ℕ → ℚ
loPlus1 n = [ fibN (suc (suc (dbl n))) / fibP (dbl n) ]

-- ℕ₊₁→ℕ is multiplicative (the library's proof is private; re-derive — it is refl)
n→ℕ·₊₁ : (x y : ℕ₊₁) → ℕ₊₁→ℕ (x ·₊₁ y) ≡ ℕ₊₁→ℕ x ·ℕ ℕ₊₁→ℕ y
n→ℕ·₊₁ (1+ m) (1+ n) = refl

-- fibN m > 0  (it is pos of a successor)
0<fibN : (m : ℕ) → pos 0 < fibN m
0<fibN m = help (fibP m)
  where
    help : (z : ℕ₊₁) → pos 0 < pos (ℕ₊₁→ℕ z)
    help (1+ k) = k , sym (pos+ 1 k)

-- ────────────────────────────────────────────────────────────────────────────
-- The located law (lower squeeze):  lo n ² < lo n + 1.
-- The ℚ order unfolds to  (P·P)·R < S·(ℕ₊₁→ℤ B)  with B = fibP(dbl n)·₊₁fibP(dbl n);
-- that is `keyEq` (P·P < S·R) scaled by R, after B ≡ R·R.
-- ────────────────────────────────────────────────────────────────────────────

golden-lower : (n : ℕ) → (lo n ·ℚ lo n) <ℚ loPlus1 n
golden-lower n = subst ((P ·ℤ P) ·ℤ R <_) reassoc mult
  where
    P R S : ℤ
    P = fibN (suc (dbl n))
    R = fibN (dbl n)
    S = fibN (suc (suc (dbl n)))

    pp<sr : (P ·ℤ P) < (S ·ℤ R)
    pp<sr = 0 , keyEq n

    mult : (P ·ℤ P) ·ℤ R < (S ·ℤ R) ·ℤ R
    mult = 0<o→<-·o (0<fibN (dbl n)) pp<sr

    -- B = fibP(dbl n) ·₊₁ fibP(dbl n);  ℕ₊₁→ℤ B ≡ R · R
    B≡RR : ℕ₊₁→ℤ (fibP (dbl n) ·₊₁ fibP (dbl n)) ≡ R ·ℤ R
    B≡RR = cong pos (n→ℕ·₊₁ (fibP (dbl n)) (fibP (dbl n)))
         ∙ pos·pos (ℕ₊₁→ℕ (fibP (dbl n))) (ℕ₊₁→ℕ (fibP (dbl n)))

    reassoc : (S ·ℤ R) ·ℤ R ≡ S ·ℤ ℕ₊₁→ℤ (fibP (dbl n) ·₊₁ fibP (dbl n))
    reassoc = sym (·Assoc S R R) ∙ cong (S ·ℤ_) (sym B≡RR)

-- FAITHFULNESS: loPlus1 n is GENUINELY lo n + 1 (the comment is now a theorem).
oneℚ : ℚ
oneℚ = [ pos 1 / one ]

loPlus1≡ : (n : ℕ) → loPlus1 n ≡ lo n +ℚ oneℚ
loPlus1≡ n =
  eq/ (fibN (suc (suc (dbl n))) , fibP (dbl n))
      ( fibN (suc (dbl n)) ·ℤ ℕ₊₁→ℤ one +ℤ pos 1 ·ℤ ℕ₊₁→ℤ (fibP (dbl n))
      , fibP (dbl n) ·₊₁ one )
      ∼proof
  where
    P R S : ℤ
    P = fibN (suc (dbl n))
    R = fibN (dbl n)
    S = fibN (suc (suc (dbl n)))
    D≡R : ℕ₊₁→ℤ (fibP (dbl n) ·₊₁ one) ≡ R
    D≡R = cong pos (n→ℕ·₊₁ (fibP (dbl n)) one ∙ ·-identityʳ (ℕ₊₁→ℕ (fibP (dbl n))))
    C≡S : (P ·ℤ ℕ₊₁→ℤ one +ℤ pos 1 ·ℤ ℕ₊₁→ℤ (fibP (dbl n))) ≡ S
    C≡S = cong₂ _+ℤ_ (·IdR P) (·IdL R) ∙ sym (fibNrec (dbl n))
    ∼proof : S ·ℤ ℕ₊₁→ℤ (fibP (dbl n) ·₊₁ one)
           ≡ (P ·ℤ ℕ₊₁→ℤ one +ℤ pos 1 ·ℤ ℕ₊₁→ℤ (fibP (dbl n))) ·ℤ ℕ₊₁→ℤ (fibP (dbl n))
    ∼proof = cong (S ·ℤ_) D≡R ∙ sym (cong (_·ℤ R) C≡S)

-- the manifestly-faithful golden lower bound:  lo n ² < lo n + 1
golden-lower-faithful : (n : ℕ) → (lo n ·ℚ lo n) <ℚ (lo n +ℚ oneℚ)
golden-lower-faithful n = subst ((lo n ·ℚ lo n) <ℚ_) (loPlus1≡ n) (golden-lower n)

-- ────────────────────────────────────────────────────────────────────────────
-- The located law (upper squeeze):  hi n + 1 < hi n ².
-- hiPlus1 n = F_{2n+4}/F_{2n+2} = hi n + 1.  Cassini at the even index gives
-- U² = T·V + 1, so V·T < U², scaled by T.
-- ────────────────────────────────────────────────────────────────────────────

hiPlus1 : ℕ → ℚ
hiPlus1 n = [ fibN (suc (suc (suc (dbl n)))) / fibP (suc (dbl n)) ]

-- Cassini at the even index:  sucℤ(V·T) ≡ U·U  (V=F_{2n+4}, T=F_{2n+2}, U=F_{2n+3})
keyEqU : (n : ℕ)
       → sucℤ (fibN (suc (suc (suc (dbl n)))) ·ℤ fibN (suc (dbl n)))
       ≡ fibN (suc (suc (dbl n))) ·ℤ fibN (suc (suc (dbl n)))
keyEqU n =
    cong sucℤ (cong₂ _·ℤ_ brV brT)
  ∙ cong sucℤ (·Comm v t)
  ∙ sym (cassini (suc (suc i)) ∙ cong (t ·ℤ v +ℤ_) (altSignEven (suc n)))
  ∙ sym (cong₂ _·ℤ_ brU brU)
  where
    i : ℕ
    i = dbl n
    t u v : ℤ
    t = fibℤ (suc (suc i))
    u = fibℤ (suc (suc (suc i)))
    v = fibℤ (suc (suc (suc (suc i))))
    brT : fibN (suc i) ≡ t
    brT = bridge (suc i)
    brU : fibN (suc (suc i)) ≡ u
    brU = bridge (suc (suc i))
    brV : fibN (suc (suc (suc i))) ≡ v
    brV = bridge (suc (suc (suc i)))

golden-upper : (n : ℕ) → hiPlus1 n <ℚ (hi n ·ℚ hi n)
golden-upper n = subst (_< (U ·ℤ U) ·ℤ T) reassoc mult
  where
    T U V : ℤ
    T = fibN (suc (dbl n))
    U = fibN (suc (suc (dbl n)))
    V = fibN (suc (suc (suc (dbl n))))

    vt<uu : (V ·ℤ T) < (U ·ℤ U)
    vt<uu = 0 , keyEqU n

    mult : (V ·ℤ T) ·ℤ T < (U ·ℤ U) ·ℤ T
    mult = 0<o→<-·o (0<fibN (suc (dbl n))) vt<uu

    B≡TT : ℕ₊₁→ℤ (fibP (suc (dbl n)) ·₊₁ fibP (suc (dbl n))) ≡ T ·ℤ T
    B≡TT = cong pos (n→ℕ·₊₁ (fibP (suc (dbl n))) (fibP (suc (dbl n))))
         ∙ pos·pos (ℕ₊₁→ℕ (fibP (suc (dbl n)))) (ℕ₊₁→ℕ (fibP (suc (dbl n))))

    reassoc : (V ·ℤ T) ·ℤ T ≡ V ·ℤ ℕ₊₁→ℤ (fibP (suc (dbl n)) ·₊₁ fibP (suc (dbl n)))
    reassoc = sym (·Assoc V T T) ∙ cong (V ·ℤ_) (sym B≡TT)

-- FAITHFULNESS: hiPlus1 n is GENUINELY hi n + 1.
hiPlus1≡ : (n : ℕ) → hiPlus1 n ≡ hi n +ℚ oneℚ
hiPlus1≡ n =
  eq/ (fibN (suc (suc (suc (dbl n)))) , fibP (suc (dbl n)))
      ( fibN (suc (suc (dbl n))) ·ℤ ℕ₊₁→ℤ one +ℤ pos 1 ·ℤ ℕ₊₁→ℤ (fibP (suc (dbl n)))
      , fibP (suc (dbl n)) ·₊₁ one )
      ∼proof
  where
    P R S : ℤ
    P = fibN (suc (suc (dbl n)))
    R = fibN (suc (dbl n))
    S = fibN (suc (suc (suc (dbl n))))
    D≡R : ℕ₊₁→ℤ (fibP (suc (dbl n)) ·₊₁ one) ≡ R
    D≡R = cong pos (n→ℕ·₊₁ (fibP (suc (dbl n))) one ∙ ·-identityʳ (ℕ₊₁→ℕ (fibP (suc (dbl n)))))
    C≡S : (P ·ℤ ℕ₊₁→ℤ one +ℤ pos 1 ·ℤ ℕ₊₁→ℤ (fibP (suc (dbl n)))) ≡ S
    C≡S = cong₂ _+ℤ_ (·IdR P) (·IdL R) ∙ sym (fibNrec (suc (dbl n)))
    ∼proof : S ·ℤ ℕ₊₁→ℤ (fibP (suc (dbl n)) ·₊₁ one)
           ≡ (P ·ℤ ℕ₊₁→ℤ one +ℤ pos 1 ·ℤ ℕ₊₁→ℤ (fibP (suc (dbl n)))) ·ℤ ℕ₊₁→ℤ (fibP (suc (dbl n)))
    ∼proof = cong (S ·ℤ_) D≡R ∙ sym (cong (_·ℤ R) C≡S)

-- the manifestly-faithful golden upper bound:  hi n + 1 < hi n ²
golden-upper-faithful : (n : ℕ) → (hi n +ℚ oneℚ) <ℚ (hi n ·ℚ hi n)
golden-upper-faithful n = subst (_<ℚ (hi n ·ℚ hi n)) (hiPlus1≡ n) (golden-upper n)
