{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE CASSINI GAP — loPlus1 n = lo n² + 1/fibP(2n)², the EXACT golden defect, hence the gap → 0.
--
-- "lo n ↑ φ" (Item A converse) needs the lower convergents to approach φ with no floor.  The defect
-- of the golden equation at rung n, loPlus1 n − lo n², is EXACTLY 1/D² (D = fibP(dbl n)): Cassini's
-- identity S·R − P² = 1 (keyEq, sucℤ(P²) ≡ S·R) read in ℚ.  Since D = fibP(dbl n) is unbounded
-- (Forcing), 1/D² → 0, so f(lo n) = lo n²−lo n = 1 − 1/D² ↑ 1 — the convergents fill φ's cut.
--
module corpus.cubical_agda.Corridor.Running.General.GapBound where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; zero)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; _·₊₁_)
open import Cubical.Data.Int using (ℤ; pos; sucℤ) renaming (_·_ to _·ℤ_; _+_ to _+ℤ_)
open import Cubical.Data.Int.Properties renaming (·DistL+ to ·DistL+ℤ)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Properties using (·CancelR)
open import corpus.cubical_agda.Corridor.Running.Bracket using (lo; fibN; fibP; dbl)
open import corpus.cubical_agda.Corridor.Running.LocatedLaw using (loPlus1)
open import corpus.cubical_agda.Corridor.Running.Ordered using (keyEq)

-- sucℤ x ≡ x + pos 1  (cubical Int:  x + pos 1 = sucℤ (x + pos 0) = sucℤ x).
sucℤ≡+1 : (x : ℤ) → (x +ℤ pos 1) ≡ sucℤ x
sucℤ≡+1 x = refl

module _ (n : ℕ) where
  private
    P R S : ℤ
    P = fibN (suc (dbl n))
    R = fibN (dbl n)
    S = fibN (suc (suc (dbl n)))
    D : ℕ₊₁
    D = fibP (dbl n)
    DD : ℕ₊₁
    DD = D ·₊₁ D
    E : ℤ
    E = ℕ₊₁→ℤ DD

  -- loPlus1 n = [S/D] ≡ [sucℤ(P·P)/D²]  (expand by D, then Cassini keyEq).
  loP1-form : loPlus1 n ≡ [ sucℤ (P ·ℤ P) / DD ]
  loP1-form = sym (·CancelR {S} {D} D) ∙ cong (λ z → [ z / DD ]) (sym (keyEq n))

  -- lo n² + 1/D² ≡ [sucℤ(P·P)/D²]  (combine same denominator, distribute, cancel).
  loSq-form : ((lo n · lo n) + [ pos 1 / DD ]) ≡ [ sucℤ (P ·ℤ P) / DD ]
  loSq-form =
      cong (λ z → [ z / (DD ·₊₁ DD) ]) (sym (·DistL+ℤ (P ·ℤ P) (pos 1) E))
    ∙ ·CancelR {(P ·ℤ P) +ℤ pos 1} {DD} DD
    ∙ cong (λ z → [ z / DD ]) (sucℤ≡+1 (P ·ℤ P))

  -- THE GAP IDENTITY:  loPlus1 n = lo n² + 1/D².
  gapForm : loPlus1 n ≡ ((lo n · lo n) + [ pos 1 / DD ])
  gapForm = loP1-form ∙ sym loSq-form
