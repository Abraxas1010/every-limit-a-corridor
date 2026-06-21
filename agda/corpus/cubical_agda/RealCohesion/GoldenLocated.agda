{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5/6 capstone: φ:ℝ (the located spectral value, D1) is BRACKETED in ℝ by
-- consecutive Fibonacci convergents 3/2 and 5/3, and the bracket width is EXACTLY
-- 1/6 = 1/(F₃·F₄) -- the golden modulus.  This unifies the located VALUE (D1) with
-- the two-sided MODULUS (the rate): the spectrum is located, and its locating
-- sequence is the golden convergents with the Fibonacci rate.  No postulates.

module corpus.cubical_agda.RealCohesion.GoldenLocated where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <Dec)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; ι; _<ℝ_)
open import corpus.cubical_agda.RealCohesion.GoldenCut using (φ)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _  = a
  getYes (no  _) ()

-- consecutive Fibonacci convergents around φ: 3/2 = F₄/F₃, 5/3 = F₅/F₄.
conv32 conv85 conv138 conv53 : ℚ
conv32  = [ pos 3  / 1+ 1 ]   -- 3/2
conv85  = [ pos 8  / 1+ 4 ]   -- 8/5  (3/2 < 8/5 < φ)
conv138 = [ pos 13 / 1+ 7 ]   -- 13/8 (φ < 13/8 < 5/3)
conv53  = [ pos 5  / 1+ 2 ]   -- 5/3

-- 3/2 lies BELOW φ in ℝ: the witness 8/5 is above 3/2 and (8/5)²<8/5+1 (8/5 < φ).
conv-below : ι conv32 <ℝ φ
conv-below =
  ∣ conv85
  , ( getYes (<Dec conv32 conv85) tt
    , ∣ inr (getYes (<Dec (conv85 · conv85) (conv85 + 1)) tt) ∣₁ ) ∣₁

-- 5/3 lies ABOVE φ in ℝ: the witness 13/8 is below 5/3 and above φ (13/8+1<(13/8)²).
conv-above : φ <ℝ ι conv53
conv-above =
  ∣ conv138
  , ( ( getYes (<Dec 1 conv138) tt
      , getYes (<Dec (conv138 + 1) (conv138 · conv138)) tt )
    , getYes (<Dec conv138 conv53) tt ) ∣₁

-- THE BRACKET WIDTH IS THE GOLDEN MODULUS: 5/3 − 3/2 = 1/6 = 1/(F₃·F₄).
golden-modulus-bracket : (conv53 + (- conv32)) ≡ [ pos 1 / 1+ 5 ]
golden-modulus-bracket = getYes (discreteℚ (conv53 + (- conv32)) [ pos 1 / 1+ 5 ]) tt
