{-# OPTIONS --cubical --safe --guardedness #-}
--
-- MONOTONICITY OF THE REPEATED-SQUARING POWER — 0 ≤ a ≤ b  ⟹  a^{2^L} ≤ b^{2^L}.
--
-- A small reusable lemma for the DedekindReal packaging of the spectral radius: it makes the cut
-- up/down-closed (an upper-cut witness ‖M^{2^L}‖₁ < q^{2^L} survives raising q, etc.) and is used in
-- the located core.  Also 0 ≤ a ⟹ 0 ≤ a^{2^L}.  Pure induction on the squaring + sq-mono-≤.
--
module corpus.cubical_agda.Corridor.Running.General.QpowMono where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all; sq-mono-≤)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (qpow)

-- 0 ≤ a ⟹ 0 ≤ a^{2^L}.
0≤qpow' : (L : ℕ) (a : ℚ) → 0 ≤ a → 0 ≤ qpow L a
0≤qpow' zero    a 0≤a = 0≤a
0≤qpow' (suc L) a 0≤a = 0≤sq-all (qpow L a)

-- 0 ≤ a ≤ b ⟹ a^{2^L} ≤ b^{2^L}.
qpow-mono : (L : ℕ) (a b : ℚ) → 0 ≤ a → a ≤ b → qpow L a ≤ qpow L b
qpow-mono zero    a b 0≤a a≤b = a≤b
qpow-mono (suc L) a b 0≤a a≤b =
  sq-mono-≤ (qpow L a) (qpow L b) (0≤qpow' L a 0≤a) (qpow-mono L a b 0≤a a≤b)
