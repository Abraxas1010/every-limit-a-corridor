{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE LOCATED-REAL COMPLETION — the framework the spectral-radius residue inhabits.
--
-- Both routes to the operator-norm C*-identity (spectral via DiagonalCStar, Gelfand via
-- traces) reduce to ONE residue: constructing the spectral radius as a LOCATED REAL — the
-- limit of a bounded monotone rational sequence with a modulus.  The corridor already has
-- this structure φ-specifically (Located.RunningGoldenBracket); this module generalises it
-- to a reusable `LocatedReal` (nested rational brackets) and proves the located reals are
-- CLOSED UNDER SQUARING — the exact operation ‖M²‖=‖M‖² needs — reusing the organism's
-- `sq-mono` (squaring is strictly monotone on ℚ≥0).  This reduces the whole spectral-theorem
-- residue to a single obligation: "the spectral radius is a LocatedReal" (its bracket), with
-- squaring (hence the C*-identity's structural content) already discharged here.
--
module corpus.cubical_agda.Corridor.Running.General.LocatedReal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isTrans≤<; <Weaken≤; isTrans<)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (sq-mono)
open import corpus.cubical_agda.Corridor.Running.Bracket renaming (lo to gLo; hi to gHi)
open import corpus.cubical_agda.Corridor.Running.Ordered using (lo<hi)
open import corpus.cubical_agda.Corridor.Running.Located using (lo↗; hi↘)

-- a constructive located real: nested, strictly-tightening rational brackets.
record LocatedReal : Type where
  constructor located
  field
    lo hi : ℕ → ℚ
    nondeg : (n : ℕ) → lo n < hi n          -- every rung is a genuine interval
    inc    : (n : ℕ) → lo n < lo (suc n)     -- lower bounds strictly increase
    dec    : (n : ℕ) → hi (suc n) < hi n     -- upper bounds strictly decrease
open LocatedReal public

-- the located/Cauchy modulus: the bracket can be made narrower than any positive ε.
Converges : LocatedReal → Type
Converges r = (ε : ℚ) → 0 < ε → Σ[ N ∈ ℕ ] ((hi r N - lo r N) < ε)

-- the corridor's golden ratio φ is a located real (the canonical instance).
goldenLocated : LocatedReal
goldenLocated = located gLo gHi lo<hi lo↗ hi↘

-- 0 ≤ hi n for a nonneg located real (0 ≤ lo n < hi n).
private
  0≤hi-of : (r : LocatedReal) → ((n : ℕ) → 0 ≤ lo r n) → (n : ℕ) → 0 ≤ hi r n
  0≤hi-of r 0≤lo n = <Weaken≤ 0 (hi r n) (isTrans≤< 0 (lo r n) (hi r n) (0≤lo n) (nondeg r n))

-- ── LOCATED REALS ARE CLOSED UNDER SQUARING (the C*-identity's structural operation) ──
-- For a NON-NEGATIVE located real r (0 ≤ lo r n), the squared brackets (lo², hi²) form a
-- located real — strict monotonicity preserved by `sq-mono`.  This is r² as a located real.
locatedSquare : (r : LocatedReal) → ((n : ℕ) → 0 ≤ lo r n) → LocatedReal
locatedSquare r 0≤lo = located
  (λ n → lo r n · lo r n)
  (λ n → hi r n · hi r n)
  (λ n → sq-mono (lo r n) (hi r n) (0≤lo n) (nondeg r n))
  (λ n → sq-mono (lo r n) (lo r (suc n)) (0≤lo n) (inc r n))
  (λ n → sq-mono (hi r (suc n)) (hi r n) (0≤hi-of r 0≤lo (suc n)) (dec r n))
