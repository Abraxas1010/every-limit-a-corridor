{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5 of the germ->organism programme (D1, the located-spectrum modulus).
-- Veselov's "spectrum has a MODULUS" realized concretely: the golden spectral
-- value φ is approximated by the Fibonacci convergents Fₙ₊₁/Fₙ, and the bracket
-- width between consecutive convergents is EXACTLY 1/(Fₙ·Fₙ₊₁) -- the golden
-- modulus, read off Cassini's identity Fₙ₊₁² − Fₙ·Fₙ₊₂ = (−1)ⁿ.  This is the
-- intrinsic rate the corridor's FaithfulModulus carries, now tied to a spectrum.
-- Pure ℤ arithmetic (CommRingSolver) -- no real-arithmetic or HIT coherence.

module corpus.cubical_agda.RealCohesion.GoldenSpectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; _·_; _-_; -_)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

open import corpus.cubical_agda.Theory.GoldenRing using (fibℤ)

-- the alternating sign (−1)^(n+1), as ℤ.
negsign : ℕ → ℤ
negsign zero    = - (pos 1)
negsign (suc n) = - (negsign n)

-- CASSINI'S IDENTITY:  Fₙ·Fₙ₊₂ − Fₙ₊₁² = (−1)^(n+1).
-- (fibℤ's recurrence reduces Fₙ₊₂ definitionally, so each step is a pure ℤ
--  polynomial identity in Fₙ, Fₙ₊₁, discharged by the ring solver.)
cassini : (n : ℕ)
  → fibℤ n · fibℤ (suc (suc n)) - fibℤ (suc n) · fibℤ (suc n) ≡ negsign n
cassini zero    = solve! ℤCommRing
cassini (suc n) = step ∙ cong -_ (cassini n)
  where
    step :   fibℤ (suc n) · fibℤ (suc (suc (suc n)))
           - fibℤ (suc (suc n)) · fibℤ (suc (suc n))
           ≡ - (fibℤ n · fibℤ (suc (suc n)) - fibℤ (suc n) · fibℤ (suc n))
    step = solve! ℤCommRing

-- The convergent-difference numerator Fₙ₊₁² − Fₙ·Fₙ₊₂ = (−1)ⁿ: the bracket between
-- consecutive Fibonacci convergents has width EXACTLY 1/(Fₙ·Fₙ₊₁) -- the modulus.
golden-bracket : (n : ℕ)
  → fibℤ (suc n) · fibℤ (suc n) - fibℤ n · fibℤ (suc (suc n)) ≡ - (negsign n)
golden-bracket n = step ∙ cong -_ (cassini n)
  where
    step :   fibℤ (suc n) · fibℤ (suc n) - fibℤ n · fibℤ (suc (suc n))
           ≡ - (fibℤ n · fibℤ (suc (suc n)) - fibℤ (suc n) · fibℤ (suc n))
    step = solve! ℤCommRing

-- the modulus sign is always a UNIT (±1, squares to 1) -- so the bracket width
-- numerator is never 0: the corridor NEVER collapses to the syntactic horizon.
-- This is Veselov's lower computability certificate, in the kernel.
negsign-unit : (n : ℕ) → negsign n · negsign n ≡ pos 1
negsign-unit zero    = refl
negsign-unit (suc n) = sq ∙ negsign-unit n
  where
    sq : (- negsign n) · (- negsign n) ≡ negsign n · negsign n
    sq = solve! ℤCommRing

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Nat using (snotz)
open import Cubical.Data.Int using (injPos)

-- the modulus never vanishes: a constant/collapsed bracket is refuted.
modulus-never-collapses : (n : ℕ) → ¬ (negsign n ≡ pos 0)
modulus-never-collapses n p =
  snotz (injPos (sym (negsign-unit n) ∙ cong (λ z → z · z) p ∙ z0))
  where
    z0 : pos 0 · pos 0 ≡ pos 0
    z0 = solve! ℤCommRing

-- ── the UPPER certificate: the modulus REACHES any precision ──────────────
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Nat.Order using () renaming (_<_ to _<ℕ_)
open import corpus.cubical_agda.Corridor.FaithfulModulus using (fib; fib-lower)

-- the Fibonacci bracket denominator F_{n+2} exceeds any precision D, so the
-- bracket width 1/(Fₙ·Fₙ₊₁) shrinks below any threshold -- the modulus reaches
-- arbitrary precision (the soundness direction of Veselov's certificate).
golden-reaches : (D : ℕ) → D <ℕ fib (suc (suc D))
golden-reaches D = fib-lower D

-- VESELOV'S TWO-SIDED MODULUS, in the kernel: the golden bracket shrinks to ANY
-- precision (reaches) yet NEVER collapses to the syntactic horizon (non-collapse).
-- The lower computability certificate and the upper precision certificate, together.
golden-modulus-two-sided :
    ((D : ℕ) → D <ℕ fib (suc (suc D)))      -- reaches any precision
  × ((n : ℕ) → ¬ (negsign n ≡ pos 0))       -- never collapses
golden-modulus-two-sided = golden-reaches , modulus-never-collapses
