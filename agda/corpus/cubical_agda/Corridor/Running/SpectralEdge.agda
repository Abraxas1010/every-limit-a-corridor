{-# OPTIONS --cubical --safe --guardedness #-}
--
-- CERTIFIED SPECTRAL EDGE of a symmetric 2×2 rational matrix [[a,b],[b,d]].
-- The larger eigenvalue is  λ₊ = (a+d+√Δ)/2,  Δ = (a−d)² + 4b²  (the discriminant
-- of the characteristic polynomial λ²−(a+d)λ+(ad−b²)).  Feeding Δ to the certified
-- bisection √ (CertifiedSqrt) yields a rational interval [slo,shi] with slo²≤Δ≤shi²,
-- hence  (a+d+slo)/2 ≤ λ₊ ≤ (a+d+shi)/2  — a certified, running bracket of the
-- spectral edge to demanded depth.  Demo: [[2,1],[1,1]] has Δ=5, λ₊=(3+√5)/2 = φ²,
-- tying the spectral edge back to the golden ratio (DedekindBridge / LocatedLaw).
--
module corpus.cubical_agda.Corridor.Running.SpectralEdge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_)
open import corpus.cubical_agda.Corridor.Running.CertifiedSqrt using (IsSqrtBracket; sqrtBracket)

private
  half : ℚ
  half = [ pos 1 / 1+ 1 ]

-- discriminant Δ = (a−d)² + 4b²  of the characteristic polynomial.
discriminant : (a b d : ℚ) → ℚ
discriminant a b d = ((a - d) · (a - d)) + (4 · (b · b))

-- the certified spectral-edge bracket: λ₊ ∈ [loλ, hiλ], with the √Δ certificate.
--   loλ = (a+d+slo)·½,  hiλ = (a+d+shi)·½,  and slo² ≤ Δ ≤ shi².
specEdgeBracket : (a b d : ℚ) → 0 ≤ discriminant a b d → (D : ℕ)
  → Σ[ loλ ∈ ℚ ] Σ[ hiλ ∈ ℚ ]
      Σ[ slo ∈ ℚ ] Σ[ shi ∈ ℚ ]
        IsSqrtBracket (discriminant a b d) slo shi
        × (loλ ≡ ((a + d) + slo) · half)
        × (hiλ ≡ ((a + d) + shi) · half)
specEdgeBracket a b d 0≤Δ D =
  let s = sqrtBracket (discriminant a b d) 0≤Δ D
      slo = fst s
      shi = fst (snd s)
      cert = snd (snd s)
  in ((a + d) + slo) · half
   , ((a + d) + shi) · half
   , slo , shi
   , cert , refl , refl
