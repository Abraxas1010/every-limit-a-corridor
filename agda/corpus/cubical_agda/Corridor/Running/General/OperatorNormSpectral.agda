{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE OPERATOR-NORM C*-IDENTITY, OPERATIONALLY — ‖M²‖ = ‖M‖² at the certified bracket.
--
-- Combining OperatorNorm's two ring identities with Phase F's certified spectral-edge
-- bisection, this proves the C*-identity for the PSD symmetric 2×2 operator norm in
-- the form that actually RUNS: a certified √-bracket [slo,shi] of disc(M) scales by
-- (a+d) to a certified √-bracket [(a+d)·slo, (a+d)·shi] of disc(M²).  Since
-- specEdge(M)=((a+d)+√disc(M))/2 and specEdge(M²)=(tr(M²)+√disc(M²))/2, and
-- √disc(M²)=(a+d)·√disc(M) (from dM2), the M² edge bracket is exactly the M edge
-- bracket squared — ‖M²‖ = ‖M‖², certified to any depth.  This discharges the
-- paper's named-open piece for the PSD symmetric 2×2 case.
--
module corpus.cubical_agda.Corridor.Running.General.OperatorNormSpectral where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_,_; _×_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; ≤-·o)
open import Cubical.Data.Rationals.Properties using (·Comm)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.Corridor.Running.CertifiedSqrt using (IsSqrtBracket)
open import corpus.cubical_agda.Corridor.Running.SpectralEdge using (discriminant)
open import corpus.cubical_agda.Corridor.Running.General.OperatorNorm using (discM2; mulSquare)

-- (i) the ℚ-level discriminant identity — disc(M²) = (a+d)²·disc(M) — tying C to F.
discriminantSquare : (a b d : ℚ)
  → discriminant ((a · a) + (b · b)) (b · (a + d)) ((b · b) + (d · d))
  ≡ ((a + d) · (a + d)) · discriminant a b d
discriminantSquare = discM2 ℚCommRing

-- (ii) THE C*-IDENTITY, certified-bracket form: a √-bracket of disc(M) scales by (a+d)
-- to a √-bracket of disc(M²).  (The spectral edge of M² is the spectral edge of M,
-- squared — ‖M²‖ = ‖M‖² — for the PSD symmetric 2×2 case.)
cstarBracket : (a b d slo shi : ℚ) → 0 ≤ ((a + d) · (a + d))
  → IsSqrtBracket (discriminant a b d) slo shi
  → IsSqrtBracket (discriminant ((a · a) + (b · b)) (b · (a + d)) ((b · b) + (d · d)))
                  ((a + d) · slo) ((a + d) · shi)
cstarBracket a b d slo shi 0≤s² (lo² , hi²) = loBound , hiBound
  where
    s discM dM2 : ℚ
    s = a + d
    discM = discriminant a b d
    dM2 = discriminant ((a · a) + (b · b)) (b · (a + d)) ((b · b) + (d · d))
    sq≡ : dM2 ≡ (s · s) · discM
    sq≡ = discriminantSquare a b d
    -- lower:  (s·slo)² = (s·s)·slo² ≤ (s·s)·discM = disc(M²).
    loStep : ((s · s) · (slo · slo)) ≤ ((s · s) · discM)
    loStep = subst2 _≤_ (·Comm (slo · slo) (s · s)) (·Comm discM (s · s))
                        (≤-·o (slo · slo) discM (s · s) 0≤s² lo²)
    loBound : ((s · slo) · (s · slo)) ≤ dM2
    loBound = subst2 _≤_ (sym (mulSquare ℚCommRing s slo)) (sym sq≡) loStep
    -- upper:  disc(M²) = (s·s)·discM ≤ (s·s)·shi² = (s·shi)².
    hiStep : ((s · s) · discM) ≤ ((s · s) · (shi · shi))
    hiStep = subst2 _≤_ (·Comm discM (s · s)) (·Comm (shi · shi) (s · s))
                        (≤-·o discM (shi · shi) (s · s) 0≤s² hi²)
    hiBound : dM2 ≤ ((s · shi) · (s · shi))
    hiBound = subst2 _≤_ (sym sq≡) (sym (mulSquare ℚCommRing s shi)) hiStep
