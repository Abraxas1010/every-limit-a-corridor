{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE OPERATOR-NORM C*-IDENTITY FOR ALL SYMMETRIC 2×2 (non-PSD included).
--
-- OperatorNormSpectral discharged ‖M²‖=‖M‖² for the PSD case, where the operator
-- norm IS the spectral edge specEdge(M)=((a+d)+√Δ)/2.  For a general (possibly
-- indefinite) symmetric M=[[a,b],[b,d]], the operator norm is the SPECTRAL RADIUS
--   ‖M‖ = max(|λ₊|,|λ₋|) = (|a+d| + √Δ)/2 ,   Δ = (a−d)²+4b²,
-- (the |a+d| handles tr<0).  The C*-identity holds the SAME way, because the
-- discriminant identity disc(M²)=(a+d)²·disc(M) is SIGN-AGNOSTIC: (a+d)²=|a+d|².
-- So a certified √-bracket [slo,shi] of disc(M) scales by |a+d| = absℚ(a+d) to a
-- certified √-bracket of disc(M²) — and with tr(M²)=(|a+d|²+Δ)/2 (traceM2, also
-- sign-agnostic) this gives ‖M²‖=‖M‖² for EVERY symmetric 2×2 matrix.  This closes
-- the operator-norm C*-identity beyond the principal case; only the n×n
-- generalisation now remains open.
--
module corpus.cubical_agda.Corridor.Running.General.OperatorNormMagnitude where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_,_; _×_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; ≤-·o)
open import Cubical.Data.Rationals.Properties using (·Comm)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.Corridor.Running.CertifiedSqrt using (IsSqrtBracket)
open import corpus.cubical_agda.Corridor.Running.SpectralEdge using (discriminant)
open import corpus.cubical_agda.Corridor.Running.General.OperatorNorm using (mulSquare)
open import corpus.cubical_agda.Corridor.Running.General.OperatorNormSpectral using (discriminantSquare)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (absℚ; 0≤absℚ; absℚ-sq; 0≤sq-all)

-- THE C*-IDENTITY, general symmetric 2×2: a √-bracket of disc(M) scales by |a+d|
-- to a √-bracket of disc(M²).  (The spectral RADIUS ‖M²‖ = ‖M‖² — any sign of tr.)
cstarBracketAbs : (a b d slo shi : ℚ)
  → IsSqrtBracket (discriminant a b d) slo shi
  → IsSqrtBracket (discriminant ((a · a) + (b · b)) (b · (a + d)) ((b · b) + (d · d)))
                  (absℚ (a + d) · slo) (absℚ (a + d) · shi)
cstarBracketAbs a b d slo shi (lo² , hi²) = loBound , hiBound
  where
    s discM dM2 : ℚ
    s = absℚ (a + d)
    discM = discriminant a b d
    dM2 = discriminant ((a · a) + (b · b)) (b · (a + d)) ((b · b) + (d · d))
    0≤s² : 0 ≤ (s · s)
    0≤s² = subst (0 ≤_) (sym (absℚ-sq (a + d))) (0≤sq-all (a + d))
    -- disc(M²) = (a+d)²·disc(M) = |a+d|²·disc(M).
    sq≡ : dM2 ≡ (s · s) · discM
    sq≡ = discriminantSquare a b d ∙ cong (_· discM) (sym (absℚ-sq (a + d)))
    -- lower:  (|a+d|·slo)² = |a+d|²·slo² ≤ |a+d|²·discM = disc(M²).
    loStep : ((s · s) · (slo · slo)) ≤ ((s · s) · discM)
    loStep = subst2 _≤_ (·Comm (slo · slo) (s · s)) (·Comm discM (s · s))
                        (≤-·o (slo · slo) discM (s · s) 0≤s² lo²)
    loBound : ((s · slo) · (s · slo)) ≤ dM2
    loBound = subst2 _≤_ (sym (mulSquare ℚCommRing s slo)) (sym sq≡) loStep
    -- upper:  disc(M²) = |a+d|²·discM ≤ |a+d|²·shi² = (|a+d|·shi)².
    hiStep : ((s · s) · discM) ≤ ((s · s) · (shi · shi))
    hiStep = subst2 _≤_ (·Comm discM (s · s)) (·Comm (shi · shi) (s · s))
                        (≤-·o discM (shi · shi) (s · s) 0≤s² hi²)
    hiBound : dM2 ≤ ((s · shi) · (s · shi))
    hiBound = subst2 _≤_ (sym sq≡) (sym (mulSquare ℚCommRing s shi)) hiStep
