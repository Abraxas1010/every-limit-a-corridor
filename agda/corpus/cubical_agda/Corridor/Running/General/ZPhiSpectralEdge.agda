{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SPECTRAL EDGE OF A 2×2 Z[φ] MATRIX — zphiSpecEdge : ℝ, the first Z[φ]-coefficient operator-norm result.
--
-- For a symmetric matrix over the golden integers, [[a+bφ, c+dφ],[c+dφ, e+fφ]], the larger eigenvalue is
--      λ₊ = (tr + √Δ)/2,   tr = (a+e)+(b+f)φ,   Δ = (A−E)² + 4C²  ∈ Z[φ],
-- and Δ = Δₐ + Δ_b·φ with Δₐ, Δ_b RATIONAL (reduce φ²=φ+1).  Every piece is a located real now: tr and
-- Δ are golden integers (zphiReal), √Δ is the located square root of a located real (sqrtRealℝ), the sum
-- tr +ℝ √Δ is located-real addition (addℝ), and the halving is a rational affine map (affineℝ ½ 0).  So
-- the spectral edge of a Z[φ] matrix is itself a located real — the Z[φ] coefficient frontier, reached
-- concretely in the 2×2 case by composing the located-real ordered field with the golden embedding.
-- (Δ ≥ 0 for a real symmetric matrix; the positive upper bound on Δ that √ needs is supplied as input.)
--
module corpus.cubical_agda.Corridor.Running.General.ZPhiSpectralEdge where

open import Cubical.Data.Rationals
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; half; 0<half)
open import corpus.cubical_agda.Corridor.Running.General.SqrtRealR using (sqrtRealℝ; PosUpper)
open import corpus.cubical_agda.Corridor.Running.General.AffineReal using (affineℝ)
open import corpus.cubical_agda.Corridor.Running.General.AddReal using (addℝ)
open import corpus.cubical_agda.Corridor.Running.General.ZPhiReal using (zphiReal)

module _ (a b c d e f : ℚ) where

  -- trace  tr = (a+e) + (b+f)φ   ∈ Z[φ].
  traceℤφ : ℝ
  traceℤφ = zphiReal (a + e) (b + f)

  -- discriminant  Δ = (A−E)² + 4C² = Δₐ + Δ_b·φ,  Δₐ,Δ_b ∈ ℚ (φ²=φ+1).
  Δa Δb : ℚ
  Δa = (((a + (- e)) · (a + (- e))) + ((b + (- f)) · (b + (- f))))
     + (4 · ((c · c) + (d · d)))
  Δb = ((2 · ((a + (- e)) · (b + (- f)))) + ((b + (- f)) · (b + (- f))))
     + (4 · ((2 · (c · d)) + (d · d)))

  discℤφ : ℝ
  discℤφ = zphiReal Δa Δb

  -- λ₊ = (tr + √Δ)/2,  a located real.  posΔ : a positive rational upper bound for Δ (always exists).
  zphiSpecEdge : PosUpper discℤφ → ℝ
  zphiSpecEdge posΔ =
    affineℝ half 0 0<half (addℝ traceℤφ (sqrtRealℝ discℤφ posΔ))
