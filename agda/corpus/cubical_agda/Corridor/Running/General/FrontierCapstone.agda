{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE FRONTIER CAPSTONE — joint typecheck of the whole located-reals frontier (the integration proof).
--
-- Importing the leaves forces the entire dependency tree (≈55 modules) to typecheck together under one
-- --safe, postulate-free compilation: items A (running≅Dedekind), B (metallic/√D), C (spectral radius +
-- faithfulness), C2/C3 (the full operator norm), F (spectral edges), and E (entropy observables).  Its
-- successful compilation IS the integration proof.
--
module corpus.cubical_agda.Corridor.Running.General.FrontierCapstone where

-- A: the running corridor IS the Dedekind point (one cut, two presentations).
open import corpus.cubical_agda.Corridor.Running.General.Cofinal using (running≅dedekind)
-- B: every quadratic irrational as a located real (metallic ratios + √D).
open import corpus.cubical_agda.Corridor.Running.General.MetallicReal using (metallic; sqrtCorridor)
-- C: the spectral radius of a symmetric matrix as a located real, faithful to the operator-norm cut.
open import corpus.cubical_agda.Corridor.Running.General.SpecRadiusReal using (specRadius)
open import corpus.cubical_agda.Corridor.Running.General.SpecRadiusFaithful using (U-sound)
-- C2/C3: the FULL operator norm of ANY rational matrix (non-symmetric) = √ρ(MᵀM).
open import corpus.cubical_agda.Corridor.Running.General.OperatorNormReal using (operatorNorm)
open import corpus.cubical_agda.Corridor.Running.General.SqrtRealR using (sqrtRealℝ)
-- F: the spectral edge λ₊ of a symmetric 2×2 as a located real.
open import corpus.cubical_agda.Corridor.Running.General.SpectralEdgeReal using (specEdge)
-- E: the corridor's logical-entropy observables (the catalogue row).
open import corpus.cubical_agda.Corridor.Running.General.CorridorObservables using (the-corridor)
-- Z[φ] frontier foundation: the golden field Q[φ] ↪ ℝ as located reals (a+bφ, decidable via φ's law).
open import corpus.cubical_agda.Corridor.Running.General.AffineReal using (affineℝ)
open import corpus.cubical_agda.Corridor.Running.General.ZPhiReal using (zphiReal; negℝ)
-- located-real arithmetic: the approximation lemma + addition (located reals as an ordered field).
open import corpus.cubical_agda.Corridor.Running.General.ApproxReal using (approxℝ)
open import corpus.cubical_agda.Corridor.Running.General.AddReal using (addℝ)
-- Z[φ] matrix layer reached: the 2×2 Z[φ] symmetric spectral edge (tr+√Δ)/2 as a located real.
open import corpus.cubical_agda.Corridor.Running.General.ZPhiSpectralEdge using (zphiSpecEdge)
-- Z[φ] matrix algebra: the pair arithmetic proven faithful to Z[φ] multiplication (n×n op-norm foundation).
open import corpus.cubical_agda.Corridor.Running.General.ZPhiMatrix using (zφMul; zφSq; faithful)
-- THE n×n Z[φ] OPERATOR NORM: ‖M‖=√ρ(M̃ᵀM̃) via the regular representation, a located real for any n.
open import corpus.cubical_agda.Corridor.Running.General.ZPhiOperatorNorm using (zphiHouseNorm; regRep)





