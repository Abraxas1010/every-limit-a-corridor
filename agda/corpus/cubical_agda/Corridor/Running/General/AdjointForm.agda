{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE C*-AXIOM AT THE VECTOR LEVEL — ‖Mx‖² = ⟨M*M·x, x⟩, the bridge to ‖M‖²=‖M*M‖.
--
-- The operator-norm C*-identity ‖M*M‖=‖M‖² (for ANY matrix M, not just symmetric)
-- rests on a single pointwise identity that needs NO spectral theory:
--      ⟨Mx, Mx⟩ = ⟨M*M·x, x⟩          (* = transpose, over ℝ/ℚ).
-- Because ‖M‖ = sup_{x≠0} ‖Mx‖/‖x‖, this identity gives ‖M‖² = sup ⟨M*Mx,x⟩/‖x‖²,
-- and with Cauchy–Schwarz ⟨M*Mx,x⟩ ≤ ‖M*Mx‖‖x‖ one gets ‖M‖² ≤ ‖M*M‖ ≤ ‖M‖² — the
-- C*-axiom, for arbitrary M and dimension.  This module proves the pointwise bridge
-- for n=2 over an arbitrary commutative ring (so it holds for ℚ and ℝ), generalising
-- the symmetric-2×2 results (OperatorNorm*) to ALL 2×2 matrices via M*M.  For
-- symmetric M (b=c) this is ‖Mx‖²=⟨M²x,x⟩, tying back to eigenSquared.
--
-- HONESTLY OPEN (the general n×n closure): (a) the same identity for general n needs
-- a finite-sum Fubini exchange, and (b) the sup/Cauchy–Schwarz completion needs the
-- constructive operator-norm sup (or the spectral theorem).  Neither is discharged here;
-- this is the algebraic keystone they build on.
--
module corpus.cubical_agda.Corridor.Running.General.AdjointForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver

module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)

  -- inner product and matrix-vector product, written out for n = 2.
  --   M = [[a,b],[c,d]],  x = (x₀,x₁);  (Mx)₀ = a·x₀+b·x₁,  (Mx)₁ = c·x₀+d·x₁.
  --   M*M = MᵀM = [[a²+c², ab+cd],[ab+cd, b²+d²]].

  -- ‖Mx‖² = ⟨M*M·x, x⟩  — the C*-axiom's pointwise bridge, ANY 2×2 matrix.
  adjointFormSq : (a b c d x₀ x₁ : ⟨ R ⟩)
    → (((a · x₀) + (b · x₁)) · ((a · x₀) + (b · x₁)))
    + (((c · x₀) + (d · x₁)) · ((c · x₀) + (d · x₁)))
    ≡ (x₀ · ((((a · a) + (c · c)) · x₀) + (((a · b) + (c · d)) · x₁)))
    + (x₁ · ((((a · b) + (c · d)) · x₀) + (((b · b) + (d · d)) · x₁)))
  adjointFormSq a b c d x₀ x₁ = solve! R

  -- symmetric specialisation (c = b):  M*M = M², so ‖Mx‖² = ⟨M²x, x⟩.
  -- (M² = [[a²+b², ab+bd],[ab+bd, b²+d²]].)
  adjointFormSqSym : (a b d x₀ x₁ : ⟨ R ⟩)
    → (((a · x₀) + (b · x₁)) · ((a · x₀) + (b · x₁)))
    + (((b · x₀) + (d · x₁)) · ((b · x₀) + (d · x₁)))
    ≡ (x₀ · ((((a · a) + (b · b)) · x₀) + (((a · b) + (b · d)) · x₁)))
    + (x₁ · ((((a · b) + (b · d)) · x₀) + (((b · b) + (d · d)) · x₁)))
  adjointFormSqSym a b d x₀ x₁ = solve! R
