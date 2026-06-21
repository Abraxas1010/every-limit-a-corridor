{-# OPTIONS --cubical --safe --guardedness #-}

-- ════════════════════════════════════════════════════════════════════════════
-- THE CORRIDOR ORGANISM — capstone of the germ→organism programme.
--
-- The paper "Every Limit a Corridor" carried three honest-scope disclaimers; this
-- module bundles their constructive answers (all kernel-checked, postulate-free):
--
--   D3  shape ≠ flat, proven only on a 2-point model
--        → proven on the genuine analytic real line ℝ          (shape≠flat-on-ℝ)
--   D1  the corridor is a "germ"
--        → the golden value φ is a genuine LOCATED REAL, IRRATIONAL, with an
--          apart conjugate ψ, bracketed by Fibonacci convergents at the golden
--          modulus rate                                        (φ, ψ, φ#ψ, golden-no-ℤ)
--   D2  the AF object is a skeleton of finite SETS
--        → genuine matrix *-algebras + AF inductive limit + a COMMUTATIVE AF
--          C*-algebra with the full C*-norm (C*-identity, submult, triangle,
--          isometric inclusions)                               (A∞, cstar-identity, …)
-- ════════════════════════════════════════════════════════════════════════════

module corpus.cubical_agda.RealCohesion.CorridorOrganism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Relation.Nullary using (¬_)

open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; _<ℝ_; _#ℝ_)
open import corpus.cubical_agda.RealCohesion.GoldenCut using (φ)
open import corpus.cubical_agda.RealCohesion.GoldenConjugate using (ψ; φ#ψ)
open import corpus.cubical_agda.RealCohesion.GoldenIrrationalZ using (golden-eqℤ; golden-no-ℤ)
open import corpus.cubical_agda.RealCohesion.GoldenLocated using (conv-below; conv-above)

-- D1 CAPSTONE: the located golden pair (φ, ψ : ℝ), apart, TOGETHER WITH the
-- irrationality of the golden recurrence.  Faithful-scope note: the last conjunct
-- is the INTEGER-RATIO statement (a²=aB+B² has no solution with B=pos(suc bn)>0) --
-- mathematically the irrationality of the golden value that φ is the located root
-- of.  The FORMAL "φ #ℝ ι q for EVERY q" link is the remaining ℚ-level obligation
-- (needs SetQuotient denominator-clearing); this Σ does not claim it.  See
-- φ≢conv32/φ≢conv53 below for the genuine typed φ≠ι q instances.
golden-spectrum-complete :
  Σ[ x ∈ ℝ ] Σ[ y ∈ ℝ ]
      (x #ℝ y)                                                   -- φ and ψ are apart
    × ((a : ℤ) (bn : ℕ) → ¬ golden-eqℤ a (pos (suc bn)))         -- a²=aB+B² has no
                                                                  -- integer-ratio soln
golden-spectrum-complete = φ , ψ , φ#ψ , golden-no-ℤ

-- D1 CAPSTONE (location): φ is strictly between consecutive Fibonacci convergents
-- 3/2 and 5/3 in ℝ -- the located value with its golden-modulus bracket.
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ι)
open import corpus.cubical_agda.RealCohesion.RealOrder using (<ℝ-irrefl)
open import corpus.cubical_agda.RealCohesion.GoldenLocated using (conv32; conv53)

φ-located-in-bracket : (ι conv32 <ℝ φ) × (φ <ℝ ι conv53)
φ-located-in-bracket = conv-below , conv-above

-- φ:ℝ is FORMALLY distinct from the bracketing rationals 3/2 and 5/3 -- genuine
-- typed φ≠ι q instances, from the strict bracket + irreflexivity of <ℝ.
φ≢conv32 : ¬ (ι conv32 ≡ φ)
φ≢conv32 p = <ℝ-irrefl φ (subst (_<ℝ φ) p conv-below)

φ≢conv53 : ¬ (φ ≡ ι conv53)
φ≢conv53 p = <ℝ-irrefl φ (subst (φ <ℝ_) (sym p) conv-above)

-- D3 CAPSTONE: shape ≠ flat on the genuine analytic real line.
open import corpus.cubical_agda.RealCohesion.ShapeNullification using (shape≠flat-on-ℝ) public

-- D2 CAPSTONE: the commutative AF C*-algebra C(Fin n) with its FULL norm structure,
-- and the proper AF tower with its two-sided golden modulus.
open import corpus.cubical_agda.RealCohesion.DiagonalCStar
  using (‖_‖; cstar-identity; submult; norm-triangle; norm-definite; ιD-isometric) public
open import corpus.cubical_agda.RealCohesion.GoldenAFAlgebra
  using (A∞; ★∞; golden-tower-proper) public
open import corpus.cubical_agda.RealCohesion.GoldenSpectrum
  using (golden-modulus-two-sided) public

-- the whole organism is re-exported through this single module.
