{-# OPTIONS --cubical --safe --guardedness #-}
--
-- POSITIVE-DEFINITENESS TEST, 2×2 — the constructive heart of the spectral-radius cut.
--
-- For symmetric M = [[a,b],[b,d]] the quadratic form is  Q(x,y) = a x² + 2b xy + d y².
-- The square-root-free Cholesky (LDLᵀ) certificate, cleared of its one division, is the
-- SUM-OF-SQUARES identity
--        a · Q(x,y) = (a x + b y)² + (a d − b²) · y²,
-- a pure ring identity (`solve!`).  It makes the 2×2 Sylvester criterion *constructive*:
--   • PD  ⟸  0 < a ∧ 0 < ad−b²   (the SOS is a positive combination of squares);
--   • ¬PD ⟹ an explicit WITNESS vector x≠0 with Q(x) ≤ 0   (from the failing pivot).
-- This is the n=2 instance of the general LDLᵀ mechanism; it specialises the cut decision
-- to `0<a ∧ 0<ad−b²`, matching the landed 2×2 edge result, and is division-free so it ports
-- to ℚ unchanged.  (n=3 and the general Schur recursion follow the same SOS pattern.)
--
module corpus.cubical_agda.Corridor.Running.General.PDTest2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- ── the SOS identity over any commutative ring ──────────────────────────────
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)

  -- ⟨Mx,x⟩ for symmetric M=[[a,b],[b,d]] at x=(x,y):  a·x² + b·xy + b·xy + d·y².
  quad : (a b d x y : ⟨ R ⟩) → ⟨ R ⟩
  quad a b d x y = (a · (x · x)) + (((b · (x · y)) + (b · (x · y))) + (d · (y · y)))

  -- the LDLᵀ / sum-of-squares certificate:  a·Q = (a x + b y)² + (a d − b²)·y².
  sosId : (a b d x y : ⟨ R ⟩)
        → (a · quad a b d x y)
        ≡ (((a · x) + (b · y)) · ((a · x) + (b · y)))
            + (((a · d) - (b · b)) · (y · y))
  sosId a b d x y = solve! R

  -- witness reductions (ring identities feeding the two non-PD branches):
  --   Q(1,0) = a            (first pivot a ≤ 0  ⟹  x=(1,0) fails)
  --   a·Q(−b,a) = (ad−b²)·a²  (second pivot ≤ 0 ⟹ x=(−b,a) fails: the (a x+b y) square is 0)
  quad10 : (a b d : ⟨ R ⟩) → quad a b d 1r 0r ≡ a
  quad10 a b d = solve! R
  sosWitB : (a b d : ⟨ R ⟩)
          → (a · quad a b d (- b) a) ≡ (((a · d) - (b · b)) · (a · a))
  sosWitB a b d = solve! R

-- ── instantiated to ℚ (the bridge ⟨ ℚCommRing ⟩ ≡ ℚ, ops definitional) ──────
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; ≤-·o; ≤-·o-cancel; ≮→≥)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all)

quadℚ : (a b d x y : ℚ) → ℚ
quadℚ = quad ℚCommRing

sosℚ : (a b d x y : ℚ)
     → (a · quadℚ a b d x y)
     ≡ (((a · x) + (b · y)) · ((a · x) + (b · y))) + (((a · d) - (b · b)) · (y · y))
sosℚ = sosId ℚCommRing

-- ── the decidable 2×2 PD criterion: 0<a ∧ 0<ad−b².  Here: the WITNESS direction ──
-- ¬PD produces an explicit nonzero vector with ⟨Mx,x⟩ ≤ 0 — exactly the locatedness
-- witness for the lower cut of the spectral radius (cut-decision ⊕ witness, one source).

-- pivot 1 fails (¬ 0<a):  x = (1,0) gives Q = a ≤ 0.
notPD-pivot1 : (a b d : ℚ) → ¬ (0 < a) → quadℚ a b d 1 0 ≤ 0
notPD-pivot1 a b d ¬0<a =
  subst (_≤ 0) (sym (quad10 ℚCommRing a b d)) (≮→≥ 0 a ¬0<a)

-- pivot 2 fails (0<a but ¬ 0<ad−b²):  x = (−b,a) gives Q ≤ 0 (the first square vanishes).
notPD-pivot2 : (a b d : ℚ) → 0 < a → ¬ (0 < ((a · d) - (b · b)))
             → quadℚ a b d (- b) a ≤ 0
notPD-pivot2 a b d 0<a ¬0<disc =
  ≤-·o-cancel (quadℚ a b d (- b) a) 0 a 0<a quadA≤0A
  where
    disc≤0 : ((a · d) - (b · b)) ≤ 0
    disc≤0 = ≮→≥ 0 ((a · d) - (b · b)) ¬0<disc
    -- (ad−b²)·a² ≤ 0·a² = 0
    rhs≤0 : (((a · d) - (b · b)) · (a · a)) ≤ 0
    rhs≤0 = subst (((a · d) - (b · b)) · (a · a) ≤_) (·AnnihilL (a · a))
              (≤-·o ((a · d) - (b · b)) 0 (a · a) (0≤sq-all a) disc≤0)
    -- a·Q(−b,a) = (ad−b²)·a² ≤ 0
    aQuad≤0 : (a · quadℚ a b d (- b) a) ≤ 0
    aQuad≤0 = subst (_≤ 0) (sym (sosWitB ℚCommRing a b d)) rhs≤0
    -- transport to Q·a ≤ 0·a for the cancellation
    quadA≤0A : (quadℚ a b d (- b) a · a) ≤ (0 · a)
    quadA≤0A = subst2 _≤_ (·Comm a (quadℚ a b d (- b) a)) (sym (·AnnihilL a)) aQuad≤0
