{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SPECTRAL-RADIUS CUT (2×2) — the decidable Dedekind cut of λmax, from the PD test.
--
-- For symmetric M = [[a,b],[b,d]] the quadratic form of qI−M is
--      ⟨(qI−M)x,x⟩ = quadℚ (q−a) (−b) (q−d) x y           (PDTest2.quad on the shifted entries),
-- so "q is strictly above λmax" is exactly "qI−M is positive definite", which PDTest2 decides:
--      isUpper q  :=  0 < (q−a)  ∧  0 < ((q−a)(q−d) − (−b)²).
-- This module reads PDTest2 into the cut: `pd-forward` gives the UPPER-BOUND property
-- (isUpper q ⟹ ⟨Mx,x⟩ < q⟨x,x⟩ ∀ x≠0), and the `notPD-pivot` witnesses give the LOWER cut.
-- One PD test supplies the cut decision AND its locatedness witness — the unification.
--
module corpus.cubical_agda.Corridor.Running.General.SpecRadiusCut where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_)
open import corpus.cubical_agda.Corridor.Running.General.PDTest2
  using (quadℚ; pd-forward; notPD-pivot1; notPD-pivot2)

-- the symmetric matrix [[a,b],[b,d]].
module _ (a b d : ℚ) where

  -- ⟨(qI−M)x,x⟩ — the shifted quadratic form (a PD test target for each q).
  shiftQ : (q x y : ℚ) → ℚ
  shiftQ q x y = quadℚ (q - a) (- b) (q - d) x y

  -- the UPPER cut:  q is strictly above λmax  ⟺  qI−M positive definite  (decidable, Sylvester).
  isUpper : ℚ → Type
  isUpper q = (0 < (q - a)) × (0 < (((q - a) · (q - d)) - ((- b) · (- b))))

  -- UPPER-BOUND property:  isUpper q  ⟹  ⟨(qI−M)x,x⟩ > 0 for every x ≠ 0
  --   (equivalently ⟨Mx,x⟩ < q·⟨x,x⟩ — q dominates every Rayleigh quotient).  Via pd-forward.
  upper-bound : (q x y : ℚ) → isUpper q → (¬ (x ≡ 0)) ⊎ (¬ (y ≡ 0))
              → 0 < shiftQ q x y
  upper-bound q x y (0<qa , 0<disc) ne =
    pd-forward (q - a) (- b) (q - d) x y 0<qa 0<disc ne

  -- LOWER-cut WITNESSES:  ¬isUpper q produces an explicit vector with ⟨(qI−M)x,x⟩ ≤ 0
  --   (so q·⟨x,x⟩ ≤ ⟨Mx,x⟩: q does NOT dominate — q is below or at λmax).  Same PD test:
  --   the failing-pivot vectors of qI−M.  This is the locatedness witness for the lower cut.

  -- pivot 1 of qI−M fails (¬ 0<(q−a)):  x=(1,0).
  notUpper-pivot1 : (q : ℚ) → ¬ (0 < (q - a)) → shiftQ q 1 0 ≤ 0
  notUpper-pivot1 q ¬0<qa = notPD-pivot1 (q - a) (- b) (q - d) ¬0<qa

  -- pivot 2 fails (0<(q−a) but ¬ 0<disc):  the eigenvector witness x=(−(−b), q−a) = (b, q−a).
  notUpper-pivot2 : (q : ℚ) → 0 < (q - a)
                  → ¬ (0 < (((q - a) · (q - d)) - ((- b) · (- b))))
                  → shiftQ q (- (- b)) (q - a) ≤ 0
  notUpper-pivot2 q 0<qa ¬0<disc = notPD-pivot2 (q - a) (- b) (q - d) 0<qa ¬0<disc
