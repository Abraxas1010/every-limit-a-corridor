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
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd; Σ-syntax)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_; yes; no)
open import corpus.cubical_agda.Corridor.Running.General.PDTest2
  using (quad; quad10; quadℚ; pd-forward; notPD-pivot1; notPD-pivot2)

-- the shift-difference identity over any commutative ring (placed BEFORE the ℚ open so
-- `open CommRingStr` doesn't clash with ℚ's `_-_`):
--   ⟨((p)I−M)x,x⟩ − ⟨((q)I−M)x,x⟩ = (p−q)·‖x‖²   (M fixed).  A pure `solve!` identity.
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  shiftDiffR : (p q a b d x y : ⟨ R ⟩)
    → quad R (p - a) (- b) (p - d) x y
    ≡ (quad R (q - a) (- b) (q - d) x y) + ((p - q) · ((x · x) + (y · y)))
  shiftDiffR p q a b d x y = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; <Dec; ≮→≥; <-+o; <-·o; ≤-+o; ≤Monotone+; isRefl≤; isTrans<≤; isTrans≤<)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all)

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

  -- local ℚ-order helpers (PDTest2's are private).
  private
    0<·0<' : (m n : ℚ) → 0 < m → 0 < n → 0 < (m · n)
    0<·0<' m n 0<m 0<n = subst (_< (m · n)) (·AnnihilL n) (<-·o 0 m n 0<n 0<m)
    negpos : (m n : ℚ) → m < 0 → 0 < n → (m · n) < 0
    negpos m n m<0 0<n = subst ((m · n) <_) (·AnnihilL n) (<-·o m 0 n 0<n m<0)
    nn+pos' : (m n : ℚ) → 0 ≤ m → 0 < n → 0 < (m + n)
    nn+pos' m n 0≤m 0<n = isTrans<≤ 0 n (m + n) 0<n
                            (subst (_≤ (m + n)) (+IdL n) (≤Monotone+ 0 m n n 0≤m (isRefl≤ n)))
    le0+lt0 : (m n : ℚ) → m ≤ 0 → n < 0 → (m + n) < 0
    le0+lt0 m n m≤0 n<0 = isTrans≤< (m + n) n 0
                            (subst ((m + n) ≤_) (+IdL n) (≤-+o m 0 n m≤0)) n<0

  -- the shift-difference, specialised to THIS matrix at ℚ.
  shiftDiff : (p q x y : ℚ) → shiftQ p x y ≡ (shiftQ q x y) + ((p - q) · ((x · x) + (y · y)))
  shiftDiff p q x y = shiftDiffR ℚCommRing p q a b d x y

  -- ── THE LOCATEDNESS:  p < q  ⟹  isUpper q  OR  an explicit witness puts p below λmax. ──
  located : (p q : ℚ) → p < q
          → isUpper q ⊎ (Σ[ x ∈ ℚ ] Σ[ y ∈ ℚ ] (shiftQ p x y < 0))
  located p q p<q with <Dec 0 (q - a)
  ... | no ¬0<qa = inr (1 , 0 , shiftP<0)
    where
      pa<0 : (p - a) < 0
      pa<0 = isTrans<≤ (p - a) (q - a) 0 (<-+o p q (- a) p<q) (≮→≥ 0 (q - a) ¬0<qa)
      shiftP<0 : shiftQ p 1 0 < 0
      shiftP<0 = subst (_< 0) (sym (quad10 ℚCommRing (p - a) (- b) (p - d))) pa<0
  ... | yes 0<qa with <Dec 0 (((q - a) · (q - d)) - ((- b) · (- b)))
  ...   | yes 0<disc = inl (0<qa , 0<disc)
  ...   | no ¬0<disc = inr (- (- b) , q - a , shiftP<0)
    where
      nrm : ℚ
      nrm = ((- (- b)) · (- (- b))) + ((q - a) · (q - a))
      0<nrm : 0 < nrm
      0<nrm = nn+pos' ((- (- b)) · (- (- b))) ((q - a) · (q - a))
                      (0≤sq-all (- (- b))) (0<·0<' (q - a) (q - a) 0<qa 0<qa)
      p-q<0 : (p - q) < 0
      p-q<0 = subst ((p - q) <_) (+Comm q (- q) ∙ +InvL q) (<-+o p q (- q) p<q)
      shiftP<0 : shiftQ p (- (- b)) (q - a) < 0
      shiftP<0 = subst (_< 0) (sym (shiftDiff p q (- (- b)) (q - a)))
                   (le0+lt0 (shiftQ q (- (- b)) (q - a)) ((p - q) · nrm)
                            (notUpper-pivot2 q 0<qa ¬0<disc)
                            (negpos (p - q) nrm p-q<0 0<nrm))
