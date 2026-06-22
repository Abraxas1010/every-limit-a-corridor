{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE C*-IDENTITY AT THE CUT LEVEL (2×2):  ‖M²‖ = ‖M‖²  as a coincidence of spectral cuts.
--
-- For symmetric M=[[a,b],[b,d]], the spectral-radius cut of ‖M²‖ at a rational square r² is
-- isPD(r²I−M²), and the cut of ‖M‖² at r² is isNorm_M(r) = isPD(rI−M) ∧ isPD(rI+M)  (q>‖M‖
-- ⟺ both rI∓M PD).  The C*-identity is exactly that these coincide for r>0:
--        isPD(r²I − M²)  ⟺  isPD(rI − M) ∧ isPD(rI + M).
-- KEYSTONE (no eigenvectors, no √, no trisect-n):  determinant MULTIPLICATIVITY
--        det(r²I − M²) = det(rI − M) · det(rI + M),
-- a pure `solve!` ring identity that holds for ANY n (the part that generalizes).  The 2×2
-- first-minor/PD bookkeeping is finished with ℚ-order (det>0 ∧ trace>0 ⟺ PD).
--
module corpus.cubical_agda.Corridor.Running.General.CStarLocated where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- determinant multiplicativity  det(r²I−M²) = det(rI−M)·det(rI+M)  (any commutative ring).
-- (placed before the ℚ open so `open CommRingStr` doesn't clash with ℚ's `_-_`.)
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  -- (the rI−M factor's off-diagonal is −b, so its det uses (−b)·(−b), matching isPD2's disc.)
  detMultR : (r a b d : ⟨ R ⟩)
    → ((((r · r) - ((a · a) + (b · b))) · ((r · r) - ((b · b) + (d · d))))
         - ((- (b · (a + d))) · (- (b · (a + d)))))
    ≡ ((((r - a) · (r - d)) - ((- b) · (- b))) · (((r + a) · (r + d)) - (b · b)))
  detMultR r a b d = solve! R

  -- first-minor of r²I−M² split two ways (so its positivity follows from a single pivot):
  --   r²−a²−b² = (a+d)(r−a) + det(rI−M)  =  −(a+d)(r+a) + det(rI+M).
  fm1R : (r a b d : ⟨ R ⟩)
    → ((r · r) - ((a · a) + (b · b)))
    ≡ (((a + d) · (r - a)) + ((((r - a) · (r - d)) - ((- b) · (- b)))))
  fm1R r a b d = solve! R
  fm2R : (r a b d : ⟨ R ⟩)
    → ((r · r) - ((a · a) + (b · b)))
    ≡ (((- (a + d)) · (r + a)) + ((((r + a) · (r + d)) - (b · b))))
  fm2R r a b d = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; <-·o; ≤-·o; <Weaken≤; isTrans<≤; isTrans≤<; _≟_; Trichotomy; lt; eq; gt;
         <-+o; ≤Monotone+; isRefl≤)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all)

-- det(r²I−M²) = det(rI−M)·det(rI+M) at ℚ.
detMult : (r a b d : ℚ)
  → ((((r · r) - ((a · a) + (b · b))) · ((r · r) - ((b · b) + (d · d))))
       - ((- (b · (a + d))) · (- (b · (a + d)))))
  ≡ ((((r - a) · (r - d)) - ((- b) · (- b))) · (((r + a) · (r + d)) - (b · b)))
detMult = detMultR ℚCommRing

private
  0<·0< : (m n : ℚ) → 0 < m → 0 < n → 0 < (m · n)
  0<·0< m n 0<m 0<n = subst (_< (m · n)) (·AnnihilL n) (<-·o 0 m n 0<n 0<m)
  -- 0 ≤ m  ∧  0 < n  ⟹  0 ≤ m·n.
  0≤·0< : (m n : ℚ) → 0 ≤ m → 0 < n → 0 ≤ (m · n)
  0≤·0< m n 0≤m 0<n = subst (_≤ (m · n)) (·AnnihilL n) (≤-·o 0 m n (<Weaken≤ 0 n 0<n) 0≤m)
  -- nonneg + pos > 0.
  nn+pos : (m n : ℚ) → 0 ≤ m → 0 < n → 0 < (m + n)
  nn+pos m n 0≤m 0<n = isTrans<≤ 0 n (m + n) 0<n
                         (subst (_≤ (m + n)) (+IdL n) (≤Monotone+ 0 m n n 0≤m (isRefl≤ n)))
  -- z < 0  ⟹  0 < −z.
  neg-pos : (z : ℚ) → z < 0 → 0 < (- z)
  neg-pos z z<0 = subst2 _<_ (+Comm z (- z) ∙ +InvL z) (+IdL (- z)) (<-+o z 0 (- z) z<0)

fm1 : (r a b d : ℚ)
  → ((r · r) - ((a · a) + (b · b)))
  ≡ (((a + d) · (r - a)) + ((((r - a) · (r - d)) - ((- b) · (- b)))))
fm1 = fm1R ℚCommRing
fm2 : (r a b d : ℚ)
  → ((r · r) - ((a · a) + (b · b)))
  ≡ (((- (a + d)) · (r + a)) + ((((r + a) · (r + d)) - (b · b))))
fm2 = fm2R ℚCommRing

-- ── the spectral matrix M = [[a,b],[b,d]] ───────────────────────────────────
module _ (a b d : ℚ) where

  isPD2 : ℚ → ℚ → ℚ → Type
  isPD2 A B D = (0 < A) × (0 < ((A · D) - (B · B)))

  -- BACKWARD:  isPD(rI−M) ∧ isPD(rI+M)  ⟹  isPD(r²I−M²)   (r above ‖M‖ ⟹ r² above ‖M²‖).
  cstar-back : (r : ℚ) → 0 < r
    → isPD2 (r - a) (- b) (r - d)
    → isPD2 (r + a) b (r + d)
    → isPD2 ((r · r) - ((a · a) + (b · b))) (- (b · (a + d))) ((r · r) - ((b · b) + (d · d)))
  cstar-back r 0<r (0<r-a , 0<DR1) (0<r+a , 0<DR2) = (0<firstMinor , 0<secondMinor)
    where
      DR1 DR2 : ℚ
      DR1 = ((r - a) · (r - d)) - ((- b) · (- b))
      DR2 = ((r + a) · (r + d)) - (b · b)
      0<secondMinor : 0 < ((((r · r) - ((a · a) + (b · b))) · ((r · r) - ((b · b) + (d · d))))
                            - ((- (b · (a + d))) · (- (b · (a + d)))))
      0<secondMinor = subst (0 <_) (sym (detMult r a b d)) (0<·0< DR1 DR2 0<DR1 0<DR2)
      0<firstMinor : 0 < ((r · r) - ((a · a) + (b · b)))
      0<firstMinor with (a + d) ≟ 0
      ... | gt 0<a+d = subst (0 <_) (sym (fm1 r a b d))
                         (nn+pos ((a + d) · (r - a)) DR1 (0≤·0< (a + d) (r - a) (<Weaken≤ 0 (a + d) 0<a+d) 0<r-a) 0<DR1)
      ... | eq a+d≡0 = subst (0 <_) (sym (fm1 r a b d)) (nn+pos ((a + d) · (r - a)) DR1 0≤term 0<DR1)
        where 0≤term : 0 ≤ ((a + d) · (r - a))
              0≤term = subst (0 ≤_) (sym (cong (_· (r - a)) a+d≡0 ∙ ·AnnihilL (r - a))) (isRefl≤ 0)
      ... | lt a+d<0 = subst (0 <_) (sym (fm2 r a b d))
                         (nn+pos ((- (a + d)) · (r + a)) DR2 (0≤·0< (- (a + d)) (r + a) (<Weaken≤ 0 (- (a + d)) (neg-pos (a + d) a+d<0)) 0<r+a) 0<DR2)
