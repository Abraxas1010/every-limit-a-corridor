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

  -- ring identities for the FORWARD direction.
  rxIdR  : (r x : ⟨ R ⟩) → ((r · r) - (x · x)) ≡ ((r - x) · (r + x))
  rxIdR  r x = solve! R
  fdIdR  : (r a b : ⟨ R ⟩) → ((r · r) - ((a · a) + (b · b))) ≡ (((r - a) · (r + a)) - (b · b))
  fdIdR  r a b = solve! R
  sdIdR  : (r b d : ⟨ R ⟩) → ((r · r) - ((b · b) + (d · d))) ≡ (((r - d) · (r + d)) - (b · b))
  sdIdR  r b d = solve! R
  abIdR  : (r a d : ⟨ R ⟩) → ((r + a) - (r - d)) ≡ (a + d)
  abIdR  r a d = solve! R
  abId2R : (r a d : ⟨ R ⟩) → ((r - d) - (r + a)) ≡ (- (a + d))
  abId2R r a d = solve! R
  -- firstDiag·secondDiag = det(r²I−M²) + offdiag².
  pdIdR  : (r a b d : ⟨ R ⟩)
    → (((r · r) - ((a · a) + (b · b))) · ((r · r) - ((b · b) + (d · d))))
    ≡ (((- (b · (a + d))) · (- (b · (a + d))))
        + ((((r · r) - ((a · a) + (b · b))) · ((r · r) - ((b · b) + (d · d))))
             - ((- (b · (a + d))) · (- (b · (a + d))))))
  pdIdR  r a b d = solve! R
  mnmIdR : (m n : ⟨ R ⟩) → ((m + n) + (- m)) ≡ n
  mnmIdR m n = solve! R
  negSqR : (x : ⟨ R ⟩) → ((- x) · (- x)) ≡ (x · x)
  negSqR x = solve! R
  sumIdR : (r x : ⟨ R ⟩) → ((r - x) + (r + x)) ≡ (r + r)
  sumIdR r x = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; <-·o; ≤-·o; <-·o-cancel; <Weaken≤; isTrans<≤; isTrans≤<; isTrans<;
         _≟_; Trichotomy; lt; eq; gt; <-+o; ≤Monotone+; isRefl≤; ≤→≯)
open import Cubical.Data.Sigma using (Σ; _×_; _,_; fst; snd)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)
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
  -- asymmetry (from ≤→≯).
  <-asym : (m n : ℚ) → m < n → ¬ (n < m)
  <-asym m n m<n = ≤→≯ m n (<Weaken≤ m n m<n)
  -- 0<m ∧ n<0 ⟹ m·n<0.
  posneg : (m n : ℚ) → 0 < m → n < 0 → (m · n) < 0
  posneg m n 0<m n<0 = subst ((m · n) <_) (·AnnihilL m)
                         (subst (_< (0 · m)) (·Comm n m) (<-·o n 0 m 0<m n<0))
  -- 0<m·n ∧ 0<m ⟹ 0<n.
  posprod→pos2 : (m n : ℚ) → 0 < (m · n) → 0 < m → 0 < n
  posprod→pos2 m n 0<mn 0<m with n ≟ 0
  ... | gt 0<n = 0<n
  ... | eq n≡0 = ⊥-rec (<-asym 0 0 0<0 0<0)
    where 0<0 : 0 < 0
          0<0 = subst (0 <_) (cong (m ·_) n≡0 ∙ ·AnnihilR m) 0<mn
  ... | lt n<0 = ⊥-rec (<-asym 0 (m · n) 0<mn (posneg m n 0<m n<0))
  -- 0<m·n ∧ 0<(m+n) ⟹ 0<m.
  posprod-possum→pos : (m n : ℚ) → 0 < (m · n) → 0 < (m + n) → 0 < m
  posprod-possum→pos m n 0<mn 0<m+n with m ≟ 0
  ... | gt 0<m = 0<m
  ... | eq m≡0 = ⊥-rec (<-asym 0 0 0<0 0<0)
    where 0<0 : 0 < 0
          0<0 = subst (0 <_) (cong (_· n) m≡0 ∙ ·AnnihilL n) 0<mn
  ... | lt m<0 = ⊥-rec (<-asym 0 (m · n) 0<mn mn<0)
    where 0<n : 0 < n
          0<n = subst (0 <_) (mnmIdR ℚCommRing m n)
                  (nn+pos (m + n) (- m) (<Weaken≤ 0 (m + n) 0<m+n) (neg-pos m m<0))
          mn<0 : (m · n) < 0
          mn<0 = subst (_< 0) (·Comm n m) (posneg n m 0<n m<0)
  -- X<Y ⟹ 0<Y−X  and  0<Y−X ⟹ X<Y.
  <→0<sub : (X Y : ℚ) → X < Y → 0 < (Y - X)
  <→0<sub X Y X<Y = subst (_< (Y - X)) (+Comm X (- X) ∙ +InvL X) (<-+o X Y (- X) X<Y)
  0<sub→< : (X Y : ℚ) → 0 < (Y - X) → X < Y
  0<sub→< X Y 0<Y-X = subst2 _<_ (+IdL X)
                        (sym (+Assoc Y (- X) X) ∙ cong (Y +_) (+InvL X) ∙ +IdR Y)
                        (<-+o 0 (Y - X) X 0<Y-X)
  -- (X−Y)<0 ⟹ X<Y.
  sub<0→< : (X Y : ℚ) → (X - Y) < 0 → X < Y
  sub<0→< X Y X-Y<0 = subst2 _<_
                        (sym (+Assoc X (- Y) Y) ∙ cong (X +_) (+InvL Y) ∙ +IdR X)
                        (+IdL Y)
                        (<-+o (X - Y) 0 Y X-Y<0)
  -- cancel a positive left factor:  0<k ∧ k·X<k·Y ⟹ X<Y.
  cancelL< : (k X Y : ℚ) → 0 < k → (k · X) < (k · Y) → X < Y
  cancelL< k X Y 0<k kX<kY = <-·o-cancel X Y k 0<k
                              (subst2 _<_ (·Comm k X) (·Comm k Y) kX<kY)
  -- 0<r ⟹ 0<r+r.
  0<2r : (r : ℚ) → 0 < r → 0 < (r + r)
  0<2r r 0<r = nn+pos r r (<Weaken≤ 0 r 0<r) 0<r
  -- 0<x ⟹ −x<0.
  pos→neg : (x : ℚ) → 0 < x → (- x) < 0
  pos→neg x 0<x = subst2 _<_ (+IdL (- x)) (+Comm x (- x) ∙ +InvL x) (<-+o 0 x (- x) 0<x)
  -- 0<m·n ∧ m<0 ⟹ n<0   (same-sign reasoning).
  posprod-neg-fst : (m n : ℚ) → 0 < (m · n) → m < 0 → n < 0
  posprod-neg-fst m n 0<mn m<0 with n ≟ 0
  ... | lt n<0 = n<0
  ... | eq n≡0 = ⊥-rec (<-asym 0 0 0<0 0<0)
    where 0<0 : 0 < 0
          0<0 = subst (0 <_) (cong (m ·_) n≡0 ∙ ·AnnihilR m) 0<mn
  ... | gt 0<n = ⊥-rec (<-asym 0 (m · n) 0<mn
                  (subst (_< 0) (·Comm n m) (posneg n m 0<n m<0)))

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

  -- FORWARD:  isPD(r²I−M²)  ⟹  isPD(rI−M) ∧ isPD(rI+M)   (r² above ‖M²‖ ⟹ r above ‖M‖).
  cstar-fwd : (r : ℚ) → 0 < r
    → isPD2 ((r · r) - ((a · a) + (b · b))) (- (b · (a + d))) ((r · r) - ((b · b) + (d · d)))
    → isPD2 (r - a) (- b) (r - d) × isPD2 (r + a) b (r + d)
  cstar-fwd r 0<r (0<fd , 0<det) = ((0<r-a , 0<DR1) , (0<r+a , 0<DR2))
    where
      fd sd od² DR1 DR2 : ℚ
      fd  = (r · r) - ((a · a) + (b · b))
      sd  = (r · r) - ((b · b) + (d · d))
      od² = (- (b · (a + d))) · (- (b · (a + d)))
      DR1 = ((r - a) · (r - d)) - ((- b) · (- b))
      DR2 = ((r + a) · (r + d)) - (b · b)
      0<fdsd : 0 < (fd · sd)
      0<fdsd = subst (0 <_) (sym (pdIdR ℚCommRing r a b d))
                 (nn+pos od² ((fd · sd) - od²) (0≤sq-all (- (b · (a + d)))) 0<det)
      0<sd : 0 < sd
      0<sd = posprod→pos2 fd sd 0<fdsd 0<fd
      -- diagonal positivity:  b² < (r∓a)(r±a) etc ⟹ 0 < r±a, 0 < r±d.
      0<rara : 0 < ((r - a) · (r + a))
      0<rara = isTrans≤< 0 (b · b) ((r - a) · (r + a)) (0≤sq-all b)
                 (0<sub→< (b · b) ((r - a) · (r + a)) (subst (0 <_) (fdIdR ℚCommRing r a b) 0<fd))
      0<rdrd : 0 < ((r - d) · (r + d))
      0<rdrd = isTrans≤< 0 (b · b) ((r - d) · (r + d)) (0≤sq-all b)
                 (0<sub→< (b · b) ((r - d) · (r + d)) (subst (0 <_) (sdIdR ℚCommRing r b d) 0<sd))
      0<r-a : 0 < (r - a)
      0<r-a = posprod-possum→pos (r - a) (r + a) 0<rara
                (subst (0 <_) (sym (sumIdR ℚCommRing r a)) (0<2r r 0<r))
      0<r+a : 0 < (r + a)
      0<r+a = posprod-possum→pos (r + a) (r - a) (subst (0 <_) (·Comm (r - a) (r + a)) 0<rara)
                (subst (0 <_) (sym (sumIdR ℚCommRing r a) ∙ +Comm (r - a) (r + a)) (0<2r r 0<r))
      0<r-d : 0 < (r - d)
      0<r-d = posprod-possum→pos (r - d) (r + d) 0<rdrd
                (subst (0 <_) (sym (sumIdR ℚCommRing r d)) (0<2r r 0<r))
      0<r+d : 0 < (r + d)
      0<r+d = posprod-possum→pos (r + d) (r - d) (subst (0 <_) (·Comm (r - d) (r + d)) 0<rdrd)
                (subst (0 <_) (sym (sumIdR ℚCommRing r d) ∙ +Comm (r - d) (r + d)) (0<2r r 0<r))
      -- b² strictly below each cross-product.
      bb<rara : (b · b) < ((r - a) · (r + a))
      bb<rara = 0<sub→< (b · b) ((r - a) · (r + a)) (subst (0 <_) (fdIdR ℚCommRing r a b) 0<fd)
      bb<rdrd : (b · b) < ((r - d) · (r + d))
      bb<rdrd = 0<sub→< (b · b) ((r - d) · (r + d)) (subst (0 <_) (sdIdR ℚCommRing r b d) 0<sd)
      0<DR1DR2 : 0 < (DR1 · DR2)
      0<DR1DR2 = subst (0 <_) (detMult r a b d) 0<det
      -- not-both-negative:  DR1<0 ⟹ 0<a+d ;  DR2<0 ⟹ a+d<0  — contradictory.
      0<DR1 : 0 < DR1
      0<DR1 with DR1 ≟ 0
      ... | gt 0<DR1' = 0<DR1'
      ... | eq DR1≡0 = ⊥-rec (<-asym 0 0 0<0 0<0)
        where 0<0 = subst (0 <_) (cong (_· DR2) DR1≡0 ∙ ·AnnihilL DR2) 0<DR1DR2
      ... | lt DR1<0 = ⊥-rec (<-asym 0 (a + d) 0<a+d ad<0)
        where
          DR2<0 : DR2 < 0
          DR2<0 = posprod-neg-fst DR1 DR2 0<DR1DR2 DR1<0
          rd<ra : (r - d) < (r + a)
          rd<ra = cancelL< (r - a) (r - d) (r + a) 0<r-a
                    (isTrans< ((r - a) · (r - d)) ((- b) · (- b)) ((r - a) · (r + a))
                      (sub<0→< ((r - a) · (r - d)) ((- b) · (- b)) DR1<0)
                      (subst (_< ((r - a) · (r + a))) (sym (negSqR ℚCommRing b)) bb<rara))
          0<a+d : 0 < (a + d)
          0<a+d = subst (0 <_) (abIdR ℚCommRing r a d) (<→0<sub (r - d) (r + a) rd<ra)
          ra<rd : (r + a) < (r - d)
          ra<rd = cancelL< (r + d) (r + a) (r - d) 0<r+d
                    (isTrans< ((r + d) · (r + a)) (b · b) ((r + d) · (r - d))
                      (subst (_< (b · b)) (·Comm (r + a) (r + d)) (sub<0→< ((r + a) · (r + d)) (b · b) DR2<0))
                      (subst (((b · b)) <_) (·Comm (r - d) (r + d)) bb<rdrd))
          ad<0 : (a + d) < 0
          ad<0 = subst (_< 0) (-Invol (a + d))
                   (pos→neg (- (a + d)) (subst (0 <_) (abId2R ℚCommRing r a d) (<→0<sub (r + a) (r - d) ra<rd)))
      0<DR2 : 0 < DR2
      0<DR2 with DR2 ≟ 0
      ... | gt 0<DR2' = 0<DR2'
      ... | eq DR2≡0 = ⊥-rec (<-asym 0 0 0<0 0<0)
        where 0<0 = subst (0 <_) (cong (DR1 ·_) DR2≡0 ∙ ·AnnihilR DR1) 0<DR1DR2
      ... | lt DR2<0 = ⊥-rec (<-asym 0 (a + d) 0<a+d ad<0)
        where
          DR1<0 : DR1 < 0
          DR1<0 = posprod-neg-fst DR2 DR1 (subst (0 <_) (·Comm DR1 DR2) 0<DR1DR2) DR2<0
          rd<ra : (r - d) < (r + a)
          rd<ra = cancelL< (r - a) (r - d) (r + a) 0<r-a
                    (isTrans< ((r - a) · (r - d)) ((- b) · (- b)) ((r - a) · (r + a))
                      (sub<0→< ((r - a) · (r - d)) ((- b) · (- b)) DR1<0)
                      (subst (_< ((r - a) · (r + a))) (sym (negSqR ℚCommRing b)) bb<rara))
          0<a+d : 0 < (a + d)
          0<a+d = subst (0 <_) (abIdR ℚCommRing r a d) (<→0<sub (r - d) (r + a) rd<ra)
          ra<rd : (r + a) < (r - d)
          ra<rd = cancelL< (r + d) (r + a) (r - d) 0<r+d
                    (isTrans< ((r + d) · (r + a)) (b · b) ((r + d) · (r - d))
                      (subst (_< (b · b)) (·Comm (r + a) (r + d)) (sub<0→< ((r + a) · (r + d)) (b · b) DR2<0))
                      (subst (((b · b)) <_) (·Comm (r - d) (r + d)) bb<rdrd))
          ad<0 : (a + d) < 0
          ad<0 = subst (_< 0) (-Invol (a + d))
                   (pos→neg (- (a + d)) (subst (0 <_) (abId2R ℚCommRing r a d) (<→0<sub (r + a) (r - d) ra<rd)))

  -- ── THE CUT-LEVEL C*-IDENTITY:  isPD(r²I−M²)  ⟺  isPD(rI−M) ∧ isPD(rI+M)  (r>0). ──
  cstar-cut : (r : ℚ) → 0 < r
    → (isPD2 ((r · r) - ((a · a) + (b · b))) (- (b · (a + d))) ((r · r) - ((b · b) + (d · d)))
        → (isPD2 (r - a) (- b) (r - d) × isPD2 (r + a) b (r + d)))
      × ((isPD2 (r - a) (- b) (r - d) × isPD2 (r + a) b (r + d))
        → isPD2 ((r · r) - ((a · a) + (b · b))) (- (b · (a + d))) ((r · r) - ((b · b) + (d · d))))
  cstar-cut r 0<r = (cstar-fwd r 0<r , λ (p- , p+) → cstar-back r 0<r p- p+)

  -- ── OPERATOR-NORM FRAMING ────────────────────────────────────────────────
  -- The operator norm of symmetric M is the spectral radius ρ(M)=max|λ|, whose cut needs
  -- BOTH ±M:  q > ‖M‖  ⟺  q > λmax(M) ∧ q > λmax(−M)  ⟺  qI−M PD ∧ qI+M PD.
  -- (isUpperM is definitionally SpecRadiusCut.isUpper of M; isUpper-negM is that of −M.)
  isUpperM isUpper-negM isNorm isUpperM² : ℚ → Type
  isUpperM     q = isPD2 (q - a) (- b) (q - d)                 -- q > λmax(M)   (qI−M PD)
  isUpper-negM q = isPD2 (q + a) b (q + d)                     -- q > λmax(−M)  (qI+M PD)
  isNorm       q = isUpperM q × isUpper-negM q                 -- q > ‖M‖ = ρ(M) = max|λ|
  isUpperM²    q = isPD2 (q - ((a · a) + (b · b))) (- (b · (a + d))) (q - ((b · b) + (d · d)))
                                                               -- q > λmax(M²) = ‖M²‖   (M² is PSD)

  -- THE C*-IDENTITY, operator-norm form:  on rational squares q=r² (r>0), the cut of ‖M²‖
  -- and the cut of ‖M‖² coincide.  Since rational squares are dense in [0,∞), this says the
  -- two located reals ‖M²‖ and ‖M‖² are EQUAL:  ‖M²‖ = ‖M‖².
  cstar-norm : (r : ℚ) → 0 < r
             → (isUpperM² (r · r) → isNorm r) × (isNorm r → isUpperM² (r · r))
  cstar-norm r 0<r = cstar-cut r 0<r
