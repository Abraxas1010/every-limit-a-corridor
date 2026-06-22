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

  -- the MIRROR SOS (complete the square on the other variable):  d·Q = (b x + d y)² + (ad−b²)·x².
  sosId-x : (a b d x y : ⟨ R ⟩)
          → (d · quad a b d x y)
          ≡ (((b · x) + (d · y)) · ((b · x) + (d · y)))
              + (((a · d) - (b · b)) · (x · x))
  sosId-x a b d x y = solve! R

  -- z² = (−z)²  (for the negative branch of square-positivity).
  negSq : (z : ⟨ R ⟩) → (z · z) ≡ ((- z) · (- z))
  negSq z = solve! R

-- ── instantiated to ℚ (the bridge ⟨ ℚCommRing ⟩ ≡ ℚ, ops definitional) ──────
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; ≤-·o; ≤-·o-cancel; ≮→≥; _≟_; Trichotomy; lt; eq; gt;
         <-·o; <-·o-cancel; <-+o; isTrans<≤; isTrans≤<; isRefl≤; ≤Monotone+)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
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

-- ── the FORWARD direction:  0<a ∧ 0<ad−b²  ⟹  PD (⟨Mx,x⟩ > 0 for every x ≠ 0) ──
-- The SOS read for positivity.  No determinant theory, no eigenvectors: just the two
-- mirror certificates, each a positive square plus the (ad−b²)·(square) term.

private
  0<·0< : (m n : ℚ) → 0 < m → 0 < n → 0 < (m · n)
  0<·0< m n 0<m 0<n = subst (_< (m · n)) (·AnnihilL n) (<-·o 0 m n 0<n 0<m)

  -- square-positivity:  z ≠ 0  ⟹  0 < z·z   (via trichotomy; the negative branch uses z²=(−z)²).
  sq-pos : (z : ℚ) → ¬ (z ≡ 0) → 0 < (z · z)
  sq-pos z z≢0 with z ≟ 0
  ... | gt 0<z = 0<·0< z z 0<z 0<z
  ... | eq z≡0 = ⊥-rec (z≢0 z≡0)
  ... | lt z<0 = subst (0 <_) (sym (negSq ℚCommRing z)) (0<·0< (- z) (- z) 0<-z 0<-z)
    where
      0<-z : 0 < (- z)
      0<-z = subst2 _<_ (+Comm z (- z) ∙ +InvL z) (+IdL (- z)) (<-+o z 0 (- z) z<0)

  -- 0 ≤ m  ∧  0 < n  ⟹  0 < m + n.
  nn+pos : (m n : ℚ) → 0 ≤ m → 0 < n → 0 < (m + n)
  nn+pos m n 0≤m 0<n =
    isTrans<≤ 0 n (m + n) 0<n
      (subst (_≤ (m + n)) (+IdL n) (≤Monotone+ 0 m n n 0≤m (isRefl≤ n)))

  -- 0<a ∧ 0<ad−b²  ⟹  0<d   (so the mirror pivot is positive too):  b² < ad, ad>0, hence d>0.
  0<d-of : (a b d : ℚ) → 0 < a → 0 < ((a · d) - (b · b)) → 0 < d
  0<d-of a b d 0<a 0<disc = <-·o-cancel 0 d a 0<a 0<d·a
    where
      b²<ad : (b · b) < (a · d)
      b²<ad = subst2 _<_ (+IdL (b · b)) lemAD (<-+o 0 ((a · d) - (b · b)) (b · b) 0<disc)
        where lemAD : (((a · d) - (b · b)) + (b · b)) ≡ (a · d)
              lemAD = solveAD ℚCommRing a b d
                where open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
                      solveAD : (R : CommRing ℓ-zero) (a b d : ⟨ R ⟩)
                              → (CommRingStr._+_ (snd R)
                                   (CommRingStr._-_ (snd R) (CommRingStr._·_ (snd R) a d)
                                                            (CommRingStr._·_ (snd R) b b))
                                   (CommRingStr._·_ (snd R) b b))
                                ≡ CommRingStr._·_ (snd R) a d
                      solveAD R a b d = let open CommRingStr (snd R) in solve! R
      0<ad : 0 < (a · d)
      0<ad = isTrans≤< 0 (b · b) (a · d) (0≤sq-all b) b²<ad
      0<d·a : (0 · a) < (d · a)
      0<d·a = subst2 _<_ (sym (·AnnihilL a)) (·Comm a d) 0<ad

  -- strip the positive pivot:  0 < c · Q  ∧  0 < c  ⟹  0 < Q.
  cancelPiv : (c q : ℚ) → 0 < c → 0 < (c · q) → 0 < q
  cancelPiv c q 0<c 0<cq =
    <-·o-cancel 0 q c 0<c (subst2 _<_ (sym (·AnnihilL c)) (·Comm c q) 0<cq)

-- THE FORWARD CRITERION.  "x ≠ 0" = one component apart from 0 (ℚ has decidable equality).
pd-forward : (a b d x y : ℚ) → 0 < a → 0 < ((a · d) - (b · b))
           → (¬ (x ≡ 0)) ⊎ (¬ (y ≡ 0))
           → 0 < quadℚ a b d x y
pd-forward a b d x y 0<a 0<disc (inr y≢0) =
  cancelPiv a (quadℚ a b d x y) 0<a 0<aQ
  where
    0<aQ : 0 < (a · quadℚ a b d x y)
    0<aQ = subst (0 <_) (sym (sosℚ a b d x y))
             (nn+pos (((a · x) + (b · y)) · ((a · x) + (b · y)))
                     (((a · d) - (b · b)) · (y · y))
                     (0≤sq-all ((a · x) + (b · y)))
                     (0<·0< ((a · d) - (b · b)) (y · y) 0<disc (sq-pos y y≢0)))
pd-forward a b d x y 0<a 0<disc (inl x≢0) =
  cancelPiv d (quadℚ a b d x y) (0<d-of a b d 0<a 0<disc) 0<dQ
  where
    0<dQ : 0 < (d · quadℚ a b d x y)
    0<dQ = subst (0 <_) (sym (sosId-x ℚCommRing a b d x y))
             (nn+pos (((b · x) + (d · y)) · ((b · x) + (d · y)))
                     (((a · d) - (b · b)) · (x · x))
                     (0≤sq-all ((b · x) + (d · y)))
                     (0<·0< ((a · d) - (b · b)) (x · x) 0<disc (sq-pos x x≢0)))
