{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5 / D1: the spectral value φ is genuinely PINNED -- the quadratic
-- x²−x is strictly monotone where x+? > 1, so the golden cut separates.  This
-- is the core of φ's located law (φ as a located real, the spectral value of the
-- golden recurrence).  Manual ℚ ring algebra (solve! fails on ℚ's SetQuotient).

module corpus.cubical_agda.RealCohesion.GoldenValue where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <-+o; <-o+; <-·o)
open import corpus.cubical_agda.RealCohesion.RealApprox using (neg-mult; 0<width; 0<·d)

-- difference of squares: (r−q)(r+q) ≡ r² − q².
diff-sq : (r q : ℚ) → (r + (- q)) · (r + q) ≡ (r · r) + (- (q · q))
diff-sq r q =
  (r + (- q)) · (r + q)
    ≡⟨ ·DistL+ (r + (- q)) r q ⟩
  ((r + (- q)) · r) + ((r + (- q)) · q)
    ≡⟨ cong₂ _+_ (·DistR+ r (- q) r) (·DistR+ r (- q) q) ⟩
  ((r · r) + ((- q) · r)) + ((r · q) + ((- q) · q))
    ≡⟨ cong₂ (λ u v → ((r · r) + u) + ((r · q) + v))
             (neg-mult q r) (neg-mult q q) ⟩
  ((r · r) + (- (q · r))) + ((r · q) + (- (q · q)))
    ≡⟨ rearrange ⟩
  (r · r) + (- (q · q)) ∎
  where
    rearrange : ((r · r) + (- (q · r))) + ((r · q) + (- (q · q)))
              ≡ (r · r) + (- (q · q))
    rearrange =
      ((r · r) + (- (q · r))) + ((r · q) + (- (q · q)))
        ≡⟨ sym (+Assoc (r · r) (- (q · r)) ((r · q) + (- (q · q)))) ⟩
      (r · r) + ((- (q · r)) + ((r · q) + (- (q · q))))
        ≡⟨ cong ((r · r) +_) (+Assoc (- (q · r)) (r · q) (- (q · q))) ⟩
      (r · r) + (((- (q · r)) + (r · q)) + (- (q · q)))
        ≡⟨ cong (λ u → (r · r) + ((u + (r · q)) + (- (q · q)))) (cong -_ (·Comm q r)) ⟩
      (r · r) + (((- (r · q)) + (r · q)) + (- (q · q)))
        ≡⟨ cong (λ u → (r · r) + (u + (- (q · q)))) (+InvL (r · q)) ⟩
      (r · r) + ((0 + (- (q · q))))
        ≡⟨ cong ((r · r) +_) (+IdL (- (q · q))) ⟩
      (r · r) + (- (q · q)) ∎

open import corpus.cubical_agda.RealCohesion.RealApprox using (-Dist; a+d≡c)

-- the key factored identity:  (r²−r) − (q²−q) ≡ (r−q)·((r+q)−1).
quad-id : (q r : ℚ)
  → (r · r + (- r)) + (- (q · q + (- q))) ≡ (r + (- q)) · ((r + q) + (- 1))
quad-id q r = sym (
  (r + (- q)) · ((r + q) + (- 1))
    ≡⟨ ·DistL+ (r + (- q)) (r + q) (- 1) ⟩
  ((r + (- q)) · (r + q)) + ((r + (- q)) · (- 1))
    ≡⟨ cong₂ _+_ (diff-sq r q) lem-1 ⟩
  ((r · r) + (- (q · q))) + ((- r) + q)
    ≡⟨ rearrange2 ⟩
  (r · r + (- r)) + (- (q · q + (- q))) ∎)
  where
    lem-1 : (r + (- q)) · (- 1) ≡ (- r) + q
    lem-1 = (r + (- q)) · (- 1)        ≡⟨ ·Comm (r + (- q)) (- 1) ⟩
            (- 1) · (r + (- q))        ≡⟨ ·DistL+ (- 1) r (- q) ⟩
            ((- 1) · r) + ((- 1) · (- q))  ≡⟨ cong (((- 1) · r) +_) (-Invol q) ⟩
            (- r) + q ∎
    rearrange2 : ((r · r) + (- (q · q))) + ((- r) + q)
               ≡ (r · r + (- r)) + (- (q · q + (- q)))
    rearrange2 =
      ((r · r) + (- (q · q))) + ((- r) + q)
        ≡⟨ sym (+Assoc (r · r) (- (q · q)) ((- r) + q)) ⟩
      (r · r) + ((- (q · q)) + ((- r) + q))
        ≡⟨ cong ((r · r) +_) (+Assoc (- (q · q)) (- r) q) ⟩
      (r · r) + (((- (q · q)) + (- r)) + q)
        ≡⟨ cong (λ z → (r · r) + ((z) + q)) (+Comm (- (q · q)) (- r)) ⟩
      (r · r) + (((- r) + (- (q · q))) + q)
        ≡⟨ cong ((r · r) +_) (sym (+Assoc (- r) (- (q · q)) q)) ⟩
      (r · r) + ((- r) + ((- (q · q)) + q))
        ≡⟨ +Assoc (r · r) (- r) ((- (q · q)) + q) ⟩
      ((r · r) + (- r)) + ((- (q · q)) + q)
        ≡⟨ cong (λ z → ((r · r) + (- r)) + ((- (q · q)) + z)) (sym (-Invol q)) ⟩
      ((r · r) + (- r)) + ((- (q · q)) + (- (- q)))
        ≡⟨ cong (((r · r) + (- r)) +_) (sym (-Dist (q · q) (- q))) ⟩
      (r · r + (- r)) + (- (q · q + (- q))) ∎

-- 0 < (c−a) ⟹ a < c (the dense-technique, reversed).
pos-diff→< : (a c : ℚ) → 0 < (c + (- a)) → a < c
pos-diff→< a c 0<d = subst2 _<_ (+IdR a) (a+d≡c a c) (<-o+ 0 (c + (- a)) a 0<d)

-- THE QUADRATIC MONOTONICITY: where q+r > 1 and q < r, x²−x strictly increases.
-- This is the heart of the golden cut's LOCATED law -- φ is genuinely pinned.
quad-mono : (q r : ℚ) → 1 < q + r → q < r → (q · q + (- q)) < (r · r + (- r))
quad-mono q r 1<q+r q<r = pos-diff→< (q · q + (- q)) (r · r + (- r)) 0<diff
  where
    0<r-q : 0 < (r + (- q))
    0<r-q = 0<width q r q<r
    0<r+q-1 : 0 < ((r + q) + (- 1))
    0<r+q-1 = subst (λ z → 0 < (z + (- 1))) (+Comm q r) (0<width 1 (q + r) 1<q+r)
    0<diff : 0 < ((r · r + (- r)) + (- (q · q + (- q))))
    0<diff = subst (0 <_) (sym (quad-id q r))
                   (0<·d (r + (- q)) ((r + q) + (- 1)) 0<r-q 0<r+q-1)
