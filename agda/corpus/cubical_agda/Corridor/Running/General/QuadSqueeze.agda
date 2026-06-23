{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE QUADRATIC SQUEEZE — q²−q < r²−r and 1 < q+r ⟹ q < r.
--
-- The order-reflection at the heart of "the running corridor converges to φ" (Item A, converse).  The
-- function f(x)=x²−x is increasing on (½,∞); both running convergents and any rational near φ live
-- there, so comparing f reflects to comparing the points.  Algebraically: (r²−r)−(q²−q) =
-- (r−q)·(r+q−1) > 0 and r+q−1 > 0 force r−q > 0.  Pure ℚ ring + sign cancellation, reusable on both
-- the lower (lo n ↑ φ) and upper (hi n ↓ φ) sides of the cut.
--
module corpus.cubical_agda.Corridor.Running.General.QuadSqueeze where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- the factorisation as an abstract ring identity (solve! cannot run on the concrete ℚ SetQuotient).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  factoredR : (q r : ⟨ R ⟩)
            → (((r · r) + (- r)) + (- ((q · q) + (- q)))) ≡ ((r + (- q)) · ((r + q) + (- 1r)))
  factoredR q r = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <-+o; <-·o-cancel)

quad-squeeze : (q r : ℚ)
             → ((q · q) + (- q)) < ((r · r) + (- r))
             → 1 < (q + r)
             → q < r
quad-squeeze q r hf h1 = diff→< 0<r-q
  where
    A B : ℚ
    A = (q · q) + (- q)
    B = (r · r) + (- r)
    -- a < b  ⟹  0 < b − a   (the DedekindReal idiom)
    0<B-A : 0 < (B + (- A))
    0<B-A = subst (_< (B + (- A))) (+InvR A) (<-+o A B (- A) hf)
    -- the factorisation (r²−r)−(q²−q) = (r−q)(r+q−1)
    factored : (B + (- A)) ≡ ((r + (- q)) · ((r + q) + (- 1)))
    factored = factoredR ℚCommRing q r
    0<prod : 0 < ((r + (- q)) · ((r + q) + (- 1)))
    0<prod = subst (0 <_) factored 0<B-A
    0<r+q-1 : 0 < ((r + q) + (- 1))
    0<r+q-1 = subst (_< ((r + q) + (- 1))) (+InvR 1)
                (<-+o 1 (r + q) (- 1) (subst (1 <_) (+Comm q r) h1))
    -- 0 < X·Y and 0 < Y  ⟹  0 < X   (cancel the positive factor)
    0<r-q : 0 < (r + (- q))
    0<r-q = <-·o-cancel 0 (r + (- q)) ((r + q) + (- 1)) 0<r+q-1
              (subst (_< ((r + (- q)) · ((r + q) + (- 1))))
                     (sym (·AnnihilL ((r + q) + (- 1)))) 0<prod)
    -- 0 < r − q  ⟹  q < r
    diff→< : 0 < (r + (- q)) → q < r
    diff→< 0<d = subst2 _<_ (+IdL q)
                   (sym (+Assoc r (- q) q) ∙ cong (r +_) (+InvL q) ∙ +IdR r)
                   (<-+o 0 (r + (- q)) q 0<d)
