{-# OPTIONS --cubical --safe --guardedness #-}
--
-- EQUALITY OF LOCATED REALS — the form the operator-norm C*-identity asserts.
--
-- ‖M²‖ = ‖M‖² is, at the located-real level, the statement that two located reals have
-- COINCIDING cuts: every lower bound of one is below every upper bound of the other, both
-- ways.  This module defines that equality `_≈_` and proves it reflexive (via the Dedekind
-- cross-cut — every lower convergent below every upper, the `CrossCut` argument generalised
-- to any `LocatedReal`) and symmetric.  Division-free (ordering only), so reachable now —
-- unlike the convergence estimate, which needs ℚ-division infrastructure the library lacks.
-- This is the relation in which the final theorem ‖M²‖≈‖M‖² lives.
--
module corpus.cubical_agda.Corridor.Running.General.LocatedEq where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order renaming (_<_ to _<ℕ_) using (_≤_; splitℕ-≤; <-weaken)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Rationals.Order
  renaming (_≤_ to _≤ℚ_)
  using (_<_; isRefl≤; isTrans≤; isTrans≤<; isTrans<≤; <Weaken≤)
open import corpus.cubical_agda.Corridor.Running.General.LocatedReal
  using (LocatedReal; lo; hi; nondeg; inc; dec)

private
  -- lower bounds increase weakly:  lo r m ≤ lo r (k + m)   (from strict `inc`).
  lo-le+ : (r : LocatedReal) (m k : ℕ) → lo r m ≤ℚ lo r (k + m)
  lo-le+ r m zero    = isRefl≤ (lo r m)
  lo-le+ r m (suc k) = isTrans≤ (lo r m) (lo r (k + m)) (lo r (suc (k + m)))
                         (lo-le+ r m k)
                         (<Weaken≤ (lo r (k + m)) (lo r (suc (k + m))) (inc r (k + m)))

  -- upper bounds decrease weakly:  hi r (k + m) ≤ hi r m   (from strict `dec`).
  hi-le+ : (r : LocatedReal) (m k : ℕ) → hi r (k + m) ≤ℚ hi r m
  hi-le+ r m zero    = isRefl≤ (hi r m)
  hi-le+ r m (suc k) = isTrans≤ (hi r (suc (k + m))) (hi r (k + m)) (hi r m)
                         (<Weaken≤ (hi r (suc (k + m))) (hi r (k + m)) (dec r (k + m)))
                         (hi-le+ r m k)

-- THE CROSS-CUT: every lower convergent is below every upper convergent (∀ n m).
cross : (r : LocatedReal) (n m : ℕ) → lo r n < hi r m
cross r n m with splitℕ-≤ n m
... | inl (k , p) =                       -- n ≤ m,  k + n ≡ m
      isTrans≤< (lo r n) (lo r m) (hi r m)
        (subst (lo r n ≤ℚ_) (cong (lo r) p) (lo-le+ r n k))
        (nondeg r m)
... | inr m<n with <-weaken m<n
...   | (k , p) =                         -- m ≤ n,  k + m ≡ n
        isTrans<≤ (lo r n) (hi r n) (hi r m)
          (nondeg r n)
          (subst (_≤ℚ hi r m) (cong (hi r) p) (hi-le+ r m k))

-- equality of located reals: coinciding cuts (mutual cross-cut).
_≈_ : LocatedReal → LocatedReal → Type
r ≈ s = ((n m : ℕ) → lo r n < hi s m) × ((n m : ℕ) → lo s n < hi r m)

-- reflexivity (the cross-cut) and symmetry.
≈-refl : (r : LocatedReal) → r ≈ r
≈-refl r = cross r , cross r

≈-sym : {r s : LocatedReal} → r ≈ s → s ≈ r
≈-sym (p , q) = q , p
