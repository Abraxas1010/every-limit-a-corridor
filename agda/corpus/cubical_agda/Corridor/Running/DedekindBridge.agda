{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE CORRIDOR IS THE POINT — running convergents bracket the Dedekind φ:ℝ, ∀n.
--
-- The project has two φ's: the Dedekind "point" `GoldenCut.φ : ℝ` (organism,
-- bracketed in `GoldenLocated` only at n=1 by 3/2, 5/3) and the running "corridor"
-- `Bracket.lo/hi` (all n).  This module proves they are one: for EVERY rung n,
-- `ι (lo n) <ℝ φ <ℝ ι (hi n)`.  The keystone is already proved — `golden-lower-
-- faithful : lo n² < lo n + 1` IS membership in φ's lower cut
-- `φL q = ∥(q<0)⊎(q²<q+1)∥₁`; the strict-`<ℝ` witness is the next convergent
-- (`lo n < lo(n+1)` by lo↗).  Dually for the upper bound, with `1 < hi(n+1)`
-- supplied by the Dedekind cut itself (`lo 0 = 1 < hi(n+1)`).  This makes "the
-- corridor converges to the point" — the paper's central metaphor — a theorem.
--
module corpus.cubical_agda.Corridor.Running.DedekindBridge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma using (_,_; _×_)
open import Cubical.Data.Sum using (inr)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_)

open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; ι; _<ℝ_)
open import corpus.cubical_agda.RealCohesion.GoldenCut using (φ)
open import corpus.cubical_agda.Corridor.Running.Bracket using (lo; hi)
open import corpus.cubical_agda.Corridor.Running.Located using (lo↗; hi↘)
open import corpus.cubical_agda.Corridor.Running.CrossCut using (lo<hi-cut)
open import corpus.cubical_agda.Corridor.Running.LocatedLaw
  using (golden-lower-faithful; golden-upper-faithful)

-- ────────────────────────────────────────────────────────────────────────────
-- LOWER: every running lower-convergent is below the Dedekind φ.
--   ι (lo n) <ℝ φ  =  ∥ Σ r, (lo n < r) × ⟦ φL ⟧ r ∥₁
--   witness r = lo(n+1):  lo n < lo(n+1) [lo↗],  lo(n+1)² < lo(n+1)+1 [golden-lower].
-- ────────────────────────────────────────────────────────────────────────────

lo<φ : (n : ℕ) → ι (lo n) <ℝ φ
lo<φ n = ∣ lo (suc n) , (lo↗ n , ∣ inr (golden-lower-faithful (suc n)) ∣₁) ∣₁

-- 1 < hi(n+1): supplied by the Dedekind cut itself — lo 0 = 1 and lo 0 < hi(n+1).
1<hi : (n : ℕ) → 1 < hi (suc n)
1<hi n = subst (_< hi (suc n)) lo0≡1 (lo<hi-cut 0 (suc n))
  where
    lo0≡1 : lo 0 ≡ 1
    lo0≡1 = refl    -- lo 0 = F₂/F₁ = [ pos 1 / one ] = 1

-- ────────────────────────────────────────────────────────────────────────────
-- UPPER: every running upper-convergent is above the Dedekind φ.
--   φ <ℝ ι (hi n)  =  ∥ Σ r, ⟦ φU ⟧ r × (r < hi n) ∥₁,   φU r = (1<r)×(r+1<r²)
--   witness r = hi(n+1):  (1 < hi(n+1)) × (hi(n+1)+1 < hi(n+1)²) [golden-upper],
--   and hi(n+1) < hi n [hi↘].
-- ────────────────────────────────────────────────────────────────────────────

φ<hi : (n : ℕ) → φ <ℝ ι (hi n)
φ<hi n = ∣ hi (suc n)
         , ( ( 1<hi n , golden-upper-faithful (suc n) ) , hi↘ n ) ∣₁

-- ────────────────────────────────────────────────────────────────────────────
-- THE BRIDGE: the running corridor brackets the Dedekind φ at every rung.
-- ────────────────────────────────────────────────────────────────────────────

runs-to-cut : (n : ℕ) → (ι (lo n) <ℝ φ) × (φ <ℝ ι (hi n))
runs-to-cut n = lo<φ n , φ<hi n
