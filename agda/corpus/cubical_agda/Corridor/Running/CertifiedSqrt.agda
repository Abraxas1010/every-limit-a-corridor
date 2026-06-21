{-# OPTIONS --cubical --safe --guardedness #-}
--
-- CERTIFIED √x BY BISECTION — a running corridor for an arbitrary non-negative
-- rational's square root.  `sqrtBracket x 0≤x D` returns a rational interval
-- [lo,hi] with `lo² ≤ x ≤ hi²`, computed by D steps of bisection of [0, x+1].
-- The bound invariant `lo²≤x≤hi²` is maintained by the decidable midpoint test:
-- whichever half contains √x keeps the invariant by construction.  This is the
-- general √ the spectral edge needs (the discriminant has no Pell structure).
--
module corpus.cubical_agda.Corridor.Running.CertifiedSqrt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_≤_; _<_; <Dec; ≮→≥; <Weaken≤; ≤-·o; ≤-+o; isTrans≤)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (x<x+1)

private
  half : ℚ
  half = [ pos 1 / 1+ 1 ]

IsSqrtBracket : (x lo hi : ℚ) → Type₀
IsSqrtBracket x lo hi = ((lo · lo) ≤ x) × (x ≤ (hi · hi))

-- ── the bisection loop, carrying the bound invariant ────────────────────────
bisect : (x lo hi : ℚ) → (lo · lo) ≤ x → x ≤ (hi · hi) → ℕ
       → Σ[ lo' ∈ ℚ ] Σ[ hi' ∈ ℚ ] IsSqrtBracket x lo' hi'
bisect x lo hi plo phi zero    = lo , hi , (plo , phi)
bisect x lo hi plo phi (suc k) = go (<Dec x (mid · mid))
  where
    mid : ℚ
    mid = (lo + hi) · half
    go : Dec (x < (mid · mid)) → Σ[ lo' ∈ ℚ ] Σ[ hi' ∈ ℚ ] IsSqrtBracket x lo' hi'
    go (yes x<mid²) = bisect x lo  mid plo                     (<Weaken≤ x (mid · mid) x<mid²) k
    go (no ¬x<mid²) = bisect x mid hi  (≮→≥ x (mid · mid) ¬x<mid²) phi                    k

-- ── initial bracket [0, x+1]:  0² = 0 ≤ x  and  x ≤ (x+1)² ──────────────────
init-lo : (x : ℚ) → 0 ≤ x → (0 · 0) ≤ x
init-lo x 0≤x = subst (_≤ x) (sym (·AnnihilL 0)) 0≤x

-- x ≤ x+1 ≤ (x+1)(x+1)   [the right step needs 1 ≤ x+1, i.e. 0 ≤ x]
init-hi : (x : ℚ) → 0 ≤ x → x ≤ ((x + 1) · (x + 1))
init-hi x 0≤x = isTrans≤ x (x + 1) ((x + 1) · (x + 1)) x≤x+1 x+1≤sq
  where
    x≤x+1 : x ≤ (x + 1)
    x≤x+1 = <Weaken≤ x (x + 1) (x<x+1 x)
    0≤x+1 : 0 ≤ (x + 1)
    0≤x+1 = isTrans≤ 0 x (x + 1) 0≤x x≤x+1
    1≤x+1 : 1 ≤ (x + 1)
    1≤x+1 = subst (_≤ (x + 1)) (+IdL 1) (≤-+o 0 x 1 0≤x)
    x+1≤sq : (x + 1) ≤ ((x + 1) · (x + 1))
    x+1≤sq = subst (_≤ ((x + 1) · (x + 1))) (·IdL (x + 1))
                   (≤-·o 1 (x + 1) (x + 1) 0≤x+1 1≤x+1)

sqrtBracket : (x : ℚ) → 0 ≤ x → (D : ℕ)
            → Σ[ lo ∈ ℚ ] Σ[ hi ∈ ℚ ] IsSqrtBracket x lo hi
sqrtBracket x 0≤x D = bisect x 0 (x + 1) (init-lo x 0≤x) (init-hi x 0≤x) D
