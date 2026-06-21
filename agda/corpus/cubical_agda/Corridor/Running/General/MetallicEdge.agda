{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE METALLIC RATIOS ARE SPECTRAL EDGES — B meets F.
--
-- metallic m = (m+√(m²+4))/2 is the larger eigenvalue of the companion matrix
-- [[m,1],[1,0]] (whose powers generate the m-Fibonacci ladder, Metallic.kfib).
-- Its characteristic discriminant is (m−0)²+4·1² = m²+4, so Phase F's certified
-- spectral-edge bisection brackets it directly.  In particular:
--   • golden  φ      = metallic 1 = spectral edge of [[1,1],[1,0]], Δ = 5
--   • silver  1+√2   = metallic 2 = spectral edge of [[2,1],[1,0]], Δ = 8
--   • bronze (3+√13)/2 = metallic 3 = spectral edge of [[3,1],[1,0]], Δ = 13
-- This unifies the two frontier strands: the metallic family (B) is exactly the
-- spectral edges (F) of its own generating matrices, certified to any depth.
--
module corpus.cubical_agda.Corridor.Running.General.MetallicEdge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Sigma using (Σ; _,_; _×_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_)
open import corpus.cubical_agda.Corridor.Running.CertifiedSqrt using (IsSqrtBracket)
open import corpus.cubical_agda.Corridor.Running.SpectralEdge using (discriminant; specEdgeBracket)

-- the certified bracket of the m-th metallic ratio = the spectral edge of [[m,1],[1,0]].
metallicEdgeBracket : (m : ℚ) → 0 ≤ discriminant m 1 0 → (D : ℕ)
  → Σ[ loλ ∈ ℚ ] Σ[ hiλ ∈ ℚ ]
      Σ[ slo ∈ ℚ ] Σ[ shi ∈ ℚ ]
        IsSqrtBracket (discriminant m 1 0) slo shi
        × (loλ ≡ ((m + 0) + slo) · [ pos 1 / 1+ 1 ])
        × (hiλ ≡ ((m + 0) + shi) · [ pos 1 / 1+ 1 ])
metallicEdgeBracket m = specEdgeBracket m 1 0

-- the metallic discriminants reduce: Δ(1)=5 (golden), Δ(2)=8 (silver), Δ(3)=13 (bronze).
_ : discriminant 1 1 0 ≡ 5
_ = refl
_ : discriminant 2 1 0 ≡ 8
_ = refl
_ : discriminant 3 1 0 ≡ 13
_ = refl
