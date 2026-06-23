{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE QUADRATIC-IRRATIONAL CORRIDORS — metallic ratios and √D as located Dedekind reals  (Item B).
--
-- The metallic ratio of k is the larger root of x² = kx + 1, namely (k + √(k²+4))/2: the golden ratio
-- (k=1), silver (k=2), bronze (k=3), ….  Each is exactly the spectral edge of [[k,1],[1,0]] — its
-- discriminant is (k−0)² + 4·1² = k²+4 and its trace is k — so metallic k = specEdge k 1 0 falls out of
-- the spectral-edge construction for FREE.  The √D corridor is just sqrtReal D.  Every quadratic
-- irrational is now a located real, with NO new analysis — the whole family is one reparametrization
-- of the constructive square root.
--
module corpus.cubical_agda.Corridor.Running.General.MetallicReal where

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ)
open import corpus.cubical_agda.Corridor.Running.General.SqrtReal using (sqrtReal)
open import corpus.cubical_agda.Corridor.Running.General.SpectralEdgeReal using (specEdge)

-- the metallic ratio of k:  the larger root of x² = kx + 1  =  (k + √(k²+4))/2.
metallic : (k : ℚ) → ℝ
metallic k = specEdge k 1 0

-- the named members of the family.
golden silver bronze : ℝ
golden = metallic 1        -- (1 + √5)/2
silver = metallic 2        -- 1 + √2
bronze = metallic 3        -- (3 + √13)/2

-- the √D corridor:  the located square root of any nonnegative rational.
sqrtCorridor : (D : ℚ) → 0 ≤ D → ℝ
sqrtCorridor D 0≤D = sqrtReal D 0≤D
