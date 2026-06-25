{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

------------------------------------------------------------------------------
-- Theory/LogicalEntropyTEEBridge.agda — the H¹-screen ↔ topological-entanglement-entropy
-- bridge: the corridor's Ellerman logical entropy and the measurable TEE are ONE currency.
--
-- *** The vacancy this fills (corridor Frontier (i), the right first step). ***
-- The corridor's $H^1$ screen carries a logical-entropy "distinction content"; the
-- companion's quantum atlas carries the golden ratio as a quantum dimension.  The physical
-- observable that makes the screen measurable is the TOPOLOGICAL ENTANGLEMENT ENTROPY
-- γ = log D, with the total quantum dimension D² = Σ dᵢ² (Kitaev–Preskill / Levin–Wen; a
-- deformation-invariant, entropy-valued quantity).  Closing Frontier (i) "in the right
-- order" means FIRST pinning the observable as a theorem: the SAME Ellerman functional
-- h(π) = 1 − Σ pᵢ² that weighs the H¹ screen, applied to the TEE's quantum-dimension
-- distribution pᵢ = dᵢ²/D², is an exact invariant.  This module proves it.
--
-- *** What is genuinely new (substitution-body sense). ***
--  • `Dsq` : the total quantum dimension squared D² = 1 + φ² (the TEE datum), and
--    `tee-D-squared` : D² = 2 + φ exactly in ℤ[φ].
--  • `fib-qd-logical-entropy-two-fifths` : the Ellerman logical entropy of the Fibonacci
--    quantum-dimension distribution is EXACTLY 2/5 — proved as 5·(D⁴−Σdᵢ⁴) = 2·D⁴ in
--    ℤ[φ] (the irrational parts cancel: the screen's currency lands on a rational).
--  • `h-screen-one-half` : the corridor's order-two H¹ screen has logical entropy 1/2
--    (reusing `LogicalEntropy.h-fwit`) — the SAME functional, the same currency.
--
-- Together: the H¹ logical-entropy screen and the measurable TEE are bridged by one
-- functional, with exact values (1/2 on the screen, 2/5 on the Fibonacci TEE datum) and the
-- TEE total quantum dimension D² = 2+φ pinned in ℤ[φ].  The remaining genuinely-physical
-- step (identifying "spectral divergence" with the entanglement spectrum / the limit norm,
-- and confronting the ν=12/5 FQHE and string-net data) is empirical, not formal.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.LogicalEntropyTEEBridge where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Rationals using (ℚ; [_/_])
open import Cubical.Data.NatPlusOne using (1+_)
open import corpus.cubical_agda.Theory.GoldenRing
  using (Gφ; _+G_; _·G_; 0G; 1G; negG; φ; fromℤ)
open import corpus.cubical_agda.Theory.LogicalEntropy using (logicalEntropy; h-fwit)

--------------------------------------------------------------------------------
-- The Fibonacci modular data, in exact ℤ[φ]
--------------------------------------------------------------------------------

-- the squared quantum dimensions of the two anyon sectors: d²(𝟏) = 1, d²(τ) = φ².
dsq-vac dsq-tau : Gφ
dsq-vac = 1G
dsq-tau = φ ·G φ

-- **the total quantum dimension squared** D² = Σ dᵢ² = 1 + φ² (the TEE datum: γ = ½ log D²).
Dsq : Gφ
Dsq = dsq-vac +G dsq-tau

-- Σ (dᵢ²)² = 1 + φ⁴ (the "coincidence" weight before normalisation).
sumSqDim : Gφ
sumSqDim = (dsq-vac ·G dsq-vac) +G (dsq-tau ·G dsq-tau)

-- the (un-normalised) distinction content D⁴ − Σ(dᵢ²)² (numerator of h on pᵢ = dᵢ²/D²).
distinctions : Gφ
distinctions = (Dsq ·G Dsq) +G negG sumSqDim

--------------------------------------------------------------------------------
-- The bridge theorems
--------------------------------------------------------------------------------

-- **the TEE total quantum dimension, exact**: D² = 2 + φ in ℤ[φ] (since φ² = φ+1).
tee-D-squared : Dsq ≡ (fromℤ (pos 2)) +G φ
tee-D-squared = refl

-- **the Ellerman logical entropy of the Fibonacci quantum-dimension distribution is 2/5**:
-- 5·(D⁴ − Σ(dᵢ²)²) = 2·D⁴ in ℤ[φ], i.e. h = (D⁴−Σdᵢ⁴)/D⁴ = 2/5 (the φ-parts cancel).
fib-qd-logical-entropy-two-fifths :
  (fromℤ (pos 5) ·G distinctions) ≡ (fromℤ (pos 2) ·G (Dsq ·G Dsq))
fib-qd-logical-entropy-two-fifths = refl

-- **the corridor's order-two H¹ screen has logical entropy 1/2** — the SAME Ellerman
-- functional (Gini–Simpson distinction probability), here on the uniform two-block class.
h-screen-one-half : logicalEntropy (2 ∷ 2 ∷ []) ≡ [ pos 1 / (1+ 1) ]
h-screen-one-half = h-fwit
