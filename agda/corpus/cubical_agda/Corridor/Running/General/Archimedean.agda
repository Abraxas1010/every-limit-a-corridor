{-# OPTIONS --cubical --safe --guardedness #-}
--
-- ℚ IS ARCHIMEDEAN — the foundational unlock for the located-real completion.
--
-- The repo search found the located-completion machinery already built: the organism's
-- `RealApprox.trisect-n` brackets any Dedekind real with width EXACTLY (2/3)ⁿ·(c−a).  The
-- only missing piece was the convergence (2/3)ⁿ → 0, which rests on ℚ being Archimedean:
--      ∀ ε > 0,  ∃ n,  1/(n+1) < ε.
-- The witness is simply n = the DENOMINATOR of ε:  for ε = p/q with p ≥ 1, take n = |q|;
-- then 1/(|q|+1) < p/q  because  q < p·(|q|+1).  This closes the last analytic gap between
-- the corridor's bracket machinery and the spectral-radius located real.
--
module corpus.cubical_agda.Corridor.Running.General.Archimedean where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; ℕ₊₁→ℕ)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)
open import Cubical.Data.Int using (ℤ; pos; sucℤ) renaming (_·_ to _·ℤ_)
open import Cubical.Data.Int.Properties renaming (·IdL to ·IdLℤ; ·IdR to ·IdRℤ) using (·IdLℤ; ·IdRℤ)
open import Cubical.Data.Int.Order using (_≤_; ≤-·o; isTrans≤; isRefl≤; suc-≤-suc) renaming (_<_ to _<ℤ_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_)
open import Cubical.HITs.SetQuotients using (elimProp)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Foundations.HLevels using (isPropΠ)

-- ℚ is Archimedean: for any positive rational, a unit fraction lies below it.
ℚ-archimedean : (ε : ℚ) → 0 < ε → ∥ Σ[ n ∈ ℕ ] ([ pos 1 / 1+ n ] < ε) ∥₁
ℚ-archimedean = elimProp (λ ε → isPropΠ (λ _ → squash₁)) helper
  where
    helper : (pq : ℤ × ℕ₊₁) → 0 < [ fst pq / snd pq ]
           → ∥ Σ[ n ∈ ℕ ] ([ pos 1 / 1+ n ] < [ fst pq / snd pq ]) ∥₁
    helper (p , q) 0<ε = ∣ ℕ₊₁→ℕ q , goal ∣₁
      where
        Q : ℕ
        Q = ℕ₊₁→ℕ q
        -- 0 < [p/q] unfolds (ℤ) to  pos 0 · ℕ₊₁→ℤ q < p · pos 1  ; reshape ⟹ pos 1 ≤ p.
        1≤p : pos 1 ≤ p
        1≤p = subst (pos 1 ≤_) (·IdRℤ p) 0<ε
        Q<sucQ : pos Q <ℤ pos (suc Q)
        Q<sucQ = isRefl≤
        sucQ≤p·sucQ : pos (suc Q) ≤ (p ·ℤ pos (suc Q))
        sucQ≤p·sucQ = subst (_≤ (p ·ℤ pos (suc Q))) (·IdLℤ (pos (suc Q)))
                        (≤-·o {k = suc Q} 1≤p)
        goal : [ pos 1 / 1+ Q ] < [ p / q ]
        goal = subst (_<ℤ (p ·ℤ pos (suc Q))) (sym (·IdLℤ (pos Q)))
                 (isTrans≤ Q<sucQ sucQ≤p·sucQ)
