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
open import Cubical.Data.Int using (ℤ; pos; negsuc; sucℤ) renaming (_·_ to _·ℤ_)
open import Cubical.Data.Int.Properties renaming (·IdL to ·IdLℤ; ·IdR to ·IdRℤ; ·Comm to ·Commℤ) using (·IdLℤ; ·IdRℤ; ·Commℤ)
open import Cubical.Data.Int.Order using (_≤_; ≤-·o; 0≤o→≤-·o; isTrans≤; isRefl≤; suc-≤-suc; negsuc<pos; zero-≤pos) renaming (_<_ to _<ℤ_)
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

-- ── the dual: ℕ is cofinal in ℚ (every rational lies below some natural) ──────
-- Together with ℚ-archimedean this is the full two-sided Archimedean property —
-- the foundation that lets trisect-n's geometric width (2/3)ⁿ·D be driven below
-- any ε (the D factor needs a natural ABOVE a rational; ε needs one BELOW it).

ℤ<pos : (a : ℤ) → Σ[ m ∈ ℕ ] (a <ℤ pos (suc m))
ℤ<pos (pos k)    = k , isRefl≤
ℤ<pos (negsuc k) = 0 , negsuc<pos

ℕ-cofinal : (r : ℚ) → ∥ Σ[ n ∈ ℕ ] (r < [ pos n / 1 ]) ∥₁
ℕ-cofinal = elimProp (λ _ → squash₁) helper
  where
    helper : (ab : ℤ × ℕ₊₁) → ∥ Σ[ n ∈ ℕ ] ([ fst ab / snd ab ] < [ pos n / 1 ]) ∥₁
    helper (a , 1+ b') with ℤ<pos a
    ... | (m , a<sucm) = ∣ suc m , goal ∣₁
      where
        1≤B : pos 1 ≤ pos (suc b')
        1≤B = suc-≤-suc zero-≤pos
        sm≤prod : pos (suc m) ≤ (pos (suc m) ·ℤ pos (suc b'))
        sm≤prod = subst2 _≤_ (·Commℤ (pos 1) (pos (suc m)) ∙ ·IdRℤ (pos (suc m)))
                            (·Commℤ (pos (suc b')) (pos (suc m)))
                            (0≤o→≤-·o zero-≤pos 1≤B)
        goal : [ a / 1+ b' ] < [ pos (suc m) / 1 ]
        goal = subst (_<ℤ (pos (suc m) ·ℤ pos (suc b'))) (sym (·IdRℤ a))
                 (isTrans≤ a<sucm sm≤prod)
