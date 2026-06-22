{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GEOMETRIC BOUND, ℚ LEVEL — (4/9)ᵏ ≤ 1/(k+1).
--
-- Lifts GeometricBoundN.geomBoundℕ (4ᵏ·(k+1) ≤ 9ᵏ) to ℚ by cross-multiplication: with
-- pow49 k := [4ᵏ / 9ᵏ], the bound pow49 k ≤ 1/(k+1) IS that integer inequality (the ℚ-≤
-- unfolds to 4ᵏ·(k+1) ≤ 9ᵏ via the cross-multiplied form, with the denominator 9ᵏ carried
-- as a ℕ₊₁ whose ℕ₊₁→ℕ image is 9ᵏ — a refl homomorphism).  This is the explicit-modulus
-- convergence at the rational level: (4/9)ᵏ ≤ 1/(k+1) → 0, which with the two-sided
-- Archimedean drives trisect-n's width below any ε.
--
module corpus.cubical_agda.Corridor.Running.General.GeometricBoundQ where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _·_; _+_)
open import Cubical.Data.Nat.Order using () renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; ℕ₊₁→ℕ; _·₊₁_)
open import Cubical.Data.Int using (ℤ; pos) renaming (_·_ to _·ℤ_)
open import Cubical.Data.Int.Properties using (pos·pos) renaming (·IdL to ·IdLℤ)
open import Cubical.Data.Int.Order renaming (_≤_ to _≤ℤ_)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Rationals using (ℚ; [_/_]; ℕ₊₁→ℤ)
open import Cubical.Data.Rationals.Order using (_≤_)
open import corpus.cubical_agda.Corridor.Running.General.GeometricBoundN using (p4; p9; geomBoundℕ)

-- ℕ₊₁→ℕ is a multiplicative homomorphism (re-derived; the library's is private).
ℕ₊₁→ℕ-· : (m n : ℕ₊₁) → ℕ₊₁→ℕ (m ·₊₁ n) ≡ ℕ₊₁→ℕ m · ℕ₊₁→ℕ n
ℕ₊₁→ℕ-· (1+ m) (1+ n) = refl

-- pos is monotone:  m ≤ n  ⟹  pos m ≤ pos n.
posMono : {m n : ℕ} → m ≤ℕ n → pos m ≤ℤ pos n
posMono {m} {n} (k , p) = k , (sym (pos+ m k) ∙ cong pos (+-comm m k ∙ p))
  where open import Cubical.Data.Int using (pos+)
        open import Cubical.Data.Nat using (+-comm)

-- 9ᵏ as a positive denominator.
p9₊₁ : ℕ → ℕ₊₁
p9₊₁ zero    = 1+ 0
p9₊₁ (suc k) = (1+ 8) ·₊₁ p9₊₁ k

p9₊₁≡ : (k : ℕ) → ℕ₊₁→ℕ (p9₊₁ k) ≡ p9 k
p9₊₁≡ zero    = refl
p9₊₁≡ (suc k) = ℕ₊₁→ℕ-· (1+ 8) (p9₊₁ k) ∙ cong (9 ·_) (p9₊₁≡ k)

-- (4/9)ᵏ as a running rational, in lowest-friction form 4ᵏ/9ᵏ.
pow49 : ℕ → ℚ
pow49 k = [ pos (p4 k) / p9₊₁ k ]

-- THE BOUND:  (4/9)ᵏ ≤ 1/(k+1).
pow49-bound : (k : ℕ) → pow49 k ≤ [ pos 1 / 1+ k ]
pow49-bound k = subst2 _≤ℤ_ lhsEq rhsEq (posMono (geomBoundℕ k))
  where
    -- posMono (geomBoundℕ k) : pos (p4 k · suc k) ≤ pos (p9 k)
    lhsEq : pos (p4 k · suc k) ≡ (pos (p4 k) ·ℤ ℕ₊₁→ℤ (1+ k))
    lhsEq = pos·pos (p4 k) (suc k)
    rhsEq : pos (p9 k) ≡ (pos 1 ·ℤ ℕ₊₁→ℤ (p9₊₁ k))
    rhsEq = sym (cong pos (p9₊₁≡ k)) ∙ sym (·IdLℤ (ℕ₊₁→ℤ (p9₊₁ k)))
