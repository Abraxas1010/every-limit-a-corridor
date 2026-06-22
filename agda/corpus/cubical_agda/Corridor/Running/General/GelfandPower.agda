{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GELFAND/TRACE ROUTE TO THE SPECTRAL RADIUS — a foreign-field attack on the
-- eigendecomposition gap.
--
-- The operator norm of a symmetric matrix is its spectral radius, and Gelfand's
-- formula computes it from RATIONAL data without finding eigenvectors:
--      ‖M‖ = lim_k (tr(M^{2k}))^{1/2k}            (tr(M^{2k}) = Σ λᵢ^{2k} ∈ ℚ).
-- Its exact algebraic core — reachable now as pure matrix algebra — is the power law
--      (M⋆M)^k ≡ M^{2k}                            [sqPow]
-- so M²'s power-traces ARE M's even-power-traces (tr((M²)^k) = tr(M^{2k})), which is the
-- trace-level content of the C*-identity ‖M²‖=‖M‖² (both sides → ρ(M)² in the limit).
-- This complements the spectral route (SpectralCStar / DiagonalCStar): two independent
-- reductions of the operator-norm C*-identity to a final located-real limit, neither
-- needing the eigenvectors.  Proven over any commutative ring via the cubical Matrix
-- library's ⋆Assoc + unit laws.
--
module corpus.cubical_agda.Corridor.Running.General.GelfandPower where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-suc)
open import Cubical.Algebra.CommRing using (CommRing)
open import Cubical.Algebra.Matrix.CommRingCoefficient

module GP (𝓡 : CommRing ℓ-zero) where
  open Coefficient 𝓡

  -- matrix power.
  _^^_ : {n : ℕ} → Mat n n → ℕ → Mat n n
  M ^^ zero    = 𝟙
  M ^^ (suc k) = M ⋆ (M ^^ k)

  -- THE POWER LAW:  (M⋆M)^k ≡ M^{k+k}  — M²'s powers are M's even powers.
  sqPow : {n : ℕ} (M : Mat n n) (k : ℕ) → (M ⋆ M) ^^ k ≡ M ^^ (k + k)
  sqPow M zero    = refl
  sqPow M (suc k) =
      cong ((M ⋆ M) ⋆_) (sqPow M k)
    ∙ sym (⋆Assoc M M (M ^^ (k + k)))
    ∙ cong (M ^^_) (sym (cong suc (+-suc k k)))

  -- consequence: the squared matrix's k-th power equals the original's (2k)-th —
  -- the exact spectral-radius bridge ρ(M²)=ρ(M)² lives in the limit of the traces of
  -- these (rational) powers.
  spectralPowerBridge : {n : ℕ} (M : Mat n n) (k : ℕ)
                      → (M ⋆ M) ^^ k ≡ M ^^ (k + k)
  spectralPowerBridge = sqPow
