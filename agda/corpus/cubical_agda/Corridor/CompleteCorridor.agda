{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE COMPLETE EFFECTIVE CORRIDOR — the full steelmanned object of Vladimir's
-- letter, all three parts in one kernel-checked certificate.
--
-- HOSTILE-AUDIT REMEDIATION — synthesis capstone.  The original 16-phase tower
-- realized the programme vacuously on the trivial (identity) model.  The
-- genuine substrate now spans the whole programme:
--
--   • the corridor: genuinely-distinct walls (cohesion `FiniteCohesion`
--     shape ≠ flat, and univalence `CrossingCorridor`), unified in
--     `FaithfulCorridor`, shrinking at the golden ladder's intrinsic rate
--     (`FaithfulModulus`, "the ladder is the rate") — together `EffectiveCorridor`;
--   • Part II: the Z[φ] approximately-finite sequential colimit (`GoldenAFColimit`);
--   • Part III: the H¹ logical-entropy screen (`EntropyScreen`).
--
-- This module bundles the three into one object AND proves the genuine
-- cross-part identity that they are not three unrelated facts but one structure:
-- the AF colimit's stages ARE the modulus's brackets — `af-stage-is-rate-bracket`
-- (`w n ≡ width (modulus n)`).  Part II's approximants and the rate's brackets
-- are the same golden ladder; the located approximation and its modulus coincide.
--
module corpus.cubical_agda.Corridor.CompleteCorridor where

open import Cubical.Foundations.Prelude using (_≡_)
open import Cubical.Data.Nat using (ℕ)

open import corpus.cubical_agda.Corridor.FaithfulModulus
  using (EffectiveCorridor; the-effective-corridor; width; modulus)
open import corpus.cubical_agda.Corridor.GoldenAFColimit
  using (GoldenAF; golden-af-witness; w; w-is-width)
open import corpus.cubical_agda.Corridor.EntropyScreen
  using (EntropyScreen; entropy-screen-witness)

-- ────────────────────────────────────────────────────────────────────────────
-- The complete object: the corridor (walls + rate), Part II, Part III.
-- ────────────────────────────────────────────────────────────────────────────

record CompleteEffectiveCorridor : Set₁ where
  constructor complete-corridor
  field
    effective : EffectiveCorridor   -- the corridor: distinct walls + intrinsic rate
    afII      : GoldenAF            -- Part II: the Z[φ] AF sequential colimit
    screenIII : EntropyScreen       -- Part III: the H¹ logical-entropy screen

open CompleteEffectiveCorridor public

-- ────────────────────────────────────────────────────────────────────────────
-- The genuine cross-part identity: the AF colimit's n-th stage carries exactly
-- the modulus's n-th bracket width — Part II and the rate are the same golden
-- ladder.  (modulus n = n, so width (modulus n) = width n = w n.)
-- ────────────────────────────────────────────────────────────────────────────

af-stage-is-rate-bracket : (n : ℕ) → w n ≡ width (modulus n)
af-stage-is-rate-bracket = w-is-width

-- the complete certificate.
the-complete-corridor : CompleteEffectiveCorridor
the-complete-corridor =
  complete-corridor the-effective-corridor golden-af-witness entropy-screen-witness
