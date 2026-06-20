{-# OPTIONS --cubical --safe --guardedness #-}
--
-- NEGATIVE CONTROL for the agda-boundary runtime-roundtrip authority lane.
--
-- This module is INTENTIONALLY REJECTED by the Agda kernel. It is the
-- `forced_true_substitution_must_fail` control: it forces the corridor's
-- boundary distinction to COLLAPSE (true ≡ false via refl) — the degenerate
-- substitution the hostile audit refuted. The kernel rejects `refl` at type
-- `true ≡ false` (distinct constructors), so a degenerate witness cannot
-- manufacture the genuine discriminator. The producer
-- `scripts/agda_boundary_runtime_roundtrip.py` REQUIRES this module to FAIL
-- `agda --cubical --safe`; if it ever compiles, the authority lane is broken.
--
module corpus.cubical_agda.Corridor.negative_controls.BadForcedTrueCollapse where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.Data.Bool using (Bool; true; false)

forced-true-collapse : true ≡ false
forced-true-collapse = refl
