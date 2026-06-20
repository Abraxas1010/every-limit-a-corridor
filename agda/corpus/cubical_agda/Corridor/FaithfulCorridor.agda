{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE FAITHFUL CORRIDOR — both genuine facets unified.
--
-- HOSTILE-AUDIT REMEDIATION capstone. The corridor thesis has two facets the
-- degenerate model conflated into one trivial `RealCohesiveModalities`:
--
--   facet (1) COHESION   — the two walls are genuinely DIFFERENT functors:
--       the upper (shape/continuity) wall collapses the boundary's two points
--       to a single connected component, the lower (flat/cost) wall keeps them
--       apart.  Realized in `Foundations.FiniteCohesion` (`shape-not-flat`,
--       a genuine set-quotient adjunction, NOT `idIso`).
--
--   facet (2) UNIVALENCE — the target is reached by a genuine identification of
--       types: the Laws-of-Form crossing path `ua crossEquiv` is non-refl and
--       transport along it flips the boundary state.  Realized in
--       `Corridor.CrossingCorridor` (the σ re-entry / √−1 half-turn).
--
-- This module bundles both into one certificate and states the UNIFIED thesis:
-- on a two-point boundary, the lower (cost) wall keeps the points apart, while
-- the upper (continuity) wall connects them — in BOTH the cohesion sense
-- (shape is contractible) AND the univalence sense (the crossing path
-- identifies them).  Neither facet is satisfiable by an identity / refl /
-- constant construction; the discriminators below are the kernel-checked proof.
--
module corpus.cubical_agda.Corridor.FaithfulCorridor where

open import Cubical.Foundations.Prelude using (_≡_; isContr)
open import Cubical.Data.Empty using (⊥)

open import corpus.cubical_agda.Foundations.FiniteCohesion as FC
  using ( FaithfulCohesionWitness ; faithful-cohesion-witness
        ; shape ; flat ; realLine ; Carrier
        ; shape-realLine-isContr ; flat-realLine-not-isContr ; shape-not-flat )
open import corpus.cubical_agda.Corridor.CrossingCorridor as CC
  using ( CrossingCorridorWitness ; crossing-corridor-witness
        ; crossing-path ; upper-wall-transports ; crossing-path-nontrivial
        ; unmarked≢marked ; reflPath )
open import corpus.cubical_agda.HottLane.BridgePrelude
  using ( transport ; unmarked ; marked )

-- ────────────────────────────────────────────────────────────────────────────
-- The unified certificate: both facets, on the same two-point boundary.
-- ────────────────────────────────────────────────────────────────────────────

record FaithfulCorridor : Set₁ where
  constructor faithful-corridor
  field
    -- facet (1): the cohesion walls are genuinely distinct functors
    cohesion : FaithfulCohesionWitness
    -- facet (2): the univalence target is reached by a genuine non-refl path
    univalence : CrossingCorridorWitness

open FaithfulCorridor public

-- the two facets were proved with two (provably) empty types; bridge them.
private
  ccElim : CC.⊥ → ⊥
  ccElim ()

-- The two facets agree on what the LOWER (cost) wall does: it keeps the
-- boundary's two points apart.
--   * cohesion sense:  `flat realLine` is not contractible (Bool: true ≢ false);
--   * univalence sense: `unmarked ≢ marked`.
-- The two facets agree on what the UPPER (continuity) wall does: it connects
-- them.
--   * cohesion sense:  `shape realLine` IS contractible (one component);
--   * univalence sense: `transport crossing-path unmarked ≡ marked`, and the
--     path is genuinely non-refl.

faithful-corridor-witness : FaithfulCorridor
faithful-corridor-witness = faithful-corridor
  faithful-cohesion-witness
  crossing-corridor-witness

-- The unified upper-wall statement: the continuity wall connects the boundary
-- in BOTH senses simultaneously.
upper-wall-connects-cohesively : isContr (Carrier (shape realLine))
upper-wall-connects-cohesively = shape-realLine-isContr

upper-wall-connects-univalently : transport crossing-path unmarked ≡ marked
upper-wall-connects-univalently = upper-wall-transports

-- The unified lower-wall statement: the cost wall keeps the boundary apart in
-- BOTH senses.
lower-wall-separates-cohesively : isContr (Carrier (flat realLine)) → ⊥
lower-wall-separates-cohesively = flat-realLine-not-isContr

lower-wall-separates-univalently : unmarked ≡ marked → ⊥
lower-wall-separates-univalently p = ccElim (unmarked≢marked p)

-- The two non-vacuity discriminators, side by side: the upper wall is genuinely
-- nontrivial as a functor (cohesion) AND as a path (univalence).
walls-distinct-cohesively : Carrier (shape realLine) ≡ Carrier (flat realLine) → ⊥
walls-distinct-cohesively = shape-not-flat

walls-distinct-univalently : crossing-path ≡ reflPath → ⊥
walls-distinct-univalently p = ccElim (crossing-path-nontrivial p)
