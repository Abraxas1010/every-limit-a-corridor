{-# OPTIONS --cubical --safe #-}
--
-- The genuine, non-vacuous core of the Effective Corridor.
--
-- HOSTILE-AUDIT REMEDIATION (2026-06-19).  The original corridor spine
-- realized its three load-bearing claims by DEGENERATE constructions:
--
--   * modal split:  shape = flat = sharp = id  (the only inhabited model,
--                   `connectedReflexiveRealCohesion`, sets every modality to
--                   the identity functor and `shapeFlatIso = idIso`), so every
--                   "cost-is-flat-wall" theorem reduced to  id ≡ id  by refl;
--   * re-entry:     `reentry (loop i) = markedShapePoint`  — the S¹ loop was
--                   sent to a CONSTANT, discarding its nontriviality;
--   * univalence:   `ua x = refl`  — a function NAMED after Voevodsky's axiom,
--                   DEFINED as the constant refl, so "exactness is univalence"
--                   proved  refl ≡ refl.
--
-- Each claim passed the Substitution Test trivially: replace shape/flat by id,
-- ua by λ_→refl, reentry by a constant — the proofs are unchanged because that
-- IS the construction.  This module replaces all three degenerate primitives
-- with the repo's GENUINE univalence machinery (`HottLane.BridgePrelude.ua`
-- built from `primGlue`, which COMPUTES) instantiated at the Laws-of-Form
-- crossing involution — the σ re-entry / √−1 half-turn that is the repo's own
-- mathematical spine — and proves the discriminators the degenerate versions
-- provably fail.
--
-- The corridor THESIS made non-vacuous here:
--   the LOWER wall (flat / cost) sees a genuine point-distinction
--   (`unmarked ≢ marked`); the UPPER wall (shape / continuity) dissolves it
--   along a path that is genuinely NOT refl (`crossing-path-nontrivial`); the
--   MODULUS is the period-two closure of the crossing (`crossing-period-two`,
--   the free-compute idempotent echo).  None of these are refl-by-degeneracy.
--
module corpus.cubical_agda.Corridor.CrossingCorridor where

open import Agda.Primitive.Cubical using () renaming (primINeg to ~_)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import corpus.cubical_agda.HottLane.BridgePrelude
  using ( ua ; transport ; LoFBoundaryState ; unmarked ; marked
        ; cross ; crossing-period-two )
open import corpus.cubical_agda.HottLane.InvolutionBorrow
  using ( crossEquiv ; borrowed-cross-transport ; borrowed-cross-transport' )

data ⊥ : Set where

-- ────────────────────────────────────────────────────────────────────────────
-- The lower wall (flat / cost): a genuine point-level distinction.
--
-- This is what makes the cost real.  In the degenerate model the two boundary
-- states were never apart in any sense the modality could not erase for free;
-- here the apartness is a kernel-checked refutation of identification.
-- ────────────────────────────────────────────────────────────────────────────

codeState : LoFBoundaryState → Set
codeState unmarked = ⊤
codeState marked   = ⊥

-- `unmarked ≢ marked`, proved by transporting `tt : codeState unmarked` along
-- the (hypothetical) identification into `codeState marked = ⊥`.
unmarked≢marked : unmarked ≡ marked → ⊥
unmarked≢marked p = transport (λ i → codeState (p i)) tt

marked≢unmarked : marked ≡ unmarked → ⊥
marked≢unmarked p = transport (λ i → codeState (p (~ i))) tt

-- ────────────────────────────────────────────────────────────────────────────
-- The upper wall (shape / continuity): the crossing path.
--
-- `ua crossEquiv` is genuine univalence on the genuine non-identity equivalence
-- `crossEquiv` (the LoF crossing).  Unlike the corridor's old `ua x = refl`,
-- this path COMPUTES: transport along it FLIPS the boundary state.
-- ────────────────────────────────────────────────────────────────────────────

crossing-path : LoFBoundaryState ≡ LoFBoundaryState
crossing-path = ua crossEquiv

reflPath : LoFBoundaryState ≡ LoFBoundaryState
reflPath _ = LoFBoundaryState

-- The continuity wall genuinely identifies the two cost-apart states.
upper-wall-transports : transport crossing-path unmarked ≡ marked
upper-wall-transports = borrowed-cross-transport

upper-wall-transports' : transport crossing-path marked ≡ unmarked
upper-wall-transports' = borrowed-cross-transport'

-- ────────────────────────────────────────────────────────────────────────────
-- THE NON-VACUITY DISCRIMINATOR.
--
-- The crossing path is genuinely NOT the trivial (refl) path.  This is exactly
-- the obligation `ua x = refl` could never meet: if the upper-wall path were
-- refl, transport would FIX `unmarked`, but it sends it to `marked`, and the
-- lower wall proves `marked ≢ unmarked`.
-- ────────────────────────────────────────────────────────────────────────────

crossing-path-nontrivial : crossing-path ≡ reflPath → ⊥
crossing-path-nontrivial q =
  unmarked≢marked (λ i → transport (q (~ i)) unmarked)

-- The dual refutation: the degenerate `ua x = refl` realization (the constant
-- path) provably CANNOT supply the upper-wall identification.  This is the
-- test-discrimination (D10) the original anti-vacuity oracle lacked: the
-- WRONG (refl) pattern fails the very obligation the corridor claims to meet.
trivial-path-cannot-cross : transport reflPath unmarked ≡ marked → ⊥
trivial-path-cannot-cross q = unmarked≢marked q

-- ────────────────────────────────────────────────────────────────────────────
-- The re-entry, carrying the S¹ loop GENUINELY (not as a constant).
--
-- The old `reentry (loop i) = markedShapePoint` discarded the loop.  Here the
-- loop is sent to the genuine crossing path, so the re-entry's monodromy is the
-- half-turn itself: transporting a state around the loop FLIPS it.
-- ────────────────────────────────────────────────────────────────────────────

data S¹ : Set where
  base : S¹
  loop : base ≡ base

reentryGenuine : S¹ → Set
reentryGenuine base     = LoFBoundaryState
reentryGenuine (loop i) = crossing-path i

-- The re-entry's loop carries the crossing: around the loop, `unmarked` flips.
reentry-loop-transports : transport (λ i → reentryGenuine (loop i)) unmarked ≡ marked
reentry-loop-transports = borrowed-cross-transport

-- ...and the loop image is genuinely nontrivial (it is the crossing path).
reentry-loop-nontrivial : (λ i → reentryGenuine (loop i)) ≡ reflPath → ⊥
reentry-loop-nontrivial = crossing-path-nontrivial

-- ────────────────────────────────────────────────────────────────────────────
-- The genuine corridor witness: the two walls are distinct, the modulus is the
-- period-two closure, and the upper-wall path is non-refl.  An inhabitant of
-- this record is a kernel-checked certificate that the corridor thesis holds
-- with content — no field is satisfiable by a degenerate (identity / refl /
-- constant) construction.
-- ────────────────────────────────────────────────────────────────────────────

record CrossingCorridorWitness : Set₁ where
  constructor crossing-corridor
  field
    -- lower wall: the cost distinction is real
    lower-wall-apart        : unmarked ≡ marked → ⊥
    -- upper wall: continuity dissolves the distinction along the crossing path
    upper-wall-identifies   : transport crossing-path unmarked ≡ marked
    -- the upper-wall path is genuinely non-refl (defeats `ua x = refl`)
    upper-wall-nontrivial   : crossing-path ≡ reflPath → ⊥
    -- the modulus closes after two steps (the free-compute idempotent echo)
    modulus-period-two      : ∀ x → cross (cross x) ≡ x
    -- the re-entry carries the loop nontrivially (defeats constant `reentry`)
    reentry-carries-loop    : transport (λ i → reentryGenuine (loop i)) unmarked ≡ marked

open CrossingCorridorWitness public

crossing-corridor-witness : CrossingCorridorWitness
crossing-corridor-witness = crossing-corridor
  unmarked≢marked
  upper-wall-transports
  crossing-path-nontrivial
  crossing-period-two
  reentry-loop-transports

-- A single packaged statement of "the two walls are genuinely distinct":
-- there is a state the lower wall keeps apart from its crossing-image while the
-- upper wall identifies them.
two-walls-genuinely-distinct :
  Σ LoFBoundaryState (λ s →
    Σ (s ≡ marked → ⊥) (λ _ → transport crossing-path s ≡ marked))
two-walls-genuinely-distinct =
  unmarked , (unmarked≢marked , upper-wall-transports)
