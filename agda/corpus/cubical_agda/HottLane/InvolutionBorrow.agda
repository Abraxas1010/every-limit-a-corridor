{-# OPTIONS --cubical --safe #-}
-- The NONTRIVIAL borrows (H5, completed): with isoToIsEquiv vendored, the
-- bridge computes transports along genuinely non-identity equivalences:
--
--   * the LoF crossing involution: transport (ua crossEquiv) unmarked ≡ marked
--   * the integer successor:       transport (ua sucEquiv) (pos 0) ≡ pos 1
--
-- Each witness below is typed as a path and proved by REFL: the cubical
-- kernel REDUCES the Glue transport to the equivalence's forward map.  The
-- Lean fragment's mirror terms (`Hott.Rehome.crossedState`, and
-- `Id.coe (ua succEquiv) 0` from the universal cover) are stuck on the
-- `univalence` axiom — but `coe_ua` (Funext.lean) proves *propositionally*
-- exactly the values this kernel computes.  The borrow and the in-Lean
-- propositional rule now certify each other.

module corpus.cubical_agda.HottLane.InvolutionBorrow where

open import Agda.Primitive
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Cubical.Equiv
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import corpus.cubical_agda.HottLane.BridgePrelude
  using (ua; transport; LoFBoundaryState; unmarked; marked; cross;
         crossing-period-two)
open import corpus.cubical_agda.HottLane.IsoToEquiv
  using (Iso; iso; isoToEquiv)

-- ── The crossing as a genuine equivalence ───────────────────────────────────

crossEquiv : LoFBoundaryState ≃ LoFBoundaryState
crossEquiv = isoToEquiv (iso cross cross crossing-period-two crossing-period-two)

-- The completed involution borrow: the Lean term
-- `Hott.Rehome.crossedState := Id.coe lofCrossingIdentification .unmarked`
-- is stuck; HERE the same transport REDUCES to `marked`.
borrowed-cross-transport : transport (ua crossEquiv) unmarked ≡ marked
borrowed-cross-transport _ = marked

borrowed-cross-transport' : transport (ua crossEquiv) marked ≡ unmarked
borrowed-cross-transport' _ = unmarked

-- ── The integer successor (the universal cover's monodromy) ─────────────────

sucInt : Int → Int
sucInt (pos n) = pos (suc n)
sucInt (negsuc zero) = pos zero
sucInt (negsuc (suc n)) = negsuc n

predInt : Int → Int
predInt (pos zero) = negsuc zero
predInt (pos (suc n)) = pos n
predInt (negsuc n) = negsuc (suc n)

sucPred : ∀ z → sucInt (predInt z) ≡ z
sucPred (pos zero) _ = pos zero
sucPred (pos (suc n)) _ = pos (suc n)
sucPred (negsuc n) _ = negsuc n

predSuc : ∀ z → predInt (sucInt z) ≡ z
predSuc (pos n) _ = pos n
predSuc (negsuc zero) _ = negsuc zero
predSuc (negsuc (suc n)) _ = negsuc (suc n)

sucEquiv : Int ≃ Int
sucEquiv = isoToEquiv (iso sucInt predInt sucPred predSuc)

-- The cover-monodromy borrow: the Lean fragment's
-- `Id.coe (ua succEquiv) 0` (inside `Cover.cover_loop_coe`) is stuck;
-- here it REDUCES.
borrowed-suc-transport : transport (ua sucEquiv) (pos 0) ≡ pos 1
borrowed-suc-transport _ = pos 1

borrowed-suc-transport-neg : transport (ua sucEquiv) (negsuc 0) ≡ pos 0
borrowed-suc-transport-neg _ = pos 0
