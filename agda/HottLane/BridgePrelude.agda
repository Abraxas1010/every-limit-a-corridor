{-# OPTIONS --cubical --safe #-}
-- HoTT-lane bridge prelude (Phase H5): the cubical twin of
-- lean/HeytingLean/Hott/Prelude.lean.
--
-- Two roles:
--
-- 1. CANONICITY BY BORROWING.  `ua` here is built from `primGlue` and
--    *computes*: `borrowed-id-transport` below is `refl` — the literal term
--    `transport (ua (idEquiv Int)) (pos 0)` REDUCES to `pos 0` in this kernel.
--    The mirror Lean term `Id.coe (ua (idEquiv Int)) 0` is STUCK (its footprint
--    contains the `univalence` axiom; `scripts/hott_agda_bridge.py` checks the
--    stuckness on the Lean side and the computation on this side, and ledgers
--    the pair).  This is the Cerioli–Meseguer borrowing round trip of the
--    proposal's H5, v1.
--
--    Named scope: the v1 borrow is along the *identity* equivalence — already a
--    genuine borrow (Lean cannot reduce even that term: `univalence` is an
--    axiom regardless of which equivalence it eats), but the involution borrow
--    `transport (ua crossEquiv) unmarked ≡ marked` is queued behind vendoring
--    `isoToIsEquiv` (the lemIso hcomp squares) into this corpus.
--
-- 2. SATISFACTION-CONDITION SEED.  The fragment sentence "the LoF crossing is a
--    bi-invertible equivalence" (`lean/HeytingLean/Hott/Rehome/LoFCrossing.lean`)
--    is re-checked here verbatim (`crossBiInv`): one sentence, two kernels, the
--    per-construct obligation of the H5 comorphism pair.

module corpus.cubical_agda.HottLane.BridgePrelude where

open import Agda.Primitive
open import Agda.Primitive.Cubical
  renaming (primINeg to ~_; primIMax to _∨_; primTransp to transp)
open import Agda.Builtin.Cubical.Path using (_≡_; PathP)
open import Agda.Builtin.Cubical.Equiv
open import Agda.Builtin.Cubical.Glue using (primGlue)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Int using (Int; pos; negsuc)

-- The identity equivalence, with its fiber contraction by connections.
idIsEquiv : ∀ {ℓ} (A : Set ℓ) → isEquiv (λ (a : A) → a)
idIsEquiv A .isEquiv.equiv-proof y =
  (y , (λ _ → y)) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j)

idEquiv : ∀ {ℓ} (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , idIsEquiv A

-- Univalence, computed: the Glue construction (this is a THEOREM of the
-- cubical kernel, not an axiom — the asymmetry the borrow exploits).
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {_} {A} {B} e i =
  primGlue B (λ { (i = i0) → A ; (i = i1) → B })
             (λ { (i = i0) → e ; (i = i1) → idEquiv B })

transport : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- ── The borrowed computation ────────────────────────────────────────────────
-- In Lean: `Id.coe (ua (idEquiv Int)) 0` is stuck on the `univalence` axiom.
-- Here the same transport REDUCES: this `refl`-typed definition is the
-- kernel-checked witness that the cubical side computes what Lean postulates.
borrowed-id-transport : transport (ua (idEquiv Int)) (pos 0) ≡ pos 0
borrowed-id-transport _ = pos 0

-- A second point, to witness uniformity of the reduction (negative payload).
borrowed-id-transport-neg : transport (ua (idEquiv Int)) (negsuc 4) ≡ negsuc 4
borrowed-id-transport-neg _ = negsuc 4

-- ── The satisfaction-condition seed: one sentence, two kernels ──────────────

-- Bi-invertibility, exactly the fragment's `IsEquiv` shape (separate left and
-- right inverses) — NOT the contractible-fibers `isEquiv` above.
record BiInv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  field
    inv-left  : B → A
    left      : ∀ a → inv-left (f a) ≡ a
    inv-right : B → A
    right     : ∀ b → f (inv-right b) ≡ b

-- The Laws-of-Form boundary carrier and crossing, mirrored from
-- lean/HeytingLean/HoTTBridge/LawsOfForm.lean.
data LoFBoundaryState : Set where
  unmarked marked : LoFBoundaryState

cross : LoFBoundaryState → LoFBoundaryState
cross unmarked = marked
cross marked = unmarked

crossing-period-two : ∀ x → cross (cross x) ≡ x
crossing-period-two unmarked _ = unmarked
crossing-period-two marked _ = marked

-- The fragment sentence, checked in this kernel: crossing is bi-invertible.
crossBiInv : BiInv cross
crossBiInv = record
  { inv-left = cross ; left = crossing-period-two
  ; inv-right = cross ; right = crossing-period-two }
