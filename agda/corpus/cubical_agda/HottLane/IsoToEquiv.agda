{-# OPTIONS --cubical --safe #-}
-- isoToIsEquiv, vendored from primitives (the lemIso hcomp squares), so the
-- HoTT-lane bridge can borrow transports along NONTRIVIAL equivalences:
-- the named prerequisite of the H5 involution borrow.
--
-- Source of the construction: the standard cubical-library lemIso argument
-- (Cubical.Foundations.Isomorphism), reproduced here over the Agda builtins
-- only (this corpus vendors no cubical library; `hfill` is defined from
-- `primHComp` + `Sub` exactly as in Cubical.Core.Primitives).

module corpus.cubical_agda.HottLane.IsoToEquiv where

open import Agda.Primitive
open import Agda.Primitive.Cubical
  renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_;
            primHComp to hcomp; primTransp to transp; itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path using (_≡_; PathP)
open import Agda.Builtin.Cubical.Sub renaming (primSubOut to outS)
open import Agda.Builtin.Cubical.Equiv
open import Agda.Builtin.Sigma

private variable
  ℓ ℓ' : Level

hfill : {A : Set ℓ} {φ : I}
        (u : ∀ i → Partial φ A)
        (u0 : Sub A φ (u i0)) (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

-- An isomorphism: function, inverse, and the two homotopies.
record Iso (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : ∀ b → fun (inv b) ≡ b
    leftInv : ∀ a → inv (fun a) ≡ a

module _ {A : Set ℓ} {B : Set ℓ'} (i : Iso A B) where
  open Iso i renaming (fun to f; inv to g; rightInv to s; leftInv to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i j = hfill (λ k → λ { (i = i1) → t x0 k
                                 ; (i = i0) → g y })
                        (inS (g (p0 (~ i)))) j

      fill1 : I → I → A
      fill1 i j = hfill (λ k → λ { (i = i1) → t x1 k
                                 ; (i = i0) → g y })
                        (inS (g (p1 (~ i)))) j

      fill2 : I → I → A
      fill2 i j = hfill (λ k → λ { (i = i1) → fill1 k i1
                                 ; (i = i0) → fill0 k i1 })
                        (inS (g y)) j

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : _≡_ {A = Σ A (λ x → f x ≡ y)} (x0 , p0) (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .isEquiv.equiv-proof y .fst .fst = g y
  isoToIsEquiv .isEquiv.equiv-proof y .fst .snd = s y
  isoToIsEquiv .isEquiv.equiv-proof y .snd z =
    lemIso y (g y) (z .fst) (s y) (z .snd)

isoToEquiv : {A : Set ℓ} {B : Set ℓ'} → Iso A B → A ≃ B
isoToEquiv i = Iso.fun i , isoToIsEquiv i
