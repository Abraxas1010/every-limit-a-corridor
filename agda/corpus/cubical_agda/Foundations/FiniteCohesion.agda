{-# OPTIONS --cubical --safe --guardedness #-}
--
-- A FAITHFUL finite real-cohesion model — the genuine substitute for the
-- corridor's degenerate `connectedReflexiveRealCohesion` (shape=flat=sharp=id).
--
-- HOSTILE-AUDIT REMEDIATION, facet (1) — cohesion.
-- (See Docs/reports/effective_corridor_hostile_audit_2026-06-19.md; facet (2),
-- genuine univalence/re-entry, is `Corridor.CrossingCorridor`.)
--
-- The audit's root-cause finding: on the bare signature
-- `CohesiveType = {Carrier : Set}` with bare-function `Hom`, a Yoneda/copower
-- argument forces `shape ∈ {id, const}` — so a faithful cohesion is IMPOSSIBLE
-- there and the corridor's "two distinct walls" collapse to `id ≡ id`.  The fix
-- enriches the type with cohesion data (an equivalence relation = "in the same
-- connected piece") and the morphisms with cohesion-preservation.  Then the
-- adjoint triple `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` is GENUINE and the modalities
--
--     shape A = Disc (Π₀ A)      flat A = Disc (Γ A)      sharp A = coDisc (Γ A)
--
-- are genuinely DIFFERENT functors: on the real line `shape` collapses the two
-- boundary points to a single connected component (it is contractible) while
-- `flat` keeps them apart.  That difference — the whole content the degenerate
-- model faked — is the theorem `shape-not-flat` below.
--
-- The construction reuses the verified cubical-library witnesses
-- (`setQuotUniversalIso`, `true≢false`, `isContrUnit`, h-levels): the faithful
-- model is assembled from existing lego blocks, not re-derived.
--
module corpus.cubical_agda.Foundations.FiniteCohesion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso; iso; compIso; invIso; isoToPath)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; ΣPathP; _×_)
open import Cubical.Data.Unit using (Unit; tt; isContrUnit; isPropUnit)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.HITs.SetQuotients
  using (_/_; [_]; eq/; squash/; setQuotUniversalIso; elimProp)

private variable ℓ : Level

-- ────────────────────────────────────────────────────────────────────────────
-- A cohesive type: a set with a prop-valued equivalence relation (the cohesion
-- = "lies in the same connected piece").
-- ────────────────────────────────────────────────────────────────────────────

record CohesiveType : Type₁ where
  constructor cohesive
  field
    Carrier  : Type
    car-set  : isSet Carrier
    Rel      : Carrier → Carrier → Type
    rel-prop : (x y : Carrier) → isProp (Rel x y)
    rel-refl : (x : Carrier) → Rel x x
    rel-sym  : (x y : Carrier) → Rel x y → Rel y x
    rel-trans : (x y z : Carrier) → Rel x y → Rel y z → Rel x z

open CohesiveType public

-- Cohesion-preserving maps.  THIS is the change the Yoneda obstruction forces:
-- morphisms are no longer bare functions, they carry preservation of cohesion.
CHom : CohesiveType → CohesiveType → Type
CHom A B =
  Σ[ f ∈ (Carrier A → Carrier B) ]
    ((x y : Carrier A) → Rel A x y → Rel B (f x) (f y))

-- ────────────────────────────────────────────────────────────────────────────
-- The discrete and codiscrete coreflections, and the three modalities.
-- ────────────────────────────────────────────────────────────────────────────

Disc : (X : Type) → isSet X → CohesiveType
Disc X Xset = cohesive X Xset _≡_
  (λ x y → Xset x y)
  (λ _ → refl)
  (λ _ _ p → sym p)
  (λ _ _ _ p q → p ∙ q)

coDisc : (X : Type) → isSet X → CohesiveType
coDisc X Xset = cohesive X Xset (λ _ _ → Unit)
  (λ _ _ → isPropUnit)
  (λ _ → tt)
  (λ _ _ _ → tt)
  (λ _ _ _ _ _ → tt)

-- Π₀ A = connected components = the set-quotient by the cohesion.
Pi0 : CohesiveType → Type
Pi0 A = Carrier A / Rel A

-- shape = Disc ∘ Π₀ : collapse each connected piece to a point, then make discrete.
shape : CohesiveType → CohesiveType
shape A = Disc (Pi0 A) squash/

-- flat = Disc ∘ Γ : keep the points, forget the cohesion (everything apart).
flat : CohesiveType → CohesiveType
flat A = Disc (Carrier A) (car-set A)

-- sharp = coDisc ∘ Γ : keep the points, make everything cohesive.
sharp : CohesiveType → CohesiveType
sharp A = coDisc (Carrier A) (car-set A)

-- ────────────────────────────────────────────────────────────────────────────
-- The genuine shape ⊣ flat adjunction.
--
-- `CHom (shape A) B` = maps out of the discrete component-set, whose
-- preservation obligation is automatic; `CHom A (flat B)` = maps `A → B`
-- constant on cohesion-classes — exactly the set-quotient universal property.
-- This is NOT `idIso`: it is the descent isomorphism of the quotient.
-- ────────────────────────────────────────────────────────────────────────────

-- preservation for a map out of a discrete (shape) source is canonical
discPresv : {A B : CohesiveType} (g : Pi0 A → Carrier B) →
  (x y : Pi0 A) → x ≡ y → Rel B (g x) (g y)
discPresv {B = B} g x y p = subst (λ z → Rel B (g x) z) (cong g p) (rel-refl B (g x))

isPropPresvShape : {A B : CohesiveType} (g : Pi0 A → Carrier B) →
  isProp ((x y : Pi0 A) → x ≡ y → Rel B (g x) (g y))
isPropPresvShape {B = B} g =
  isPropΠ2 (λ x y → isPropΠ (λ _ → rel-prop B (g x) (g y)))

-- step 1: forget the (propositional, canonical) preservation field
shapeHomIso : (A B : CohesiveType) → Iso (CHom (shape A) B) (Pi0 A → Carrier B)
shapeHomIso A B = iso
  fst
  (λ g → g , discPresv {A} {B} g)
  (λ g → refl)
  (λ h → ΣPathP (refl , isPropPresvShape {A} {B} (fst h) (discPresv {A} {B} (fst h)) (snd h)))

-- step 2: the set-quotient universal property IS the rest of the adjunction
shapeFlatIso : (A B : CohesiveType) → Iso (CHom (shape A) B) (CHom A (flat B))
shapeFlatIso A B =
  compIso (shapeHomIso A B) (setQuotUniversalIso (car-set B))

-- ────────────────────────────────────────────────────────────────────────────
-- The real line and the DISCRIMINATION: shape collapses it, flat keeps it apart.
-- This is the content the degenerate `shape A = A` model could never carry.
-- ────────────────────────────────────────────────────────────────────────────

-- the real line: two boundary points, totally cohesive (one connected piece).
realLine : CohesiveType
realLine = cohesive Bool isSetBool (λ _ _ → Unit)
  (λ _ _ → isPropUnit)
  (λ _ → tt)
  (λ _ _ _ → tt)
  (λ _ _ _ _ _ → tt)

-- the upper wall (shape) collapses the line to a single point: it is connected.
shape-realLine-isContr : isContr (Carrier (shape realLine))
shape-realLine-isContr =
  [ true ] , λ x → elimProp (λ y → squash/ [ true ] y) (λ b → eq/ true b tt) x

-- the lower wall (flat) keeps the two points apart: it is NOT connected.
flat-realLine-not-isContr : isContr (Carrier (flat realLine)) → ⊥
flat-realLine-not-isContr c = true≢false (isContr→isProp c true false)

-- THE DISCRIMINATION: `shape` and `flat` are genuinely different functors —
-- they disagree on the real line.  If their carriers there were equal, the
-- contractibility of the shape would transport to the flat, forcing the two
-- boundary points equal — impossible.
shape-not-flat :
  Carrier (shape realLine) ≡ Carrier (flat realLine) → ⊥
shape-not-flat p =
  flat-realLine-not-isContr (subst isContr p shape-realLine-isContr)

-- The corridor thesis, faithfully: a single state the lower wall keeps apart
-- from its image (Bool: true ≢ false) while the upper wall identifies all
-- states (shape is contractible).  No field is satisfiable by an identity model.
record FaithfulCohesionWitness : Type₁ where
  constructor faithful-cohesion
  field
    upper-wall-connects   : isContr (Carrier (shape realLine))
    lower-wall-separates  : isContr (Carrier (flat realLine)) → ⊥
    walls-distinct        : Carrier (shape realLine) ≡ Carrier (flat realLine) → ⊥
    adjunction-genuine    : (A B : CohesiveType) → Iso (CHom (shape A) B) (CHom A (flat B))

open FaithfulCohesionWitness public

faithful-cohesion-witness : FaithfulCohesionWitness
faithful-cohesion-witness = faithful-cohesion
  shape-realLine-isContr
  flat-realLine-not-isContr
  shape-not-flat
  shapeFlatIso
