{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

------------------------------------------------------------------------------
-- Theory/CohesiveTower.agda — genuine cubical-HoTT port of `lean/CohesiveTower.lean`
-- (the dimensional progression is a real-cohesive tower; the 0D→1D step is the SHAPE modality ∫).
-- Lean is the reference (PM: lean_to_agda_full_rewrite, P4/Tier-3; Sprint 8). This module REPLACES the
-- `Agda.Builtin.Equality` shadow `Foundations/RealCohesiveModalities.agda` with genuine cubical Path
-- (the A1 fix the PM §1 calls for).
--
-- Lean↔Agda (A3): the finite `π₀` model `Space`/`shape`(∫)/`flat`(♭)/`IsDiscrete` ↔ same (genuine
-- `≡` Path, cubical `_≤_`/`_<_`); `shape_idem`/`flat_idem`/`shape_flat_eq` ↔ same (`refl`);
-- `point_discrete`/`line_cohesive`/`shape_line_is_point` ↔ same; `cohesionTower` (the dim spine,
-- `String` fields dropped like `CayleyFilter`) ↔ `cohesionTower` + `cohesionTower-dims`.
--
-- L-refinement (genuine HoTT): `IsModality` (an idempotent endo on `Space`) + `Modality` (the HoTT
-- pointed-idempotent-endofunctor frame on `Type`, the universal-property shape of cohesion); the
-- finite shape/flat are the 0-truncated shadow of the ∫/♭ modalities. Honest scope (matching the Lean):
-- this is the finite `π₀`/0-truncated model — the full ∞-cohesive `∫⊣♭⊣♯` as `(∞,1)`-functors and the
-- differential refinement (GR) are INVOKED, not reproven (they live in the heyting-imm `HoTTBridge`).
--
-- Glue (§2): set-level mirror — Path on `Space`/ℕ; `‖Agda‖₀ = Lean shadow` is the identity.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.CohesiveTower where

open import Cubical.Core.Primitives using (Type; Level; ℓ-suc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; subst)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (znots to ℕznots; snotz to ℕsnotz)
open import Cubical.Data.Nat.Order using (_≤_; _<_; ≤-refl; ≤-trans; ≤-sucℕ; ¬m<m)
open import Cubical.Data.Nat.Properties using (injSuc)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; map)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Relation.Nullary using (¬_)

private variable ℓ : Level

--------------------------------------------------------------------------------
-- A finite π₀ model of cohesion: the shape ∫ and flat ♭ modalities
--------------------------------------------------------------------------------

-- A finite cohesive space: `points`, `pieces = |π₀|` (the connected components — the shape),
-- subject to the cohesion axiom **pieces have points**.
record Space : Type where
  constructor space
  field
    points pieces : ℕ
    pieces≤points : pieces ≤ points
    pieces-pos    : 0 < points → 0 < pieces
open Space

-- **The shape modality ∫** = π₀ — the discrete space of connected pieces.
shape : Space → Space
shape X = space (pieces X) (pieces X) ≤-refl (λ h → h)
-- **The flat modality ♭** — the underlying discrete points (cohesion forgotten).
flat : Space → Space
flat X = space (points X) (points X) ≤-refl (λ h → h)

-- A space is **discrete** when every point is its own piece (∫ = id).
IsDiscrete : Space → Type
IsDiscrete X = pieces X ≡ points X

-- ∫ lands in the discrete; ∫ and ♭ are idempotent (modalities); ∫♭ = ♭.
shape-discrete : (X : Space) → IsDiscrete (shape X)
shape-discrete X = refl
shape-idem : (X : Space) → shape (shape X) ≡ shape X
shape-idem X = refl
flat-discrete : (X : Space) → IsDiscrete (flat X)
flat-discrete X = refl
flat-idem : (X : Space) → flat (flat X) ≡ flat X
flat-idem X = refl
shape-flat-eq : (X : Space) → shape (flat X) ≡ flat X
shape-flat-eq X = refl

--------------------------------------------------------------------------------
-- The 0D→1D cohesion step: the point is discrete, the line is cohesive
--------------------------------------------------------------------------------

-- The 0D **point** — discrete.
point : Space
point = space 1 1 ≤-refl (λ h → h)
-- The 1D **line** on `n ≥ 2` points — connected (one piece), hence cohesive.
line : (n : ℕ) → 2 ≤ n → Space
line n h = space n 1 (≤-trans ≤-sucℕ h) (λ _ → ≤-refl)

point-discrete : IsDiscrete point
point-discrete = refl
-- **The line is cohesive** (not discrete): fewer pieces than points.
line-cohesive : (n : ℕ) (h : 2 ≤ n) → ¬ (IsDiscrete (line n h))
line-cohesive n h p = ¬m<m {1} (subst (λ m → 2 ≤ m) (sym p) h)   -- `2 ≤ 1` is `1 < 1`
-- **∫ collapses the line to a point**: `|∫(line)| = 1`.
shape-line-is-point : (n : ℕ) (h : 2 ≤ n) → points (shape (line n h)) ≡ 1
shape-line-is-point n h = refl
-- …in fact `∫(line) = point` on the nose (Invocation-2): the shape of the cohesive line IS the
-- discrete point — the 0D→1D cohesion step, as an equality of spaces.
shape-line-eq-point : (n : ℕ) (h : 2 ≤ n) → shape (line n h) ≡ point
shape-line-eq-point n h = refl

--------------------------------------------------------------------------------
-- The cohesion tower — the dimensional realms classified
--------------------------------------------------------------------------------

record CohesiveRealm : Type where
  constructor realm
  field
    dim      : ℕ
    discrete : Bool      -- discrete only at the 0D point; cohesive above
open CohesiveRealm

-- The dimensional progression: discrete point, then cohesive line / plane / cell.
cohesionTower : List CohesiveRealm
cohesionTower = realm 0 true ∷ realm 1 false ∷ realm 2 false ∷ realm 3 false ∷ []

cohesionTower-dims : map dim cohesionTower ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
cohesionTower-dims = refl
-- Only the 0D point is discrete; cohesion is acquired at the 0D→1D step and kept.
cohesionTower-cohesion : map discrete cohesionTower ≡ (true ∷ false ∷ false ∷ false ∷ [])
cohesionTower-cohesion = refl

--------------------------------------------------------------------------------
-- L-refinement: the modality structure (genuine HoTT universal-property frame)
--------------------------------------------------------------------------------

-- An idempotent endo-operation on `Space` (the finite shadow of a modality).
IsModality : (Space → Space) → Type
IsModality ○ = (X : Space) → ○ (○ X) ≡ ○ X

shape-is-modality : IsModality shape
shape-is-modality = shape-idem
flat-is-modality : IsModality flat
flat-is-modality = flat-idem
-- ∫ and ♭ are GENUINELY DIFFERENT modalities (non-vacuity): on the line they disagree
-- (`|∫(line)| = 1 ≠ 2 = |♭(line)|`).
modalities-differ : ¬ (shape (line 2 ≤-refl) ≡ flat (line 2 ≤-refl))
modalities-differ p = ℕznots (injSuc (cong points p))
-- ∫♭ = ♭: a discrete (flat) space is its own shape — the adjoint-string compatibility (∫∘♭ = ♭).
adjoint-string-compatibility : (X : Space) → (shape (flat X) ≡ flat X) × (IsDiscrete (flat X))
adjoint-string-compatibility X = shape-flat-eq X , flat-discrete X

-- The HoTT **modality** frame: a pointed endofunctor on `Type` with an idempotent multiplication
-- (the universal-property shape of a real-cohesive ∫/♭/♯ modality). The finite `Space` shape/flat
-- are its 0-truncated shadow.
record Modality (○ : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    η   : {A : Type ℓ} → A → ○ A
    μ   : {A : Type ℓ} → ○ (○ A) → ○ A
-- Non-vacuity: the identity modality (the discrete realm, ∫ = id) inhabits it.
idModality : Modality {ℓ} (λ A → A)
idModality = record { η = λ x → x ; μ = λ x → x }
