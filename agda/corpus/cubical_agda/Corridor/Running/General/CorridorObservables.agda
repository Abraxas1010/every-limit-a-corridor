{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE CORRIDOR'S OBSERVABLES — the catalogue row for "the corridor"  (Item E, logical-entropy provenance).
--
-- A number-system object in the IAOM catalogue is characterised by four observables.  For the running
-- golden corridor:
--   (1) ALGEBRAIC BEHAVIOUR    : the golden quadratic x² = x + 1 (GoldenCut φ's located law).
--   (2) PROVENANCE COST μ(D)=D : to reach rung D you climb D Cassini steps — a strictly increasing,
--                                 non-constant ladder depth.
--   (3) LOGICAL ENTROPY        : ½ — the Ellerman distinction-content of the balanced ±1 Cassini sign,
--                                 EXACTLY the organism's H¹ cohomological screen (EntropyProvenance).
--   (4) BARE-METAL NODE COUNT  : the interaction-net size of the lowered bracket — supplied by Phase D
--                                 (the Boundary lowering); recorded here as the pending fourth column.
-- The discriminating control (HC-E): logical entropy is OBJECT-DEPENDENT, not a universal constant —
-- the trivial partition has 0, the corridor ½, the trisection engine's three-block object ⅔.  Distinct
-- objects carry distinct distinction-content, so the observable genuinely measures.
--
module corpus.cubical_agda.Corridor.Running.General.CorridorObservables where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Order using () renaming (_<_ to _<ℕ_)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <Dec)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_×_; _,_)
open import corpus.cubical_agda.Corridor.Running.General.EntropyProvenance
  using (logicalEntropy2; entropy2-zero; entropy2-half)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _ = a

-- ── (2) PROVENANCE COST: the Cassini/convergent ladder depth to reach rung D. ──
provenanceCost : ℕ → ℕ
provenanceCost D = D

-- discriminating: the cost strictly grows with depth (it is not a flat constant).
provenance-grows : (D : ℕ) → provenanceCost D <ℕ provenanceCost (suc D)
provenance-grows D = 0 , refl

-- ── (3) LOGICAL ENTROPY: the corridor's balanced Cassini-sign value ½. ──────────
corridorEntropy : ℚ
corridorEntropy = logicalEntropy2 [ pos 1 / 1+ 1 ]      -- = ½  (entropy2-half)

-- ── HC-E CONTROL: entropy is object-dependent, not a universal constant. ────────
-- the trisection engine's three-block object (masses ⅓,⅓,⅓): h = 1 − 3·(⅓)² = ⅔.
trisectionEntropy : ℚ
trisectionEntropy =
  1 - ((onethird · onethird) + ((onethird · onethird) + (onethird · onethird)))
  where onethird = [ pos 1 / 1+ 2 ]

trisection-twothirds : trisectionEntropy ≡ [ pos 2 / 1+ 2 ]
trisection-twothirds = getYes (discreteℚ trisectionEntropy [ pos 2 / 1+ 2 ]) tt

-- across OBJECTS: trivial 0 < corridor ½ < trisection ⅔ — three distinct values.
entropy-discriminates-objects : (0 < corridorEntropy) × (corridorEntropy < trisectionEntropy)
entropy-discriminates-objects =
    getYes (<Dec 0 corridorEntropy) tt
  , getYes (<Dec corridorEntropy trisectionEntropy) tt

-- ── THE CATALOGUE ROW for "the corridor". ──────────────────────────────────────
record CorridorRow : Type₀ where
  field
    cost     : ℕ → ℕ            -- (2) provenance cost μ
    entropy  : ℚ               -- (3) logical entropy
    -- (1) algebraic behaviour is the golden quadratic x²=x+1 (GoldenCut φ's located law);
    -- (4) bare-metal node count is supplied by Phase D and recorded there.
    entropy≡½ : entropy ≡ [ pos 1 / 1+ 1 ]

the-corridor : CorridorRow
the-corridor = record
  { cost = provenanceCost
  ; entropy = corridorEntropy
  ; entropy≡½ = entropy2-half
  }
