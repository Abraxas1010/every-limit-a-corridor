{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

------------------------------------------------------------------------------
-- Theory/LogicalEntropy.agda — genuine cubical-HoTT port of `lean/LogicalEntropy.lean`
-- (Ellerman's LOGICAL entropy = a COUNT of distinctions: for a partition, `h = |distinctions| / |U|²`
-- is the probability two random draws land in different blocks, and the Gini–Simpson identity
-- `h = 1 − Σpᵢ²` is distinction-counting because indistinctions = `Σ|block|²` and every ordered pair is
-- one or the other). Lean is the reference (PM: lean_to_agda_full_rewrite, P5/Tier-2; Sprint 18 —
-- THE FIRST ℚ-DIVISION UNBLOCK, using the `RationalField` constructed in Sprint 17).
--
-- *** This is the flagship demonstration that the constructed ℚ-field unblocks the ℚ stratum. ***
-- Sprint 7 deferred this on "ℚ-field + Finset gap, BOTH"; ℚ-division is now built (`RationalField`)
-- and the Finset is sidestepped by representing a partition by its block-SIZE LIST.
--
-- Lean↔Agda (A3): `logicalEntropy` / `mono_card` (indistinctions = Σ|block|²) / the fundamental
-- identity / `logicalEntropy_fwit` (`h = 1/2` on the balanced 4-partition) ↔ same. DEVIATION: the
-- `Fintype`/`Finset.filter.card` partition ↦ a block-size `List ℕ` (`total = Σ`, `sumSq = Σ(·²)`,
-- `distinctions = |U|² ∸ Σ|block|²` — faithful, the entropy depends only on the block sizes). The
-- identity `h = 1 − Σpᵢ²` is delivered in CLEARED form `h · |U|² = distinctions` (= the
-- distinction-count, via the field law `·-linv` — avoiding fraction-subtraction algebra).
--
-- Glue (§2): set-level mirror. Ties to the Observer/entropy arc (the third value M of Ω₃ as logical
-- entropy `1/3`; `1 − Σpᵢ² = h`). Uses `RationalField.invℚ`/`_/ℚ_`/`·-linv-pos`.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.LogicalEntropy where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_; _∸_)
open import Cubical.Data.Nat.Properties using (+-comm; +∸)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; ≤-refl; ≤-k+)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_)
open import Cubical.Data.List using (List; []; _∷_; map; foldr)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Rationals using (ℚ; [_/_]; ·Assoc; ·IdR) renaming (_·_ to _·ℚ_)
open import Cubical.HITs.SetQuotients using (eq/)
open import Cubical.Tactics.NatSolver using (solveℕ!)
open import corpus.cubical_agda.Theory.RationalField using (invℚ; _/ℚ_; oneℚ; ·-linv-pos)

--------------------------------------------------------------------------------
-- The combinatorial core (block sizes; "entropy = distinction counting")
--------------------------------------------------------------------------------

sumList : List ℕ → ℕ
sumList = foldr _+_ 0

-- A partition of a finite set, given by its block sizes. `total = |U|`, `sumSq = Σ|block|²`.
total : List ℕ → ℕ
total = sumList
sumSq : List ℕ → ℕ
sumSq bs = sumList (map (λ b → b · b) bs)
-- distinctions = `|U|² − Σ|block|²` (the ordered pairs the partition separates).
distinctions : List ℕ → ℕ
distinctions bs = (total bs · total bs) ∸ sumSq bs

-- `a + (b ∸ a) ≡ b` for `a ≤ b`.
private
  addMonus : (a b : ℕ) → a ≤ b → (a + (b ∸ a)) ≡ b
  addMonus a b (d , p) = cong (a +_) (cong (_∸ a) (sym p) ∙ +∸ d a) ∙ +-comm a d ∙ p

-- **`Σ|block|² ≤ |U|²`** — the indistinctions never exceed the total ordered pairs (the cross terms
-- `2·bᵢ·bⱼ ≥ 0`). The combinatorial fact underlying `0 ≤ h ≤ 1`.
private
  expand : (b T : ℕ) → (((b · T) + (T · b)) + ((b · b) + (T · T))) ≡ ((b + T) · (b + T))
  expand b T = solveℕ!

sumSq-le : (bs : List ℕ) → sumSq bs ≤ (total bs · total bs)
sumSq-le []         = ≤-refl
sumSq-le (b ∷ rest) = ≤-trans step1 step2
  where
  T = total rest
  step1 : ((b · b) + sumSq rest) ≤ ((b · b) + (T · T))
  step1 = ≤-k+ (sumSq-le rest)
  step2 : ((b · b) + (T · T)) ≤ ((b + T) · (b + T))
  step2 = ((b · T) + (T · b)) , expand b T

-- **The complementary count** `distinctions + indistinctions = |U|²` — every ordered pair is a
-- distinction or an indistinction (`Σ|block|²`). This IS "logical entropy counts distinctions".
complementary : (bs : List ℕ) → (distinctions bs + sumSq bs) ≡ (total bs · total bs)
complementary bs = +-comm (distinctions bs) (sumSq bs)
                 ∙ addMonus (sumSq bs) (total bs · total bs) (sumSq-le bs)

--------------------------------------------------------------------------------
-- Logical entropy over ℚ (the ℚ-division unblock) + the Gini–Simpson identity
--------------------------------------------------------------------------------

-- the ℕ → ℚ embedding `n ↦ [n/1]`.
ℕ→ℚ : ℕ → ℚ
ℕ→ℚ n = [ pos n / (1+ 0) ]

-- **Logical entropy** `h = |distinctions| / |U|²` (now a genuine ℚ, via the constructed division).
logicalEntropy : List ℕ → ℚ
logicalEntropy bs = ℕ→ℚ (distinctions bs) /ℚ ℕ→ℚ (total bs · total bs)

-- **The Gini–Simpson identity, cleared** (`h · |U|² = distinctions`): normalizing the entropy by the
-- total ordered-pair count recovers the distinction count — `h = 1 − Σpᵢ²` with denominators cleared,
-- via the field law `q⁻¹·q = 1`. (For any nonempty `|U|²= suc K`.)
gini-simpson-cleared : (d K : ℕ) → ((ℕ→ℚ d /ℚ [ pos (suc K) / (1+ 0) ]) ·ℚ [ pos (suc K) / (1+ 0) ]) ≡ ℕ→ℚ d
gini-simpson-cleared d K =
    sym (·Assoc (ℕ→ℚ d) (invℚ [ pos (suc K) / (1+ 0) ]) [ pos (suc K) / (1+ 0) ])
  ∙ cong (ℕ→ℚ d ·ℚ_) (·-linv-pos K (1+ 0))
  ∙ ·IdR (ℕ→ℚ d)

--------------------------------------------------------------------------------
-- Concrete witnesses (the ℚ-division actually computes the entropy)
--------------------------------------------------------------------------------

-- **The balanced 2-block partition of a 4-element set has `h = 1/2`** (Lean `logicalEntropy_fwit`):
-- `|U|=4`, `8` distinctions out of `16` ordered pairs, `8/16 = 1/2`. The ℚ-division COMPUTES it.
h-fwit : logicalEntropy (2 ∷ 2 ∷ []) ≡ [ pos 1 / (1+ 1) ]
h-fwit = eq/ _ _ refl    -- `[8/16] ∼ [1/2]`: `8·2 ≡ 1·16` (both `16`), by `refl`

-- **A single block has zero entropy** (`h = 0`): no distinctions (`|U|² = Σ|block|²`).
h-single : logicalEntropy (4 ∷ []) ≡ [ pos 0 / (1+ 0) ]
h-single = eq/ _ _ refl    -- `[0/16] ∼ [0/1]`: `0·1 ≡ 0·16` (both `0`), by `refl`

-- The Gini–Simpson identity on the 4-partition: `h · |U|² = 8` (the distinction count).
fundamental-fwit : (logicalEntropy (2 ∷ 2 ∷ []) ·ℚ [ pos 16 / (1+ 0) ]) ≡ ℕ→ℚ 8
fundamental-fwit = gini-simpson-cleared 8 15

--------------------------------------------------------------------------------
-- Invocation-2: the GENERAL Gini–Simpson identity + the σ-orbit (Koide) tie
--------------------------------------------------------------------------------

-- **The Gini–Simpson identity for ANY nonempty partition**: `h · |U|² = distinctions`. Normalizing
-- the entropy by the total ordered-pair count recovers the distinction count — for every partition
-- whose `|U|²` is positive (`≡ suc K`). The full Ellerman identity, denominators cleared.
entropy-fundamental : (bs : List ℕ) (K : ℕ) → (total bs · total bs) ≡ suc K
  → (logicalEntropy bs ·ℚ [ pos (suc K) / (1+ 0) ]) ≡ ℕ→ℚ (distinctions bs)
entropy-fundamental bs K eq =
    cong (_·ℚ [ pos (suc K) / (1+ 0) ]) (cong (λ z → ℕ→ℚ (distinctions bs) /ℚ [ pos z / (1+ 0) ]) eq)
  ∙ gini-simpson-cleared (distinctions bs) K

-- **The three-generation σ-orbit has logical entropy `2/3`** (3 singleton blocks of a 3-element set:
-- `9 − 3 = 6` distinctions, `6/9 = 2/3`). This is the Koide purity complement `1 − Q = 1/3`'s dual:
-- `Q = 2/3` is the σ-orbit purity, `h = 2/3` here is the distinction probability of the ℤ/3 orbit —
-- the logical-entropy reading of the three values of Ω₃. Computed by the ℚ-division (`refl` ∼).
h-three-orbit : logicalEntropy (1 ∷ 1 ∷ 1 ∷ []) ≡ [ pos 2 / (1+ 2) ]
h-three-orbit = eq/ _ _ refl    -- `[6/9] ∼ [2/3]`: `6·3 ≡ 2·9` (both `18`)
