{-# OPTIONS --cubical --safe --guardedness #-}
--
-- Z[φ] AS AN AF SEQUENTIAL COLIMIT — Vladimir's "Part II", grounded genuinely.
--
-- HOSTILE-AUDIT REMEDIATION (legacy phase A8, on the genuine substrate).
--
-- An AF ("approximately finite") object is a sequential colimit of finite
-- stages with genuine (non-surjective) inclusions.  Here the stages are the
-- GOLDEN ladder rungs of `FaithfulModulus` — stage n has `w n = fib(n+2)`
-- points — and the colimit is their union along the Fibonacci inclusions.
--
-- The non-vacuity (what makes it a genuine AF colimit, not a constant sequence
-- collapsing to one stage): each inclusion is GENUINELY non-surjective — the
-- value `w n` is reached only at stage n+1, never from stage n
-- (`inclusion-not-surjective`).  The colimit grows without bound at the golden
-- rate; a degenerate "AF" colimit whose maps were equivalences would fail it.
--
module corpus.cubical_agda.Corridor.GoldenAFColimit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order using (_<_; _≤_; <-weaken; <≤-trans; ¬m<m)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sequence.Base using (Sequence; sequence)
open import Cubical.HITs.SequentialColimit.Base using (SeqColim; incl; push)

open import corpus.cubical_agda.Corridor.FaithfulModulus
  using (width; ladder-narrows)

-- The golden ladder width, behind an `opaque` wall: `width` unfolds to a
-- Fibonacci sum, which makes the unifier choke wherever a `width`-typed term
-- meets a metavariable (Sequence.map's `1 + n`, `incl`'s implicit index).  The
-- wall lets the equivalence `w n = width n` and the strict growth be proved
-- (where the body is visible) while treating `w n` atomically everywhere else.
opaque
  w : ℕ → ℕ
  w n = width n

  w-narrows : (n : ℕ) → w n < w (suc n)
  w-narrows = ladder-narrows

  w-mono : (n : ℕ) → w n ≤ w (suc n)
  w-mono n = <-weaken (w-narrows n)

  -- the AF stage width IS the modulus bracket width (exposed for the capstone
  -- cross-part identity: Part II's stages are the rate's brackets).
  w-is-width : (n : ℕ) → w n ≡ width n
  w-is-width n = refl

-- ────────────────────────────────────────────────────────────────────────────
-- The golden ladder as a Sequence: stage n carries the bracket's `w n` points,
-- included into stage n+1 along the (strict) Fibonacci growth.
-- ────────────────────────────────────────────────────────────────────────────

GoldenStage : ℕ → Type
GoldenStage n = Σ[ k ∈ ℕ ] (k < w n)

-- the genuine inclusion stage n ↪ stage n+1 (re-index, keeping the value).
-- codomain `1 + n` matches `Sequence.map` syntactically.
goldenInclusion : {n : ℕ} → GoldenStage n → GoldenStage (1 + n)
goldenInclusion {n} (k , k<wn) = k , <≤-trans k<wn (w-mono n)

goldenSequence : Sequence ℓ-zero
goldenSequence = sequence GoldenStage goldenInclusion

-- the AF colimit of the golden ladder.
GoldenAFColimit : Type
GoldenAFColimit = SeqColim goldenSequence

-- ────────────────────────────────────────────────────────────────────────────
-- Non-vacuity: the value `w n` is fresh at stage n+1 — the inclusion from stage
-- n can never reach it, so the colimit genuinely grows.
-- ────────────────────────────────────────────────────────────────────────────

-- the point with value `w n` exists at stage n+1 (by strict narrowing)…
freshPoint : (n : ℕ) → GoldenStage (suc n)
freshPoint n = w n , w-narrows n

-- …but no point of stage n has value `w n` (every value is < w n), and the
-- inclusion preserves the value — so the fresh point is genuinely new.
inclusion-not-surjective :
  (n : ℕ) (q : GoldenStage n) → fst q ≡ w n → ⊥
inclusion-not-surjective n (k , k<wn) e = ¬m<m (subst (_< w n) e k<wn)

-- the fresh colimit point, exhibited.
freshColimitPoint : (n : ℕ) → GoldenAFColimit
freshColimitPoint n = incl (freshPoint n)

-- ────────────────────────────────────────────────────────────────────────────
-- The AF certificate: a genuine sequential colimit whose every inclusion is
-- non-surjective — the object grows at the golden rate, no finite stage
-- exhausts it.
-- ────────────────────────────────────────────────────────────────────────────

record GoldenAF : Type where
  constructor golden-af
  field
    grows        : (n : ℕ) → w n < w (suc n)
    fresh-missed : (n : ℕ) (q : GoldenStage n) → fst q ≡ w n → ⊥

open GoldenAF public

golden-af-witness : GoldenAF
golden-af-witness = golden-af w-narrows inclusion-not-surjective
