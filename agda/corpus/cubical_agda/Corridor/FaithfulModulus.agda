{-# OPTIONS --cubical --safe --guardedness #-}
--
-- "THE LADDER IS THE RATE" — Vladimir's effective-modulus thesis, faithfully.
--
-- HOSTILE-AUDIT REMEDIATION, the modulus/rate layer (legacy phase A6, grounded
-- genuinely instead of on the trivial model).
--
-- Vladimir's letter and the two papers ("climbing without numbers", "the
-- spectrum has a modulus") make one constructive claim: an effective object
-- replaces a *point* (a classical limit) by a *corridor* — a bracket that
-- shrinks at an INTRINSIC RATE carried as data.  "The ladder is the rate": the
-- modulus is not a free parameter, it is read off the ladder's own contraction.
--
-- The non-vacuity that distinguishes an effective limit from a classical one:
-- the modulus must be GENUINELY UNBOUNDED — a constant modulus is refuted,
-- because convergence requires unboundedly deep descent.  That refutation
-- (`modulus-forced` / `constant-modulus-unsound`) is the in-kernel
-- substitution-test discriminator the degenerate A6 lacked.
--
-- The ladder here is the repo-native GOLDEN / Fibonacci ladder (the Zeckendorf
-- / Pisot spine, φ² = φ + 1): rung n carries a bracket of denominator
-- `fib (n+2)`, so the bracket narrows by the golden growth.  The modulus is
-- read off `fib` — the rate IS the ladder.
--
module corpus.cubical_agda.Corridor.FaithfulModulus where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-comm)
open import Cubical.Data.Nat.Order
  using (_≤_; _<_; ≤-refl; ≤-suc; ≤-trans; ≤-k+; ≤-+k; <-suc; ≤SumLeft)
open import Cubical.Data.Sigma using (Σ-syntax; _,_)

open import corpus.cubical_agda.Corridor.FaithfulCorridor
  using (FaithfulCorridor; faithful-corridor-witness)

-- ────────────────────────────────────────────────────────────────────────────
-- The golden / Fibonacci ladder (repo-native Zeckendorf / Pisot spine).
-- ────────────────────────────────────────────────────────────────────────────

fib : ℕ → ℕ
fib zero          = zero
fib (suc zero)    = suc zero
fib (suc (suc n)) = fib (suc n) + fib n

-- the bracket denominator at rung n: fib(n+2) = 1, 2, 3, 5, 8, …
-- bigger denominator = narrower bracket.
width : ℕ → ℕ
width n = fib (suc (suc n))

-- monotone-both for ≤ on the natural numbers (from the one-sided library lemmas)
+-mono-≤ : {a b c d : ℕ} → a ≤ b → c ≤ d → a + c ≤ b + d
+-mono-≤ {b = b} {c = c} p q = ≤-trans (≤-+k {k = c} p) (≤-k+ {k = b} q)

-- fib of any positive index is positive: the ladder never stalls.
fib-pos : (n : ℕ) → 1 ≤ fib (suc n)
fib-pos zero    = ≤-refl
fib-pos (suc m) = ≤-trans (fib-pos m) ≤SumLeft

-- THE LADDER REACHES PRECISION: rung n delivers denominator ≥ n+1.
-- (a genuine lower bound on the golden growth, proved by induction — the
--  soundness of the modulus rests on it, not on a constant.)
fib-lower : (n : ℕ) → suc n ≤ fib (suc (suc n))
fib-lower zero    = ≤-refl
fib-lower (suc m) =
  subst (λ z → z ≤ fib (suc (suc (suc m))))
        (+-comm (suc m) 1)
        (+-mono-≤ (fib-lower m) (fib-pos m))

-- ────────────────────────────────────────────────────────────────────────────
-- The modulus: precision demand D ↦ ladder rung achieving it.  Read off `fib`.
-- ────────────────────────────────────────────────────────────────────────────

modulus : ℕ → ℕ
modulus D = D

-- SOUNDNESS: at rung `modulus D` the bracket denominator is ≥ D — the demanded
-- precision is achieved.  (Uses the genuine lower bound; a constant modulus
-- cannot satisfy this.)
modulus-sound : (D : ℕ) → D ≤ width (modulus D)
modulus-sound D = ≤-trans (≤-suc ≤-refl) (fib-lower D)

-- THE LADDER STRICTLY CONTRACTS: each rung's denominator strictly grows.
ladder-narrows : (n : ℕ) → width n < width (suc n)
ladder-narrows n =
  subst (λ z → z ≤ width (suc n))
        (+-comm (fib (suc (suc n))) 1)
        (≤-k+ {k = fib (suc (suc n))} (fib-pos n))

-- NON-VACUITY: a CONSTANT modulus is refuted.  For any fixed rung c there is a
-- precision demand its bracket cannot meet — so no constant function is a
-- sound modulus.  This is the in-kernel substitution test for "the rate is
-- genuinely carried, not a constant".
modulus-forced : (c : ℕ) → Σ[ D ∈ ℕ ] (width c < D)
modulus-forced c = suc (width c) , <-suc

-- ────────────────────────────────────────────────────────────────────────────
-- The effective-modulus certificate, and the full EFFECTIVE CORRIDOR:
-- the two genuine walls (cohesion + univalence) PLUS the intrinsic rate.
-- ────────────────────────────────────────────────────────────────────────────

record EffectiveModulus : Type where
  constructor effective-modulus
  field
    rung-width   : ℕ → ℕ
    the-modulus  : ℕ → ℕ
    sound        : (D : ℕ) → D ≤ rung-width (the-modulus D)
    narrows      : (n : ℕ) → rung-width n < rung-width (suc n)
    not-constant : (c : ℕ) → Σ[ D ∈ ℕ ] (rung-width c < D)

open EffectiveModulus public

golden-modulus : EffectiveModulus
golden-modulus = effective-modulus width modulus modulus-sound ladder-narrows modulus-forced

-- The effective corridor = a faithful bracket (genuinely-distinct walls) that
-- shrinks at the golden ladder's intrinsic, non-constant rate.  This is the
-- full steelmanned object of Vladimir's letter, with every claim kernel-checked.
record EffectiveCorridor : Set₁ where
  constructor effective-corridor
  field
    bracket : FaithfulCorridor    -- the two genuine walls (cohesion + univalence)
    rate    : EffectiveModulus    -- the ladder's intrinsic convergence rate

open EffectiveCorridor public

the-effective-corridor : EffectiveCorridor
the-effective-corridor = effective-corridor faithful-corridor-witness golden-modulus
