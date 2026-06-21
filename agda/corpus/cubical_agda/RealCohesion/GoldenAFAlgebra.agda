{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 4 of the germ->organism programme (D2b): the AF inductive LIMIT.
-- This upgrades the corridor's GoldenAFColimit (a colimit of finite SETS) to the
-- colimit of the finite-dimensional *-ALGEBRAS M_n(ℤ[φ]) along the Bratteli
-- *-algebra homomorphism ιB -- a genuine approximately-finite *-algebra.  The
-- involution descends to the limit precisely because ιB preserves ★.

module corpus.cubical_agda.RealCohesion.GoldenAFAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sequence.Base using (Sequence; sequence)
open import Cubical.HITs.SequentialColimit.Base using (SeqColim; incl; push)

open import corpus.cubical_agda.RealCohesion.GoldenMatrixAlgebra

-- The golden AF tower: the matrix *-algebras M_n(ℤ[φ]) joined by Bratteli ιB.
goldenAFSeq : Sequence ℓ-zero
goldenAFSeq = sequence (λ n → Mat n n) (λ {n} → ιB {n})

-- The AF inductive limit: a colimit of finite-dimensional ALGEBRAS, not sets.
A∞ : Type
A∞ = SeqColim goldenAFSeq

-- The *-involution descends to the limit -- using ιB-preserves-★.
★∞ : A∞ → A∞
★∞ (incl {n = n} M)   = incl {n = n} (M ★)
★∞ (push {n = n} M i) = (push (M ★) ∙ cong incl (ιB-preserves-★ n M)) i

-- The AF tower is PROPER: every Bratteli inclusion is non-surjective (the corner
-- unit E₀₀ is unreachable), so the limit genuinely grows.  A degenerate "AF"
-- colimit whose connecting maps were surjective/equivalences would fail this.
open import Cubical.Relation.Nullary using (¬_)

golden-tower-proper : (n : ℕ) (M : Mat n n) → ¬ (ιB M ≡ E00 n)
golden-tower-proper = ιB-nonsurjective
