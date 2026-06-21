{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 2 of the germ->organism programme: the genuine shape modality and
-- Disclaimer 3 (shape != flat on the ANALYTIC real line, not a 2-point model).
--
-- shape ∫ := nullification at ℝ (Shulman's real-cohesive shape, a genuine
-- Modality, CONSTRUCTED not postulated). flat ♭ := the set-level identity
-- reflection (no crisp modality; stated honestly). The separation is then:
--   ∫ℝ is contractible (ℝ is the localizing generator), while ♭ℝ = ℝ keeps the
--   apart reals 0 and 1 distinct -- so the two modalities differ on the line.

module corpus.cubical_agda.RealCohesion.ShapeNullification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)
open import Cubical.HITs.Nullification

open import Cubical.Data.Rationals using (ℚ)
open import corpus.cubical_agda.RealCohesion.DedekindReal

-- The localizing family: nullify at the real line itself.
SR : Unit → Type₁
SR _ = ℝ

-- shape = nullification at ℝ (the real-cohesive ∫); a genuine modality.
∫ : Type₁ → Type₁
∫ X = Null SR X

-- flat on a set = the set itself (honest set-level reflection; no crisp).
♭ : Type₁ → Type₁
♭ X = X

-- ── D3 crux: the shape of the analytic real line is contractible ──────────
-- ℝ is the generator of the nullification, so ∫ℝ collapses to a point.
shape-ℝ-isContr : isContr (∫ ℝ)
shape-ℝ-isContr = generatorsConnected SR tt

-- ── the flat side: ♭ℝ = ℝ keeps 0 and 1 apart ────────────────────────────
open import Cubical.Relation.Nullary using (¬_)

-- disjointness projection from a real's cut data (7th of the 8 cut laws).
disjOf : (x : ℝ) (q : ℚ) → ⟦ lowerCut x ⟧ q → ⟦ upperCut x ⟧ q → ⊥
disjOf x = x .snd .snd .snd .snd .snd .snd .snd .snd .fst

<ℝ-irrefl : (x : ℝ) → ¬ (x <ℝ x)
<ℝ-irrefl x = PT.rec (λ p q i → ⊥.isProp⊥ p q i) λ { (q , xUq , xLq) → disjOf x q xLq xUq }

0ℝ≢1ℝ : ¬ (0ℝ ≡ 1ℝ)
0ℝ≢1ℝ p = <ℝ-irrefl 1ℝ (subst (_<ℝ 1ℝ) p 0<ℝ1)

flat-ℝ-not-isContr : ¬ isContr (♭ ℝ)
flat-ℝ-not-isContr (c , h) = 0ℝ≢1ℝ (sym (h 0ℝ) ∙ h 1ℝ)

-- ── D3: shape and flat are different functors on the analytic line ────────
shape≠flat-on-ℝ : ¬ (∫ ℝ ≃ ♭ ℝ)
shape≠flat-on-ℝ e = flat-ℝ-not-isContr (isOfHLevelRespectEquiv 0 e shape-ℝ-isContr)

-- the operational heart: shape MERGES the two reals that flat keeps APART.
shape-merges-0-1 : Path (∫ ℝ) ∣ 0ℝ ∣ ∣ 1ℝ ∣
shape-merges-0-1 = isContr→isProp shape-ℝ-isContr ∣ 0ℝ ∣ ∣ 1ℝ ∣
