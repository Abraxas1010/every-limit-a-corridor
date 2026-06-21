{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5 / real arithmetic: the rational embedding ι : ℚ → ℝ is a genuine
-- ORDER-EMBEDDING (q < r in ℚ iff ι q < ι r in ℝ), and it commutes with
-- negation.  So ℝ contains ℚ order- and sign-faithfully -- the rational spectral
-- values (e.g. integer eigenvalues over ℤ[φ]) embed correctly.  No postulates.

module corpus.cubical_agda.RealCohesion.RealEmbedding where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)

open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Rationals.Order using (_<_; isProp<; isTrans<)
open import corpus.cubical_agda.RealCohesion.DedekindReal

-- ι preserves the strict order:  q < r  ⟹  ι q <ℝ ι r.
-- (the separating rational is any point strictly between q and r -- dense.)
ι-monotone : (q r : ℚ) → q < r → ι q <ℝ ι r
ι-monotone q r q<r = ∣ dense q r q<r ∣₁

-- ι reflects the strict order:  ι q <ℝ ι r  ⟹  q < r.
ι-reflects : (q r : ℚ) → ι q <ℝ ι r → q < r
ι-reflects q r = PT.rec (isProp< q r) λ { (s , q<s , s<r) → isTrans< q s r q<s s<r }

-- ι commutes with negation: -ℝ (ι q) ≡ ι (- q) (sign-faithfulness).
open import Cubical.Data.Rationals using (-_; -Invol)
open import Cubical.Functions.Logic using (⇔toPath)
open import corpus.cubical_agda.RealCohesion.RealNegation using (-ℝ_; neg-flip)

-ℝ-ι : (q : ℚ) → -ℝ (ι q) ≡ ι (- q)
-ℝ-ι q = ΣPathP (pL , ΣPathP (pU ,
                   isProp→PathP (λ i → isPropIsCut (pL i) (pU i)) _ _))
  where
    pL : lowerCut (-ℝ (ι q)) ≡ lowerCut (ι (- q))
    pL = funExt λ p → ⇔toPath
           (λ h → subst (_< (- q)) (-Invol p) (neg-flip q (- p) h))
           (λ h → subst (_< (- p)) (-Invol q) (neg-flip p (- q) h))
    pU : upperCut (-ℝ (ι q)) ≡ upperCut (ι (- q))
    pU = funExt λ p → ⇔toPath
           (λ h → subst ((- q) <_) (-Invol p) (neg-flip (- p) q h))
           (λ h → subst ((- p) <_) (-Invol q) (neg-flip (- q) p h))
