{-# OPTIONS --cubical --safe --guardedness #-}

-- φ is irrational, integer-ratio level: no a:ℤ, B:ℤ>0 satisfy a² = aB + B²
-- (i.e. a/B = φ is impossible).  Reduces to the ℕ infinite descent golden-no-pos
-- by sign-casing a and using the symmetry a ↦ B−a (which maps the ψ-root case,
-- a<0, to the φ-root case, a>0).  No postulates.

module corpus.cubical_agda.RealCohesion.GoldenIrrationalZ where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc) renaming (_·_ to _·ℕ_; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Order using (zero-≤; suc-≤-suc)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)
open import corpus.cubical_agda.RealCohesion.GoldenIrrational using (golden-eq; golden-no-pos)

golden-eqℤ : ℤ → ℤ → Type
golden-eqℤ a B = a · a ≡ a · B + B · B

-- X + (−Y) ≡ 0  ⟹  X ≡ Y   (ℤ).
diff0→eqℤ : (X Y : ℤ) → X + (- Y) ≡ pos 0 → X ≡ Y
diff0→eqℤ X Y p = step1 ∙ cong (_+ Y) p ∙ step2
  where step1 : X ≡ (X + (- Y)) + Y
        step1 = solve! ℤCommRing
        step2 : (pos 0) + Y ≡ Y
        step2 = solve! ℤCommRing

-- the symmetry a ↦ B−a preserves the golden relation.
golden-sym : (a B : ℤ) → golden-eqℤ a B → golden-eqℤ (B + (- a)) B
golden-sym a B h = diff0→eqℤ _ _ (defect ∙ h→0)
  where
    h→0 : (a · a) + (- (a · B + B · B)) ≡ pos 0
    h→0 = cong (_+ (- (a · B + B · B))) h ∙ inv
      where inv : (a · B + B · B) + (- (a · B + B · B)) ≡ pos 0
            inv = solve! ℤCommRing
    defect : ((B + (- a)) · (B + (- a))) + (- ((B + (- a)) · B + B · B))
           ≡ (a · a) + (- (a · B + B · B))
    defect = solve! ℤCommRing

-- a positive ℤ solution gives a positive ℕ solution.
from-pos : (A bn : ℕ) → golden-eqℤ (pos A) (pos (suc bn))
         → A ·ℕ A ≡ A ·ℕ suc bn +ℕ suc bn ·ℕ suc bn
from-pos A bn h = injPos (pos·pos A A ∙ h ∙ cong₂ _+_ (sym (pos·pos A (suc bn)))
                                                       (sym (pos·pos (suc bn) (suc bn)))
                          ∙ sym (pos+ (A ·ℕ suc bn) (suc bn ·ℕ suc bn)))

-- the φ-root case: a = pos (suc A).
no-pos-suc : (A bn : ℕ) → golden-eqℤ (pos (suc A)) (pos (suc bn)) → ⊥
no-pos-suc A bn h =
  golden-no-pos (suc A) (suc bn) (suc-≤-suc zero-≤) (suc-≤-suc zero-≤) (from-pos (suc A) bn h)

-- the a=0 case reduces to pos 0 ≡ B·B  (B a variable, so solve! sees a clean atom).
golden-eqℤ-0 : (B : ℤ) → golden-eqℤ (pos 0) B → pos 0 ≡ B · B
golden-eqℤ-0 B h = pre ∙ h ∙ post
  where pre  : pos 0 ≡ pos 0 · pos 0
        pre  = solve! ℤCommRing
        post : pos 0 · B + B · B ≡ B · B
        post = solve! ℤCommRing

-- NO integer ratio equals φ:  ¬ (a² = aB + B²) for B = pos (suc bn) > 0.
golden-no-ℤ : (a : ℤ) (bn : ℕ) → ¬ golden-eqℤ a (pos (suc bn))
golden-no-ℤ (pos zero) bn h =
  ℕ.znots (injPos (golden-eqℤ-0 (pos (suc bn)) h ∙ sym (pos·pos (suc bn) (suc bn))))
golden-no-ℤ (pos (suc A)) bn h = no-pos-suc A bn h
golden-no-ℤ (negsuc k) bn h =
  no-pos-suc (bn +ℕ suc k) bn (subst (λ z → golden-eqℤ z (pos (suc bn))) aeq sym-h)
  where
    sym-h : golden-eqℤ (pos (suc bn) + (- negsuc k)) (pos (suc bn))
    sym-h = golden-sym (negsuc k) (pos (suc bn)) h
    aeq : pos (suc bn) + (- negsuc k) ≡ pos (suc (bn +ℕ suc k))
    aeq = sym (pos+ (suc bn) (suc k))
