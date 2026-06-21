{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 3 of the germ->organism programme (D2a): finite-dimensional matrix
-- *-algebras over ℤ[φ].  This upgrades the corridor's AF "skeleton" (finite SETS
-- with inclusions) to a tower of genuine finite-dimensional ALGEBRAS with
-- *-homomorphism inclusions -- the algebra content the disclaimer flagged as
-- missing.  --cubical --safe --guardedness, no postulates.
--
-- Z[φ] is packaged as a CommRing from Theory/GoldenRing's proven axioms; the
-- cubical matrix-ring machinery then supplies M_n(ℤ[φ]) with associative
-- multiplication and unit for free.  The *-involution is conjugate-transpose
-- with the Galois conjugation φ↦ψ=1−φ as scalar conjugation.

module corpus.cubical_agda.RealCohesion.GoldenMatrixAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; isSetℤ)
open import Cubical.Algebra.CommRing.Base using (CommRing; makeCommRing)
open import Cubical.Algebra.Matrix.CommRingCoefficient

open import corpus.cubical_agda.Theory.GoldenRing

-- ℤ[φ] is a set (it is ℤ × ℤ up to the record eta).
isSetGφ : isSet Gφ
isSetGφ = isSetRetract (λ x → a x , b x) (λ p → gφ (fst p) (snd p))
                       (λ _ → refl) (isSet× isSetℤ isSetℤ)

-- Package ℤ[φ] as a CommRing from GoldenRing's proven axioms.
GφCommRing : CommRing ℓ-zero
GφCommRing = makeCommRing 0G 1G _+G_ _·G_ negG isSetGφ
  (λ x y z → sym (+G-assoc x y z)) +G-idR +G-invR +G-comm
  (λ x y z → sym (·G-assoc x y z)) ·G-idR ·G-distR ·G-comm

-- The matrix ring M_m,n(ℤ[φ]): Mat, 𝟙, _⋆_ (associative mult), transpose ᵗ.
open Coefficient GφCommRing public

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)

private variable m n k : ℕ

-- ── the *-involution: conjugate-transpose with the Galois conjugation ──────
_★ : Mat m n → Mat n m
(M ★) i j = conj (M j i)

infix 9 _★

★-involutive : (M : Mat m n) → (M ★) ★ ≡ M
★-involutive M = funExt λ i → funExt λ j → conj-involutive (M i j)

open import Cubical.Data.Int using (pos; injPos)
open import Cubical.Data.Nat using (znots)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Relation.Nullary using (¬_)

0G≢1G : ¬ (0G ≡ 1G)
0G≢1G p = znots (injPos (cong a p))

-- ── Bratteli corner inclusion  M_n(ℤ[φ]) ↪ M_{n+1}(ℤ[φ]) ─────────────────
ιB : Mat n n → Mat (suc n) (suc n)
ιB M zero    zero    = 0G
ιB M zero    (suc j) = 0G
ιB M (suc i) zero    = 0G
ιB M (suc i) (suc j) = M i j

-- it is injective (recovers M from the (suc,suc) block)
ιB-injective : (M N : Mat n n) → ιB M ≡ ιB N → M ≡ N
ιB-injective M N p = funExt λ i → funExt λ j → cong (λ f → f (suc i) (suc j)) p

-- it is NOT surjective: the top-left corner unit E₀₀ is unreachable.
-- (n explicit: it is only in the result type, so the Fin match needs it as data.)
E00 : (n : ℕ) → Mat (suc n) (suc n)
E00 n zero    zero    = 1G
E00 n zero    (suc j) = 0G
E00 n (suc i) zero    = 0G
E00 n (suc i) (suc j) = 0G

ιB-nonsurjective : (n : ℕ) (M : Mat n n) → ¬ (ιB M ≡ E00 n)
ιB-nonsurjective n M p = 0G≢1G (cong (λ f → f zero zero) p)

-- it is a *-homomorphism for the involution (corner and conj-transpose commute)
ιB-preserves-★ : (n : ℕ) (M : Mat n n) → ιB (M ★) ≡ (ιB M) ★
ιB-preserves-★ n M = funExt λ i → funExt λ j → g i j
  where
    g : (i j : Fin (suc n)) → ιB (M ★) i j ≡ ((ιB M) ★) i j
    g zero    zero    = refl
    g zero    (suc j) = refl
    g (suc i) zero    = refl
    g (suc i) (suc j) = refl

-- ── multiplicative-law helpers (for ιB being an ALGEBRA homomorphism) ─────
+G-idL : (x : Gφ) → 0G +G x ≡ x
+G-idL x = +G-comm 0G x ∙ +G-idR x

0·0 : 0G ·G 0G ≡ 0G
0·0 = refl

ιB-zero-row : (M : Mat n n) (k : Fin (suc n)) → ιB M zero k ≡ 0G
ιB-zero-row M zero    = refl
ιB-zero-row M (suc k) = refl

ιB-zero-col : (M : Mat n n) (k : Fin (suc n)) → ιB M k zero ≡ 0G
ιB-zero-col M zero    = refl
ιB-zero-col M (suc k) = refl

open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open Sum (CommRing→Ring GφCommRing) using (∑Ext; ∑Mul0r; ∑Mulr0)

-- ιB preserves matrix multiplication: a genuine ALGEBRA homomorphism.
ιB-preserves-⋆ : (n : ℕ) (M N : Mat n n) → ιB M ⋆ ιB N ≡ ιB (M ⋆ N)
ιB-preserves-⋆ n M N = funExt λ a → funExt λ b → g a b
  where
    g : (a b : Fin (suc n)) → (ιB M ⋆ ιB N) a b ≡ ιB (M ⋆ N) a b
    g zero b =
      (∑Ext (λ k → cong (_·G ιB N k b) (ιB-zero-row M k)) ∙ ∑Mul0r (λ k → ιB N k b))
        ∙ sym (ιB-zero-row (M ⋆ N) b)
    g (suc i) zero =
      (∑Ext (λ k → cong (ιB M (suc i) k ·G_) (ιB-zero-col N k)) ∙ ∑Mulr0 (λ k → ιB M (suc i) k))
        ∙ sym (ιB-zero-col (M ⋆ N) (suc i))
    g (suc i) (suc j) = cong (_+G (M ⋆ N) i j) 0·0 ∙ +G-idL ((M ⋆ N) i j)

-- entrywise matrix addition (the AbGroup structure, stated self-containedly)
_+M_ : Mat m n → Mat m n → Mat m n
(M +M N) i j = M i j +G N i j

infixl 7 _+M_

-- ιB preserves addition: together with ⋆ and ★ this makes ιB a genuine
-- (unital-free) *-algebra homomorphism -- an AF Bratteli connecting map.
ιB-preserves-+ : (n : ℕ) (M N : Mat n n) → ιB (M +M N) ≡ ιB M +M ιB N
ιB-preserves-+ n M N = funExt λ a → funExt λ b → h a b
  where
    h : (a b : Fin (suc n)) → ιB (M +M N) a b ≡ (ιB M +M ιB N) a b
    h zero    zero    = sym (+G-idL 0G)
    h zero    (suc j) = sym (+G-idL 0G)
    h (suc i) zero    = sym (+G-idL 0G)
    h (suc i) (suc j) = refl

-- ── ★ is a *-anti-automorphism: (M⋆N)★ = N★⋆M★ ───────────────────────────
open import Cubical.Algebra.Ring using (RingHom; IsRingHom; makeIsRingHom)
open import Cubical.Algebra.Ring.BigOps using (module SumMap)

private 𝑹G = CommRing→Ring GφCommRing

-- the Galois conjugation is a ring homomorphism (pres1 is refl; pres0/pres- derived).
conjHom : RingHom 𝑹G 𝑹G
conjHom = conj , makeIsRingHom refl conj-+ conj-·

open Sum (CommRing→Ring GφCommRing) using (∑)
open SumMap 𝑹G 𝑹G conjHom using (∑Map)

★-antihom : (n : ℕ) (M N : Mat n n) → (M ⋆ N) ★ ≡ N ★ ⋆ M ★
★-antihom n M N = funExt λ a → funExt λ b →
      ∑Map (λ k → M b k ·G N k a)
    ∙ ∑Ext (λ k → conj-· (M b k) (N k a))
    ∙ ∑Ext (λ k → ·G-comm (conj (M b k)) (conj (N k a)))
