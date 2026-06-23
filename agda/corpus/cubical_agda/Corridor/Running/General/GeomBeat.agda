{-# OPTIONS --cubical --safe --guardedness #-}
--
-- GEOMETRIC BEAT — for 0 < q < r and any C, eventually  C·q^{2^L} < r^{2^L}.
--
-- The ratio form of the growth, used directly in LOCATEDNESS (with C = n²): if the lower cut fails at
-- a level where r^{2^L} > n²·q^{2^L}, the upper cut must hold.  Reduces to qgrow at t = r·q⁻¹ > 1
-- (ℚ is a field: hasInverseℚ), using qpow-multiplicativity qpow L (a·b) = qpow L a · qpow L b and
-- r = t·q.  No analysis beyond the landed qgrow.
--
module corpus.cubical_agda.Corridor.Running.General.GeomBeat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)

module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  sqMulRegroupR : (a b : ⟨ R ⟩) → ((a · b) · (a · b)) ≡ ((a · a) · (b · b))
  sqMulRegroupR a b = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isIrrefl<; isTrans<; <-·o; _≟_; Trichotomy; lt; eq; gt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁) renaming (map to ∥map∥)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Algebra.Field.Instances.Rationals using (hasInverseℚ)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (0<1ℚ)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (qpow)
open import corpus.cubical_agda.Corridor.Running.General.GeomGrowArch using (qgrow)

-- qpow distributes over products, and is positive on positives.
qpow-mult : (L : ℕ) (a b : ℚ) → qpow L (a · b) ≡ (qpow L a · qpow L b)
qpow-mult zero    a b = refl
qpow-mult (suc L) a b =
  cong (λ z → z · z) (qpow-mult L a b) ∙ sqMulRegroupR ℚCommRing (qpow L a) (qpow L b)

0<qpow : (L : ℕ) (q : ℚ) → 0 < q → 0 < qpow L q
0<qpow zero    q 0<q = 0<q
0<qpow (suc L) q 0<q = subst (_< (qpow L q · qpow L q)) (·AnnihilL (qpow L q))
                         (<-·o 0 (qpow L q) (qpow L q) (0<qpow L q 0<q) (0<qpow L q 0<q))

private
  q≢0 : (q : ℚ) → 0 < q → ¬ (q ≡ 0)
  q≢0 q 0<q q≡0 = isIrrefl< 0 (subst (0 <_) q≡0 0<q)
  -- inv of a positive is positive (from q·inv = 1 > 0).
  0<inv : (q inv : ℚ) → 0 < q → (q · inv) ≡ 1 → 0 < inv
  0<inv q inv 0<q q·inv≡1 with inv ≟ 0
  ... | gt 0<i = 0<i
  ... | eq i≡0 = ⊥-rec (isIrrefl< 0
        (subst (0 <_) (sym q·inv≡1 ∙ cong (q ·_) i≡0 ∙ ·AnnihilR q) 0<1ℚ))
  ... | lt i<0 = ⊥-rec (isIrrefl< 0 (isTrans< 0 (q · inv) 0
        (subst (0 <_) (sym q·inv≡1) 0<1ℚ)
        (subst2 _<_ (·Comm inv q) (·AnnihilL q) (<-·o inv 0 q 0<q i<0))))

-- THE BEAT:  0 < q < r  ⟹  ∃L,  C·q^{2^L} < r^{2^L}.
geom-beat : (q r : ℚ) → 0 < q → q < r → (C : ℚ) → ∥ Σ[ L ∈ ℕ ] ((C · qpow L q) < qpow L r) ∥₁
geom-beat q r 0<q q<r C = ∥map∥ use (qgrow (r · inv) 1<t C)
  where
    inv : ℚ
    inv = fst (hasInverseℚ q (q≢0 q 0<q))
    q·inv≡1 : (q · inv) ≡ 1
    q·inv≡1 = snd (hasInverseℚ q (q≢0 q 0<q))
    0<i : 0 < inv
    0<i = 0<inv q inv 0<q q·inv≡1
    1<t : 1 < (r · inv)
    1<t = subst (_< (r · inv)) q·inv≡1 (<-·o q r inv 0<i q<r)
    r≡tq : r ≡ ((r · inv) · q)
    r≡tq = sym (sym (·Assoc r inv q) ∙ cong (r ·_) (·Comm inv q ∙ q·inv≡1) ∙ ·IdR r)
    use : Σ[ L ∈ ℕ ] (C < qpow L (r · inv)) → Σ[ L ∈ ℕ ] ((C · qpow L q) < qpow L r)
    use (L , C<t) = L ,
      subst ((C · qpow L q) <_)
        (sym (cong (qpow L) r≡tq ∙ qpow-mult L (r · inv) q))
        (<-·o C (qpow L (r · inv)) (qpow L q) (0<qpow L q 0<q) C<t)
