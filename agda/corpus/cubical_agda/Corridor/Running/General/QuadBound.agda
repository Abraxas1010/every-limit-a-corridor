{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GERSHGORIN / ℓ¹ QUADRATIC-FORM BOUND — ⟨x, A·x⟩ ≤ ‖A‖₁ · ⟨x,x⟩, any matrix, all n.
--
-- ‖A‖₁ = Σᵢⱼ |Aᵢⱼ| is the (computable, rational) ℓ¹ entry-sum.  This is the computable UPPER bracket
-- for the spectral radius in the "spectrum has a modulus" route: every Rayleigh quotient is ≤ ‖A‖₁,
-- so ‖A‖₁ ≥ ρ(A).  Proof: bound each term Aᵢⱼxᵢxⱼ ≤ |Aᵢⱼ|·⟨x,x⟩ (because |xᵢxⱼ| ≤ ⟨x,x⟩, proved
-- squared via sqrt-mono-≤ — no abs-multiplicativity, no ∑Exchange, no symmetry), then sum: distribute
-- xᵢ into the inner sum (∑Mulrdist), apply ∑-mono, factor ⟨x,x⟩ and the row-sums out (∑Mulldist).
--
module corpus.cubical_agda.Corridor.Running.General.QuadBound where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc; FinVec)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- ring identities for the per-term bound (before the ℚ open: `-_` clash).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  sqProdR : (u a v : ⟨ R ⟩) → ((u · (a · v)) · (u · (a · v))) ≡ ((a · a) · ((u · u) · (v · v)))
  sqProdR u a v = solve! R
  sqMulR : (a g : ⟨ R ⟩) → ((a · g) · (a · g)) ≡ ((a · a) · (g · g))
  sqMulR a g = solve! R

open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_≤_; _<_; isRefl≤; isTrans≤; isTrans<; <Weaken≤; <Dec; <-+o; ≤-·o)
open import Cubical.Relation.Nullary using (yes; no)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (absℚ; absℚ-sq; 0≤absℚ; 0≤sq-all)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫; gram-nonneg)
open import corpus.cubical_agda.Corridor.Running.General.QuadLemmas using (term-le-sum; sqrt-mono-≤)
open import corpus.cubical_agda.Corridor.Running.General.SumOrder using (∑-mono)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Sum (CommRing→Ring ℚCommRing) using (∑; ∑Mulrdist; ∑Mulldist)

private
  neg-pos : (c : ℚ) → c < 0 → 0 < (- c)
  neg-pos c c<0 = subst2 _<_ (+InvR c) (+IdL (- c)) (<-+o c 0 (- c) c<0)
  0≤·0≤ : (a b : ℚ) → 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
  0≤·0≤ a b 0≤a 0≤b = subst (_≤ (a · b)) (·AnnihilL b) (≤-·o 0 a b 0≤b 0≤a)
  le-prod : (p q G : ℚ) → 0 ≤ p → 0 ≤ G → p ≤ G → q ≤ G → (p · q) ≤ (G · G)
  le-prod p q G 0≤p 0≤G p≤G q≤G =
    isTrans≤ (p · q) (p · G) (G · G)
      (subst2 _≤_ (·Comm q p) (·Comm G p) (≤-·o q G p 0≤p q≤G))
      (≤-·o p G G 0≤G p≤G)

-- every rational is ≤ its absolute value.
val≤abs : (c : ℚ) → c ≤ absℚ c
val≤abs c with <Dec c 0
... | yes c<0 = <Weaken≤ c (- c) (isTrans< c 0 (- c) c<0 (neg-pos c c<0))
... | no  _   = isRefl≤ c

-- the per-term bound: u·(a·v) ≤ |a|·G  whenever u² ≤ G and v² ≤ G  (0 ≤ G).
perTermG : (a u v G : ℚ) → 0 ≤ G → (u · u) ≤ G → (v · v) ≤ G → (u · (a · v)) ≤ (absℚ a · G)
perTermG a u v G 0≤G uu≤G vv≤G =
  isTrans≤ (u · (a · v)) (absℚ (u · (a · v))) (absℚ a · G)
    (val≤abs (u · (a · v)))
    (sqrt-mono-≤ (absℚ (u · (a · v))) (absℚ a · G)
      (0≤absℚ (u · (a · v))) (0≤·0≤ (absℚ a) G (0≤absℚ a) 0≤G) sq≤)
  where
    lhs : (absℚ (u · (a · v)) · absℚ (u · (a · v))) ≡ ((a · a) · ((u · u) · (v · v)))
    lhs = absℚ-sq (u · (a · v)) ∙ sqProdR ℚCommRing u a v
    rhs : ((absℚ a · G) · (absℚ a · G)) ≡ ((a · a) · (G · G))
    rhs = sqMulR ℚCommRing (absℚ a) G ∙ cong (_· (G · G)) (absℚ-sq a)
    core : ((a · a) · ((u · u) · (v · v))) ≤ ((a · a) · (G · G))
    core = subst2 _≤_ (·Comm ((u · u) · (v · v)) (a · a)) (·Comm (G · G) (a · a))
             (≤-·o ((u · u) · (v · v)) (G · G) (a · a) (0≤sq-all a)
               (le-prod (u · u) (v · v) G (0≤sq-all u) 0≤G uu≤G vv≤G))
    sq≤ : (absℚ (u · (a · v)) · absℚ (u · (a · v))) ≤ ((absℚ a · G) · (absℚ a · G))
    sq≤ = subst2 _≤_ (sym lhs) (sym rhs) core

-- one row: xᵢ·(A·x)ᵢ ≤ (Σⱼ|Aᵢⱼ|)·⟨x,x⟩.
perRow : {n : ℕ} (A : Mat n n) (x : Mat n 1) (i : Fin n)
       → (x i zero · ((A ⋆ x) i zero)) ≤ ((∑ (λ j → absℚ (A i j))) · ⟪ x , x ⟫)
perRow {n} A x i =
  subst (_≤ ((∑ (λ j → absℚ (A i j))) · ⟪ x , x ⟫)) (sym distr)
    (subst ((∑ (λ j → x i zero · (A i j · x j zero))) ≤_) factor
      (∑-mono n (λ j → x i zero · (A i j · x j zero)) (λ j → absℚ (A i j) · ⟪ x , x ⟫)
        (λ j → perTermG (A i j) (x i zero) (x j zero) ⟪ x , x ⟫ (gram-nonneg x)
                 (term-le-sum n (λ k → x k zero · x k zero) i (λ k → 0≤sq-all (x k zero)))
                 (term-le-sum n (λ k → x k zero · x k zero) j (λ k → 0≤sq-all (x k zero))))))
  where
    distr : (x i zero · ((A ⋆ x) i zero)) ≡ ∑ (λ j → x i zero · (A i j · x j zero))
    distr = ∑Mulrdist (x i zero) (λ j → A i j · x j zero)
    factor : (∑ (λ j → absℚ (A i j) · ⟪ x , x ⟫)) ≡ ((∑ (λ j → absℚ (A i j))) · ⟪ x , x ⟫)
    factor = sym (∑Mulldist ⟪ x , x ⟫ (λ j → absℚ (A i j)))

-- the ℓ¹ entry-sum norm and the quadratic-form bound.
oneNorm : {n : ℕ} → Mat n n → ℚ
oneNorm {n} A = ∑ (λ i → ∑ (λ j → absℚ (A i j)))

quadBound : {n : ℕ} (A : Mat n n) (x : Mat n 1) → ⟪ x , A ⋆ x ⟫ ≤ (oneNorm A · ⟪ x , x ⟫)
quadBound {n} A x =
  subst (⟪ x , A ⋆ x ⟫ ≤_) factorOut
    (∑-mono n (λ i → x i zero · ((A ⋆ x) i zero))
              (λ i → (∑ (λ j → absℚ (A i j))) · ⟪ x , x ⟫)
              (λ i → perRow A x i))
  where
    factorOut : (∑ (λ i → (∑ (λ j → absℚ (A i j))) · ⟪ x , x ⟫)) ≡ (oneNorm A · ⟪ x , x ⟫)
    factorOut = sym (∑Mulldist ⟪ x , x ⟫ (λ i → ∑ (λ j → absℚ (A i j))))
