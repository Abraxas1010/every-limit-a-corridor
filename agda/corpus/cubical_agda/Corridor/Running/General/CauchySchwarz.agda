{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE CAUCHY–SCHWARZ INEQUALITY — ⟨u,v⟩² ≤ ⟨u,u⟩·⟨v,v⟩, every dimension.
--
-- The engine of the dyadic modulus: it gives the squaring-refinement step rayUp(A²)(s²) ⟹ rayUp A s
-- (for PSD A), via ⟨Ax,x⟩² = ⟨Ax,x⟩² ≤ ⟨Ax,Ax⟩⟨x,x⟩ = ⟨A²x,x⟩⟨x,x⟩.  Proved division-free and with
-- NO vector operations: the auxiliary sum
--      Q = Σᵢ (⟨v,v⟩·uᵢ − ⟨u,v⟩·vᵢ)²  ≥ 0   (a sum of squares),
-- expands (purely at the ∑ level, via ∑Split + ∑Mulrdist) to  ⟨v,v⟩·(⟨u,u⟩·⟨v,v⟩ − ⟨u,v⟩²),
-- so that product is ≥ 0; cancelling the nonnegative ⟨v,v⟩ (case split on 0 vs >0, with gram-def at 0)
-- gives Cauchy–Schwarz.
--
module corpus.cubical_agda.Corridor.Running.General.CauchySchwarz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin; FinVec; zero)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- per-term expansion and the final scalar simplification, over any commutative ring (before ℚ open).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  sqDiffR : (c d u v : ⟨ R ⟩)
    → (((c · u) - (d · v)) · ((c · u) - (d · v)))
      ≡ (((c · c) · (u · u)) + ((((- (c · d)) · (u · v)) + ((- (c · d)) · (u · v))) + ((d · d) · (v · v))))
  sqDiffR c d u v = solve! R
  csCollapseR : (cuu cuv cvv : ⟨ R ⟩)
    → (((cvv · cvv) · cuu) + (((( - (cvv · cuv)) · cuv) + ((- (cvv · cuv)) · cuv)) + ((cuv · cuv) · cvv)))
      ≡ (cvv · ((cuu · cvv) - (cuv · cuv)))
  csCollapseR cuu cuv cvv = solve! R

open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_≤_; _<_; isRefl≤; isTrans≤<; isIrrefl<; ≤Monotone+; ≮→≥; <-·o; _≟_; Trichotomy; lt; eq; gt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫; gram-nonneg; gram-def)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Sum (CommRing→Ring ℚCommRing) using (∑; ∑Ext; ∑Split; ∑Mulrdist; ∑Mulr0)

private
  0≤sub→≤ : (Z Y : ℚ) → 0 ≤ (Y - Z) → Z ≤ Y
  0≤sub→≤ Z Y 0≤Y-Z = subst2 _≤_ (+IdL Z)
                         (sym (+Assoc Y (- Z) Z) ∙ cong (Y +_) (+InvL Z) ∙ +IdR Y)
                         (≤Monotone+ 0 (Y - Z) Z Z 0≤Y-Z (isRefl≤ Z))
  cancelPos : (a X : ℚ) → 0 < a → 0 ≤ (a · X) → 0 ≤ X
  cancelPos a X 0<a 0≤aX = ≮→≥ X 0 ¬X<0
    where ¬X<0 : X < 0 → ⊥
          ¬X<0 X<0 = isIrrefl< 0 (isTrans≤< 0 (a · X) 0 0≤aX
                       (subst2 _<_ (·Comm X a) (·AnnihilL a) (<-·o X 0 a 0<a X<0)))

private
  -- ⟨u,u⟩, ⟨u,v⟩, ⟨v,v⟩ are the corresponding ∑'s (definitional from GramPosDef's inner product).
  -- the auxiliary sum Q = Σᵢ (c·uᵢ − d·vᵢ)²  with  c = ⟨v,v⟩,  d = ⟨u,v⟩.
  Qsum : {n : ℕ} (u v : Mat n 1) → ℚ
  Qsum {n} u v = ∑ (λ i → ((⟪ v , v ⟫ · u i zero) - (⟪ u , v ⟫ · v i zero))
                        · ((⟪ v , v ⟫ · u i zero) - (⟪ u , v ⟫ · v i zero)))

  0≤Q : {n : ℕ} (u v : Mat n 1) → 0 ≤ Qsum u v
  0≤Q {n} u v = gram-nonneg (λ i _ → (⟪ v , v ⟫ · u i zero) - (⟪ u , v ⟫ · v i zero))

  -- Q expands to ⟨v,v⟩·(⟨u,u⟩·⟨v,v⟩ − ⟨u,v⟩²), purely by ∑Split + ∑Mulrdist.
  Q≡ : {n : ℕ} (u v : Mat n 1)
     → Qsum u v ≡ (⟪ v , v ⟫ · ((⟪ u , u ⟫ · ⟪ v , v ⟫) - (⟪ u , v ⟫ · ⟪ u , v ⟫)))
  Q≡ {n} u v =
      ∑Ext (λ i → sqDiffR ℚCommRing (⟪ v , v ⟫) (⟪ u , v ⟫) (u i zero) (v i zero))
    ∙ ∑Split fA (λ i → (fB i + fB i) + fC i)
    ∙ cong (∑ fA +_) (∑Split (λ i → fB i + fB i) fC)
    ∙ cong (λ z → ∑ fA + (z + ∑ fC)) (∑Split fB fB)
    ∙ (λ t → split-fA t + ((split-fB t + split-fB t) + split-fC t))
    ∙ csCollapseR ℚCommRing (⟪ u , u ⟫) (⟪ u , v ⟫) (⟪ v , v ⟫)
    where
      c = ⟪ v , v ⟫ ; d = ⟪ u , v ⟫
      fA = λ (i : Fin n) → (c · c) · (u i zero · u i zero)
      fB = λ (i : Fin n) → (- (c · d)) · (u i zero · v i zero)
      fC = λ (i : Fin n) → (d · d) · (v i zero · v i zero)
      -- each ∑(scalar · termᵢ) ≡ scalar · ⟨·,·⟩  (∑Mulrdist; ⟨·,·⟩ is the corresponding ∑ definitionally).
      split-fA : ∑ fA ≡ (c · c) · ⟪ u , u ⟫
      split-fA = sym (∑Mulrdist (c · c) (λ i → u i zero · u i zero))
      split-fB : ∑ fB ≡ (- (c · d)) · ⟪ u , v ⟫
      split-fB = sym (∑Mulrdist (- (c · d)) (λ i → u i zero · v i zero))
      split-fC : ∑ fC ≡ (d · d) · ⟪ v , v ⟫
      split-fC = sym (∑Mulrdist (d · d) (λ i → v i zero · v i zero))

-- 0 ≤ ⟨v,v⟩·(⟨u,u⟩·⟨v,v⟩ − ⟨u,v⟩²).
cs-form : {n : ℕ} (u v : Mat n 1)
        → 0 ≤ (⟪ v , v ⟫ · ((⟪ u , u ⟫ · ⟪ v , v ⟫) - (⟪ u , v ⟫ · ⟪ u , v ⟫)))
cs-form u v = subst (0 ≤_) (Q≡ u v) (0≤Q u v)

-- CAUCHY–SCHWARZ:  ⟨u,v⟩² ≤ ⟨u,u⟩·⟨v,v⟩.
cauchy-schwarz : {n : ℕ} (u v : Mat n 1) → (⟪ u , v ⟫ · ⟪ u , v ⟫) ≤ (⟪ u , u ⟫ · ⟪ v , v ⟫)
cauchy-schwarz {n} u v with ⟪ v , v ⟫ ≟ 0
... | eq vv≡0 = subst2 _≤_ (sym uv²≡0) (sym uu·0) (isRefl≤ 0)
  where
    -- v = 0, so ⟨u,v⟩ = 0 and ⟨u,u⟩·⟨v,v⟩ = 0; both sides are 0.
    ⟪u,0⟫≡0 : ⟪ u , (λ _ _ → 0) ⟫ ≡ 0
    ⟪u,0⟫≡0 = ∑Mulr0 (λ i → u i zero)
    uv²≡0 : (⟪ u , v ⟫ · ⟪ u , v ⟫) ≡ 0
    uv²≡0 = cong (λ w → ⟪ u , w ⟫ · ⟪ u , w ⟫) (gram-def v vv≡0)
          ∙ cong (λ z → z · z) ⟪u,0⟫≡0 ∙ ·AnnihilL 0
    uu·0 : (⟪ u , u ⟫ · ⟪ v , v ⟫) ≡ 0
    uu·0 = cong (⟪ u , u ⟫ ·_) vv≡0 ∙ ·AnnihilR ⟪ u , u ⟫
... | lt vv<0 = ⊥-rec (isIrrefl< 0 (isTrans≤< 0 ⟪ v , v ⟫ 0 (gram-nonneg v) vv<0))
... | gt 0<vv = 0≤sub→≤ (⟪ u , v ⟫ · ⟪ u , v ⟫) (⟪ u , u ⟫ · ⟪ v , v ⟫) 0≤bracket
  where
    0≤bracket : 0 ≤ ((⟪ u , u ⟫ · ⟪ v , v ⟫) - (⟪ u , v ⟫ · ⟪ u , v ⟫))
    0≤bracket = cancelPos ⟪ v , v ⟫ ((⟪ u , u ⟫ · ⟪ v , v ⟫) - (⟪ u , v ⟫ · ⟪ u , v ⟫)) 0<vv (cs-form u v)
