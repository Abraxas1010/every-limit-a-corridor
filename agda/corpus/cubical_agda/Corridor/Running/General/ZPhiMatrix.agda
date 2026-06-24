{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE Z[φ] MATRIX ALGEBRA — golden-integer matrices as rational pairs, proven faithful (n×n foundation).
--
-- A matrix over Z[φ] is A+Bφ for rational matrices A,B.  Because φ²=φ+1, the product stays in the same
-- pair form:  (A+Bφ)(C+Dφ) = (AC+BD) + (AD+BC+BD)φ.  So Z[φ]-matrix arithmetic — in particular the
-- REPEATED SQUARING the spectral radius runs on — never leaves the pair (A,B) of ORDINARY rational
-- matrices, and reuses the existing matrix machinery (⋆, ∑) with no new coefficient ring.
--
-- The theorem `faithful` proves this is correct: for any commutative ring element t with t²=t+1 (i.e. any
-- realisation of the golden ratio — φ⁺=(1+√5)/2 or φ⁻=(1−√5)/2 in ℝ), evaluating the pair product equals
-- the product of the evaluations.  This is the rigorous foundation of the general n×n Z[φ] operator norm:
-- ‖M‖ = √ρ(MᵀM), MᵀM = P+Qφ, and the running squaring (P,Q)↦(P²+Q², PQ+QP+Q²) is exactly `zφMul` squared.
--
module corpus.cubical_agda.Corridor.Running.General.ZPhiMatrix where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Algebra.Matrix.CommRingCoefficient using (module Coefficient)
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Tactics.CommRingSolver using (solve!)

module _ {ℓ} (R : CommRing ℓ) where
  open Coefficient R using (Mat; _⋆_)
  open Sum (CommRing→Ring R) using (∑; ∑Ext)
  open CommRingStr (snd R)

  -- a Z[φ] matrix:  the pair (A,B) standing for A + Bφ.
  ZφMat : ℕ → Type ℓ
  ZφMat n = Mat n n × Mat n n

  -- pointwise sum of matrices.
  _⊕_ : {n : ℕ} → Mat n n → Mat n n → Mat n n
  (M ⊕ N) i j = M i j + N i j

  -- Z[φ] product via φ²=φ+1:  (A+Bφ)(C+Dφ) = (AC+BD) + (AD+BC+BD)φ.
  zφMul : {n : ℕ} → ZφMat n → ZφMat n → ZφMat n
  zφMul (A , B) (C , D) = ((A ⋆ C) ⊕ (B ⋆ D)) , (((A ⋆ D) ⊕ (B ⋆ C)) ⊕ (B ⋆ D))

  -- repeated squaring stays in the pair form — what the spectral radius runs on.
  zφSq : {n : ℕ} → ZφMat n → ZφMat n
  zφSq s = zφMul s s

  -- evaluation at a golden element t (t²=t+1):  (A,B) ↦ A + t·B, entrywise.
  evalE : {n : ℕ} (t : ⟨ R ⟩) → ZφMat n → Mat n n
  evalE t (A , B) i j = A i j + (t · B i j)


  module _ (t : ⟨ R ⟩) (golden : (t · t) ≡ (t + 1r)) where

    -- the entrywise product expansion, using t²=t+1 once.
    prodExpand : (a b c d : ⟨ R ⟩)
      → ((a + (t · b)) · (c + (t · d)))
      ≡ ((a · c) + ((t · (a · d)) + ((t · (b · c)) + ((t · (b · d)) + (b · d)))))
    prodExpand a b c d =
        step1 a b c d
      ∙ cong (λ z → (a · c) + ((t · (a · d)) + ((t · (b · c)) + (z · (b · d))))) golden
      ∙ step2 a b c d
      where
        step1 : (a b c d : ⟨ R ⟩)
          → ((a + (t · b)) · (c + (t · d)))
          ≡ ((a · c) + ((t · (a · d)) + ((t · (b · c)) + ((t · t) · (b · d)))))
        step1 a b c d = solve! R
        step2 : (a b c d : ⟨ R ⟩)
          → ((a · c) + ((t · (a · d)) + ((t · (b · c)) + ((t + 1r) · (b · d)))))
          ≡ ((a · c) + ((t · (a · d)) + ((t · (b · c)) + ((t · (b · d)) + (b · d)))))
        step2 a b c d = solve! R

    -- ring rearrangements on ABSTRACT variables (solve! reflects cleanly only on variables, not on the
    -- foldrFin/Vec.lookup that the matrix entries ∑ reduce to — so the ∑'s enter only as instantiations).
    ringId5 : (a₁ a₂ a₃ a₄ a₅ x₁ x₂ x₃ x₄ x₅ : ⟨ R ⟩)
      → ((a₁ + ((t · a₂) + ((t · a₃) + ((t · a₄) + a₅))))
          + (x₁ + ((t · x₂) + ((t · x₃) + ((t · x₄) + x₅)))))
      ≡ ((a₁ + x₁) + ((t · (a₂ + x₂)) + ((t · (a₃ + x₃)) + ((t · (a₄ + x₄)) + (a₅ + x₅)))))
    ringId5 _ _ _ _ _ _ _ _ _ _ = solve! R
    ringIdMul : (u v w x : ⟨ R ⟩)
      → ((u + x) + (t · ((v + w) + x))) ≡ (u + ((t · v) + ((t · w) + ((t · x) + x))))
    ringIdMul _ _ _ _ = solve! R

    -- THE ∑-LIFT, by FinData induction.  ∑ of the five-term shape V₁+(t·V₂+(t·V₃+(t·V₄+V₅))) equals
    -- ∑V₁+(t·∑V₂+(t·∑V₃+(t·∑V₄+∑V₅))).  Doing it by induction (not a ∑Split/∑Mulrdist cong-chain) keeps
    -- the foldrFin reduction under control: the cons rule ∑{suc n}V ≡ V zero + ∑(V∘suc) is refl, so each
    -- step is just a ring rearrangement of the head plus the inductive tail.
    bigLemma : {n : ℕ} (V₁ V₂ V₃ V₄ V₅ : Fin n → ⟨ R ⟩)
      → ∑ (λ l → V₁ l + ((t · V₂ l) + ((t · V₃ l) + ((t · V₄ l) + V₅ l))))
      ≡ (∑ V₁ + ((t · ∑ V₂) + ((t · ∑ V₃) + ((t · ∑ V₄) + ∑ V₅))))
    bigLemma {nzero}  V₁ V₂ V₃ V₄ V₅ = solve! R
    bigLemma {nsuc n} V₁ V₂ V₃ V₄ V₅ =
        cong (s0 +_) (bigLemma (λ i → V₁ (suc i)) (λ i → V₂ (suc i))
                              (λ i → V₃ (suc i)) (λ i → V₄ (suc i)) (λ i → V₅ (suc i)))
      ∙ rearrange
      where
        s0 : ⟨ R ⟩
        s0 = V₁ zero + ((t · V₂ zero) + ((t · V₃ zero) + ((t · V₄ zero) + V₅ zero)))
        w₁ = ∑ (λ i → V₁ (suc i)) ; w₂ = ∑ (λ i → V₂ (suc i)) ; w₃ = ∑ (λ i → V₃ (suc i))
        w₄ = ∑ (λ i → V₄ (suc i)) ; w₅ = ∑ (λ i → V₅ (suc i))
        rearrange :
            (s0 + (w₁ + ((t · w₂) + ((t · w₃) + ((t · w₄) + w₅)))))
          ≡ ((V₁ zero + w₁) + ((t · (V₂ zero + w₂)) + ((t · (V₃ zero + w₃))
              + ((t · (V₄ zero + w₄)) + (V₅ zero + w₅)))))
        rearrange = ringId5 (V₁ zero) (V₂ zero) (V₃ zero) (V₄ zero) (V₅ zero) w₁ w₂ w₃ w₄ w₅

    -- the faithfulness theorem, entrywise:  evalE (zφMul s s') i j ≡ (evalE s ⋆ evalE s') i j.
    faithfulE : {n : ℕ} (s s' : ZφMat n) (i j : Fin n)
      → evalE t (zφMul s s') i j ≡ (evalE t s ⋆ evalE t s') i j
    faithfulE {n} (A , B) (C , D) i j = lhsRing ∙ sym bigChain
      where
        ac ad bc bd : Fin n → ⟨ R ⟩
        ac = λ l → A i l · C l j
        ad = λ l → A i l · D l j
        bc = λ l → B i l · C l j
        bd = λ l → B i l · D l j
        AC AD BC BD : ⟨ R ⟩
        AC = (A ⋆ C) i j ; AD = (A ⋆ D) i j ; BC = (B ⋆ C) i j ; BD = (B ⋆ D) i j
        target : ⟨ R ⟩
        target = AC + ((t · AD) + ((t · BC) + ((t · BD) + BD)))
        -- (eval ⋆ eval) i j = ∑(entrywise product) ≡ ∑(expanded) ≡ target, by ∑Ext + the induction.
        bigChain : (evalE t (A , B) ⋆ evalE t (C , D)) i j ≡ target
        bigChain =
            ∑Ext (λ l → prodExpand (A i l) (B i l) (C l j) (D l j))
          ∙ bigLemma ac ad bc bd bd
        -- evalE (zφMul …) i j = (AC+BD) + t·((AD+BC)+BD) ≡ target  (pure ring; entries are atoms).
        lhsRing : evalE t (zφMul (A , B) (C , D)) i j ≡ target
        lhsRing = ringIdMul AC AD BC BD

    -- THE FAITHFULNESS THEOREM:  the pair arithmetic IS Z[φ] multiplication, for any t with t²=t+1.
    faithful : {n : ℕ} (s s' : ZφMat n) → evalE t (zφMul s s') ≡ (evalE t s ⋆ evalE t s')
    faithful s s' = funExt (λ i → funExt (λ j → faithfulE s s' i j))
