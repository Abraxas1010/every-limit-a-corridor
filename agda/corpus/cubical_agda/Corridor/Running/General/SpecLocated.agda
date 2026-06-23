{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE LOCATED CORE — for 0 < a < b, either a is a (raw) lower bound or b is a (raw) upper bound.
--
-- This is the analytic heart of the spectral-radius cut's locatedness.  Run geom-beat to find a level
-- where n²·a^{2^L} < b^{2^L}; lift it to suc L (where M^{2^L} = B⋆B is a square) by beat-suc; then
-- DECIDE (finite, decidable) whether some diagonal of M^{2^{suc L}} exceeds a^{2^{suc L}}.  Yes ⟹ a
-- is below ρ (a raw lower-cut witness).  No ⟹ every diagonal ≤ a^{2^{suc L}}, so by the off-diagonal
-- bound ‖M^{2^{suc L}}‖₁ ≤ a^{2^{suc L}}·n² < b^{2^{suc L}} ⟹ b is above ρ (a raw upper-cut witness).
-- No spectral theory; the disjunction is made by a finite rational comparison.
--
module corpus.cubical_agda.Corridor.Running.General.SpecLocated where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fz; suc to fsuc)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁) renaming (map to ∥map∥)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_; <Dec; isTrans<; isTrans≤<; ≮→≥; <Weaken≤)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.OneNormDiagBound using (nSq; oneNorm-diag-bound)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (pow2; qpow; pow2-sym)
open import corpus.cubical_agda.Corridor.Running.General.QpowMono using (0≤qpow')
open import corpus.cubical_agda.Corridor.Running.General.GeomBeat using (geom-beat)
open import corpus.cubical_agda.Corridor.Running.General.SpecLocHelpers using (1≤nSq; beat-suc)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ)

-- finite existential is decidable (cubical has no DecΣ over Fin).
∃Fin-dec : (n : ℕ) (P : Fin n → Type₀) → ((i : Fin n) → Dec (P i)) → Dec (Σ[ i ∈ Fin n ] P i)
∃Fin-dec zero    P decP = no (λ { (() , _) })
∃Fin-dec (suc n) P decP with decP fz
... | yes p0 = yes (fz , p0)
... | no ¬p0 with ∃Fin-dec n (λ i → P (fsuc i)) (λ i → decP (fsuc i))
...   | yes (i , pi) = yes (fsuc i , pi)
...   | no ¬rest = no (λ { (fz , p) → ¬p0 p ; (fsuc i , p) → ¬rest (i , p) })

module _ {n' : ℕ} (M : Mat (suc n') (suc n')) (symM : M ᵀ ≡ M) where

  -- the raw lower / upper witnesses (expanded forms of lowAt / uppAt).
  LowRaw UppRaw : ℚ → Type₀
  LowRaw q = Σ[ L ∈ ℕ ] Σ[ i ∈ Fin (suc n') ] (qpow L q < (pow2 L M) i i)
  UppRaw q = Σ[ L ∈ ℕ ] (oneNorm (pow2 L M) < qpow L q)

  coreLoc : (a b : ℚ) → 0 < a → a < b → ∥ LowRaw a ⊎ ((0 < b) × UppRaw b) ∥₁
  coreLoc a b 0<a a<b = ∥map∥ use (geom-beat a b 0<a a<b (nSq (suc n')))
    where
      0<b : 0 < b
      0<b = isTrans< 0 a b 0<a a<b
      0≤a : 0 ≤ a
      0≤a = <Weaken≤ 0 a 0<a
      use : Σ[ L ∈ ℕ ] ((nSq (suc n') · qpow L a) < qpow L b)
          → LowRaw a ⊎ ((0 < b) × UppRaw b)
      use (L , beat) with
        ∃Fin-dec (suc n') (λ i → qpow (suc L) a < (pow2 (suc L) M) i i)
                  (λ i → <Dec (qpow (suc L) a) ((pow2 (suc L) M) i i))
      ... | yes (i , wit) = inl (suc L , i , wit)
      ... | no ¬ex = inr (0<b , (suc L , uppWit))
        where
          beatS : (nSq (suc n') · qpow (suc L) a) < qpow (suc L) b
          beatS = beat-suc (nSq (suc n')) a b (1≤nSq n') 0≤a L beat
          diag≤ : (k : Fin (suc n')) → ((pow2 L M ⋆ pow2 L M) k k) ≤ qpow (suc L) a
          diag≤ k = ≮→≥ (qpow (suc L) a) ((pow2 (suc L) M) k k) (λ h → ¬ex (k , h))
          -- ‖M^{2^{suc L}}‖₁ ≤ a^{2^{suc L}}·n² = n²·a^{2^{suc L}} < b^{2^{suc L}}.
          bound : oneNorm (pow2 L M ⋆ pow2 L M) ≤ (qpow (suc L) a · nSq (suc n'))
          bound = oneNorm-diag-bound (pow2 L M) (pow2-sym M symM L)
                    (qpow (suc L) a) (0≤qpow' (suc L) a 0≤a) diag≤
          uppWit : oneNorm (pow2 (suc L) M) < qpow (suc L) b
          uppWit = isTrans≤< (oneNorm (pow2 (suc L) M)) (nSq (suc n') · qpow (suc L) a) (qpow (suc L) b)
                     (subst (oneNorm (pow2 (suc L) M) ≤_) (·Comm (qpow (suc L) a) (nSq (suc n'))) bound)
                     beatS
