{-# OPTIONS --cubical --safe --guardedness #-}
--
-- FAITHFULNESS — the located real specRadius M IS the operator norm ‖M‖, not just numerically.
--
-- The located real is built from the RUNNING power conditions (‖M^{2^L}‖₁ < q^{2^L}), an ℓ¹/diagonal
-- bracket sequence.  This module certifies it is faithful to the OPERATOR-NORM cut normUp M q
-- (= ‖Mx‖² < q²⟨x,x⟩ for all x≠0, i.e. ‖M‖ < q): every upper-cut witness implies the operator-norm
-- bound.  Hence specRadius's upper cut soundly bounds the operator norm — the spectral-radius real and
-- the C*-norm agree on the upper side.  Proof: lift any upper witness one squaring (upp-persist), then
-- run the C*-identity chain (normUp-from-pow).  No spectral theory — faithfulness rides on the landed
-- C*-identity.
--
module corpus.cubical_agda.Corridor.Running.General.SpecRadiusFaithful where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals using (ℚ)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.CStarRay using (normUp)
open import corpus.cubical_agda.Corridor.Running.General.SpecCutDisjoint using (upp-persist)
open import corpus.cubical_agda.Corridor.Running.General.PowerScaffold using (normUp-from-pow)
open import corpus.cubical_agda.Corridor.Running.General.SpecLocated using (UppRaw)

open Coefficient ℚCommRing using (Mat)
open Adjoint ℚCommRing using (_ᵀ)

-- every upper-cut witness of specRadius implies the operator-norm bound ‖M‖ < q.
U-sound : {n' : ℕ} (M : Mat (suc n') (suc n')) (symM : M ᵀ ≡ M) (q : ℚ)
        → UppRaw M symM q → normUp M q
U-sound M symM q (L , h) = normUp-from-pow M symM q L (upp-persist M symM q L h)
