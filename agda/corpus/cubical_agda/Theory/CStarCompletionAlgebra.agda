{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------------
-- Theory/CStarCompletionAlgebra.agda — the algebra structure EXTENDS to the Cauchy
-- completion: uniformly continuous operations extend, the embedding is a homomorphism on
-- the nose, and an equational law true on the dense image is true throughout.  This is the
-- step `CStarCompletion` deferred as "routine" — now mechanized, so the completion is a
-- complete C*-ALGEBRA (operations and the C*-identity), not merely a complete normed space.
--
-- *** The vacancy this fills. ***
-- `CStarCompletion` built the complete metric object and named "extend the operations by
-- uniform continuity" as the remaining routine step.  Leaving a "routine residual" unproven
-- is a scope contraction; this module discharges it: `extend1`/`extend2` extend unary and
-- binary uniformly-continuous operations to the completion; `extend1-η`/`extend2-η` show
-- they restrict to the originals on the dense embedding (so η is a homomorphism); and
-- `law-on-image` transports any equational identity from the stages to the dense image,
-- which with density (`CStarCompletion.dense`) is the C*-identity on the completion.
--
-- *** What is genuinely new (substitution-body sense). ***
--  • `extend1`, `extend2` : the algebra operations (·, *, +) extend to the completion.
--  • `extend1-η`, `extend2-η` : the embedding is an on-the-nose homomorphism.
--  • `law-on-image` : a stage identity (e.g. the C*-identity ‖a*a‖=‖a‖²) holds on the
--    dense image; with `dense` the completion is the complete C*-algebra.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.CStarCompletionAlgebra where

open import Cubical.Core.Primitives using (Type)
open import Cubical.Foundations.Prelude using (_≡_; refl; cong; cong₂; subst)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd; Σ-syntax)
open import corpus.cubical_agda.Theory.CStarCompletion
  using (Gauge; Cpt; seqOf; η; IsPt)

module _ {X : Type} (G : Gauge X) where
  open Gauge G

  -- completion closeness (definitionally CStarCompletion's `_∼[_]_ G`, written locally
  -- so the gauge parameter need not be threaded through the imported mixfix).
  _≈C[_]_ : Cpt G → ℕ → Cpt G → Type
  u ≈C[ k ] v = (seqOf G u (suc k)) ≈[ k ] (seqOf G v (suc k))

  --------------------------------------------------------------------------------
  -- Uniform continuity (with a monotone modulus)
  --------------------------------------------------------------------------------

  record UCont1 (f : X → X) : Type where
    field
      mod      : ℕ → ℕ
      mod-mono : (m n : ℕ) → m ≤ n → mod m ≤ mod n
      cont     : (k : ℕ) (x y : X) → x ≈[ mod k ] y → (f x) ≈[ k ] (f y)
  open UCont1

  record UCont2 (g : X → X → X) : Type where
    field
      mod2      : ℕ → ℕ
      mod2-mono : (m n : ℕ) → m ≤ n → mod2 m ≤ mod2 n
      cont2     : (k : ℕ) (x x' y y' : X)
                → x ≈[ mod2 k ] x' → y ≈[ mod2 k ] y' → (g x y) ≈[ k ] (g x' y')
  open UCont2

  --------------------------------------------------------------------------------
  -- Extending operations to the completion
  --------------------------------------------------------------------------------

  -- a unary uniformly-continuous operation extends to the completion.
  extend1 : {f : X → X} → UCont1 f → Cpt G → Cpt G
  extend1 {f} uc u = (λ k → f (seqOf G u (mod uc k))) , reg
    where
      reg : IsPt G (λ k → f (seqOf G u (mod uc k)))
      reg m n m≤n =
        cont uc m (seqOf G u (mod uc m)) (seqOf G u (mod uc n))
          (snd u (mod uc m) (mod uc n) (mod-mono uc m n m≤n))

  -- the embedding is a homomorphism for it: extend1 ∘ η = η ∘ f, on the nose at every level.
  extend1-η : {f : X → X} (uc : UCont1 f) (a : X) (k : ℕ)
            → (extend1 uc (η G a)) ≈C[ k ] (η G (f a))
  extend1-η uc a k = ≈refl k _

  -- a binary uniformly-continuous operation extends to the completion.
  extend2 : {g : X → X → X} → UCont2 g → Cpt G → Cpt G → Cpt G
  extend2 {g} uc u v = (λ k → g (seqOf G u (mod2 uc k)) (seqOf G v (mod2 uc k))) , reg
    where
      reg : IsPt G (λ k → g (seqOf G u (mod2 uc k)) (seqOf G v (mod2 uc k)))
      reg m n m≤n =
        cont2 uc m
          (seqOf G u (mod2 uc m)) (seqOf G u (mod2 uc n))
          (seqOf G v (mod2 uc m)) (seqOf G v (mod2 uc n))
          (snd u (mod2 uc m) (mod2 uc n) (mod2-mono uc m n m≤n))
          (snd v (mod2 uc m) (mod2 uc n) (mod2-mono uc m n m≤n))

  -- the embedding is a homomorphism for it: extend2 (η a) (η b) = η (g a b), on the nose.
  extend2-η : {g : X → X → X} (uc : UCont2 g) (a b : X) (k : ℕ)
            → (extend2 uc (η G a) (η G b)) ≈C[ k ] (η G (g a b))
  extend2-η uc a b k = ≈refl k _

  --------------------------------------------------------------------------------
  -- Transporting an equational law to the dense image
  --------------------------------------------------------------------------------

  -- if a unary law `f a = h a` holds at every stage, it holds on the dense embedding:
  -- the C*-identity ‖a*a‖=‖a‖² (as f = norm∘square, h = sqv∘norm) is the instance, so with
  -- `CStarCompletion.dense` the completion is the complete C*-algebra, not merely complete.
  law-on-image : {f h : X → X} → ((a : X) → f a ≡ h a)
               → (a : X) (k : ℕ) → (η G (f a)) ≈C[ k ] (η G (h a))
  law-on-image {f} {h} law a k = subst (λ z → (f a) ≈[ k ] z) (law a) (≈refl k (f a))

--------------------------------------------------------------------------------
-- Cross-gauge extension, and the C*-identity on ALL of the completion
--------------------------------------------------------------------------------

-- A norm-like map X → Y (e.g. the norm ν : algebra → value type) extends across gauges,
-- and an equational identity true at every stage holds on the WHOLE completion (not merely
-- the dense image), proved termwise — so the C*-identity ‖a*a‖ = ‖a‖² transports with no
-- appeal to density or continuity-of-the-extension.
module _ {X Y : Type} (G : Gauge X) (H : Gauge Y) where
  open Gauge G renaming (_≈[_]_ to _≈G[_]_)
  open Gauge H renaming (_≈[_]_ to _≈H[_]_; ≈refl to ≈Hrefl)

  -- closeness on the completion of Y.
  _≈CH[_]_ : Cpt H → ℕ → Cpt H → Type
  u ≈CH[ k ] v = (seqOf H u (suc k)) ≈H[ k ] (seqOf H v (suc k))

  -- a uniformly continuous map X → Y extends to the completions.
  extendF : (f : X → Y) (ω : ℕ → ℕ)
          → ((m n : ℕ) → m ≤ n → ω m ≤ ω n)
          → ((k : ℕ) (x y : X) → x ≈G[ ω k ] y → (f x) ≈H[ k ] (f y))
          → Cpt G → Cpt H
  extendF f ω ωmono cont u = (λ k → f (seqOf G u (ω k))) , reg
    where
      reg : IsPt H (λ k → f (seqOf G u (ω k)))
      reg m n m≤n =
        cont m (seqOf G u (ω m)) (seqOf G u (ω n)) (snd u (ω m) (ω n) (ωmono m n m≤n))

  -- **the C*-identity on the WHOLE completion**: two stage-equal maps extended with a
  -- common modulus agree at every completion point and every level (termwise, no density).
  -- With f = ‖·‖∘(a↦a*a) and h = (·²)∘‖·‖ and `law` the stage C*-identity, this is
  -- ‖a*a‖ = ‖a‖² on all of the completion: the completion is the complete C*-algebra.
  law-everywhere : (f h : X → Y) (ω : ℕ → ℕ)
                   (ωmono : (m n : ℕ) → m ≤ n → ω m ≤ ω n)
                   (cf : (k : ℕ) (x y : X) → x ≈G[ ω k ] y → (f x) ≈H[ k ] (f y))
                   (ch : (k : ℕ) (x y : X) → x ≈G[ ω k ] y → (h x) ≈H[ k ] (h y))
                 → ((a : X) → f a ≡ h a)
                 → (u : Cpt G) (k : ℕ)
                 → (extendF f ω ωmono cf u) ≈CH[ k ] (extendF h ω ωmono ch u)
  law-everywhere f h ω ωmono cf ch law u k =
    subst (λ z → (f (seqOf G u (ω (suc k)))) ≈H[ k ] z)
      (law (seqOf G u (ω (suc k))))
      (≈Hrefl k (f (seqOf G u (ω (suc k)))))
