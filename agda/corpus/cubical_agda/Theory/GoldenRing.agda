{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

------------------------------------------------------------------------------
-- Theory/GoldenRing.agda — the quadratic integer ring ℤ[φ] = ℤ[x]/(x²−x−1).
--
-- *** First-principles re-scope of the "ℝ-analysis (√/exp/log)" infrastructure phase. ***
-- Stripping names (mathematical-intuition Strategy 8/9), EVERY deferred "ℝ" conjunct in the
-- generative core (Tiers 0–4) is not about Cauchy reals at all — it is about the quadratic integer
-- ring ℤ[φ]: φ²=φ+1 (`phi_sq`), √5=2φ−1 (so √5²=5), the Galois conjugation φ↦ψ=1−φ
-- (`golden_irrational`/`φ↦ψ`), the norm a²+ab−b², and irrationality ¬∃c∈ℤ. c²=c+1
-- (`no_scalar_golden`). NONE needs transcendental analysis; all are decidable-equality algebra over
-- ℤ, hence clean `--cubical --safe` with ZERO postulates. (The genuine √/exp/log only appears in the
-- QED/QCD RG-flow PHYSICS tail, which the plan defers as the optional mechanical mirror.)
--
-- Representation: `a + b·φ ↦ gφ a b` (ℤ × ℤ), with the twisted multiplication forced by φ²=φ+1:
--   (a+bφ)(c+dφ) = ac + (ad+bc)φ + bd·φ² = (ac+bd) + (ad+bc+bd)φ.
-- The CommRing axioms, the Galois hom, and norm-multiplicativity reduce component-wise to ℤ ring
-- identities, discharged by `solve! ℤCommRing` (no manual ℤ-algebra). The computational headlines
-- (φ²=φ+1, √5²=5, conj φ = ψ, φ+ψ=1, φ·ψ=−1) hold by `refl` (cubical ℤ reduces concrete pos/negsuc).
--
-- Glue: the ring-element companion of `SplitQuaternionGolden` (which carries only the MATRIX shadow
-- `fib²=fib+I`); supplies `phi_sq`/`no_scalar_golden`/Galois to NumerationDualEigenform,
-- SpectralNucleusBridge, NoneistCohomology, NumerationGrothendieckInstitution, EigenformDichotomy.
-- The Fibonacci power law `φⁿ = Fₙ·φ + Fₙ₋₁` ties to `Zeckendorf.fib`.
--
-- Lean↔Agda (A3):
--   `GoldenRatioPisot.phi_sq` / Rhombohedral `phi_sq` ↔ `phi-sq`
--   `sqrt5_sq` / algebraic √5 witness                 ↔ `sqrt5-sq`
--   Galois `φ ↦ ψ`, `φ+ψ=1`, `φψ=-1`                  ↔ `conj-phi`, `phi+psi`, `phi*psi`
--   `no_scalar_golden` / golden irrationality          ↔ `no-scalar-golden`
--   Fibonacci power law for φ                          ↔ `phi-pow`
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.GoldenRing where

open import Cubical.Core.Primitives using (Type)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_; subst)
open import Cubical.Data.Int
  using (ℤ; pos; negsuc; _+_; _·_; -_; _-_; ·Comm; ·IdR; ·IdL; ·AnnihilR; ·AnnihilL; pos0+; +Comm
        ; pos·pos; negsuc·negsuc; injPos; posNotnegsuc)
open import Cubical.Data.Nat
  using (ℕ; zero; suc; snotz; znots; injSuc; +-zero) renaming (_·_ to _·ℕ_; _+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
  using (_<_; _≤_; <≤-trans; <-+k; ≤-·k; <→≢; suc-≤-suc; zero-≤)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

--------------------------------------------------------------------------------
-- The carrier ℤ[φ] = { a + b·φ : a b ∈ ℤ }
--------------------------------------------------------------------------------

record Gφ : Type where
  constructor gφ
  field
    a b : ℤ
open Gφ public

-- componentwise path (ℤ[φ] is a set; equality is determined by the two coordinates).
Gφ≡ : {x y : Gφ} → a x ≡ a y → b x ≡ b y → x ≡ y
Gφ≡ p q i = gφ (p i) (q i)

--------------------------------------------------------------------------------
-- Ring operations (the twisted multiplication forced by φ²=φ+1)
--------------------------------------------------------------------------------

0G 1G : Gφ
0G = gφ (pos 0) (pos 0)
1G = gφ (pos 1) (pos 0)

infixl 6 _+G_
infixl 7 _·G_

_+G_ : Gφ → Gφ → Gφ
x +G y = gφ (a x + a y) (b x + b y)

negG : Gφ → Gφ
negG x = gφ (- a x) (- b x)

-- (a+bφ)(c+dφ) = (ac+bd) + (ad+bc+bd)φ.
_·G_ : Gφ → Gφ → Gφ
x ·G y = gφ ((a x · a y) + (b x · b y))
            (((a x · b y) + (b x · a y)) + (b x · b y))

-- the ring embedding ℤ ↪ ℤ[φ] (`n ↦ n + 0·φ`).
fromℤ : ℤ → Gφ
fromℤ n = gφ n (pos 0)

--------------------------------------------------------------------------------
-- The distinguished elements: φ, its conjugate ψ = 1−φ, and √5 = 2φ−1
--------------------------------------------------------------------------------

φ ψ √5 : Gφ
φ  = gφ (pos 0) (pos 1)        -- φ        = 0 + 1·φ
ψ  = gφ (pos 1) (negsuc 0)     -- ψ = 1−φ  = 1 + (−1)·φ   (the Galois conjugate / other root)
√5 = gφ (negsuc 0) (pos 2)     -- √5 = 2φ−1 = (−1) + 2·φ

-- the Galois conjugation a+bφ ↦ a+bψ = (a+b) + (−b)φ  (sends φ to ψ).
conj : Gφ → Gφ
conj x = gφ (a x + b x) (- b x)

-- the field norm N(a+bφ) = (a+bφ)(a+bψ) = a² + ab − b²  (a SCALAR, ∈ ℤ).
-- (written with `+ (- …)` rather than binary `_-_`: the CommRing solver recognizes the ring's unary
-- negation but not `Cubical.Data.Int._-_`.)
norm : Gφ → ℤ
norm x = ((a x · a x) + (a x · b x)) + (- (b x · b x))

--------------------------------------------------------------------------------
-- Computational headlines (cubical ℤ reduces concrete pos/negsuc ⇒ `refl`)
--------------------------------------------------------------------------------

-- **φ² = φ + 1** — the defining golden relation. THE headline (`phi_sq`/`RhombohedralCell.phi_sq`).
phi-sq : φ ·G φ ≡ φ +G 1G
phi-sq = refl

-- **(√5)² = 5** — √5 lives in ℤ[φ] (no Cauchy reals needed).
sqrt5-sq : √5 ·G √5 ≡ fromℤ (pos 5)
sqrt5-sq = refl

-- **conj φ = ψ** — the Galois conjugation sends φ to the other root.
conj-phi : conj φ ≡ ψ
conj-phi = refl

-- **φ + ψ = 1** and **φ · ψ = −1** — φ, ψ are the two roots of x²−x−1 (trace 1, norm −1).
golden-sum : φ +G ψ ≡ 1G
golden-sum = refl

golden-prod : φ ·G ψ ≡ negG 1G
golden-prod = refl

-- **ψ ALSO satisfies the golden law ψ²=ψ+1** — the Galois conjugate is the *other* root of x²−x−1.
-- The golden law has a two-element solution set {φ, ψ} (the σ-orbit of the conjugation), neither in ℤ.
psi-sq : ψ ·G ψ ≡ ψ +G 1G
psi-sq = refl

-- **the minimal polynomial vanishes: φ² − φ − 1 = 0** — the defining relation of ℤ[x]/(x²−x−1), the
-- same content as `phi-sq` written as the vanishing of the monic minimal polynomial of φ.
golden-minpoly : ((φ ·G φ) +G negG φ) +G negG 1G ≡ 0G
golden-minpoly = refl

-- **N(φ) = −1** (the golden unit has norm −1, so φ is a unit of ℤ[φ]).
norm-phi : norm φ ≡ negsuc 0
norm-phi = refl

--------------------------------------------------------------------------------
-- The CommRing axioms (component-wise ℤ identities ⇒ `solve! ℤCommRing`)
--------------------------------------------------------------------------------

+G-comm : (x y : Gφ) → x +G y ≡ y +G x
+G-comm x y = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

+G-assoc : (x y z : Gφ) → (x +G y) +G z ≡ x +G (y +G z)
+G-assoc x y z = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

+G-idR : (x : Gφ) → x +G 0G ≡ x
+G-idR x = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

+G-invR : (x : Gφ) → x +G negG x ≡ 0G
+G-invR x = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

·G-comm : (x y : Gφ) → x ·G y ≡ y ·G x
·G-comm x y = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

·G-assoc : (x y z : Gφ) → (x ·G y) ·G z ≡ x ·G (y ·G z)
·G-assoc x y z = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

-- (`solve! ℤCommRing` chokes on literal `· pos 0`/`· pos 1` from `1G`; hand-proved via the ℤ unit /
-- annihilation lemmas.)
private
  +id0 : (z : ℤ) → z + pos 0 ≡ z
  +id0 z = +Comm z (pos 0) ∙ sym (pos0+ z)

·G-idR : (x : Gφ) → x ·G 1G ≡ x
·G-idR x = Gφ≡
  (cong₂ _+_ (·IdR (a x)) (·AnnihilR (b x)) ∙ +id0 (a x))
  (cong (_+ (b x · pos 0)) (cong₂ _+_ (·AnnihilR (a x)) (·IdR (b x)) ∙ sym (pos0+ (b x)))
    ∙ cong (b x +_) (·AnnihilR (b x)) ∙ +id0 (b x))

·G-distR : (x y z : Gφ) → x ·G (y +G z) ≡ (x ·G y) +G (x ·G z)
·G-distR x y z = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

--------------------------------------------------------------------------------
-- The Galois conjugation is a ring automorphism; the norm is multiplicative
--------------------------------------------------------------------------------

conj-involutive : (x : Gφ) → conj (conj x) ≡ x
conj-involutive x = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

conj-+ : (x y : Gφ) → conj (x +G y) ≡ conj x +G conj y
conj-+ x y = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

conj-· : (x y : Gφ) → conj (x ·G y) ≡ conj x ·G conj y
conj-· x y = Gφ≡ (solve! ℤCommRing) (solve! ℤCommRing)

-- **N(xy) = N(x)·N(y)** — the norm is a monoid hom ℤ[φ]ˣ → ℤˣ (the multiplicative invariant).
-- (`solve!` does not reflect through the `Gφ` field-projections on this degree-4 goal, so it is routed
-- through the raw 4-variable polynomial identity, which IS definitionally `norm (x ·G y) ≡ …`.)
private
  nm-raw : (a1 b1 a2 b2 : ℤ) →
    (((((a1 · a2) + (b1 · b2)) · (((a1 · a2) + (b1 · b2))))
        + (((a1 · a2) + (b1 · b2)) · (((a1 · b2) + (b1 · a2)) + (b1 · b2))))
        + (- ((((a1 · b2) + (b1 · a2)) + (b1 · b2)) · (((a1 · b2) + (b1 · a2)) + (b1 · b2)))))
    ≡ (((a1 · a1) + (a1 · b1)) + (- (b1 · b1))) · (((a2 · a2) + (a2 · b2)) + (- (b2 · b2)))
  nm-raw a1 b1 a2 b2 = solve! ℤCommRing

norm-mult : (x y : Gφ) → norm (x ·G y) ≡ norm x · norm y
norm-mult x y = nm-raw (a x) (b x) (a y) (b y)

-- **conj √5 = −√5** — under the Galois conjugation the irrational part flips sign (√5 ↦ −√5), exactly
-- the classical `a+b√5 ↦ a−b√5`. So `√5` is the "purely irrational" axis (fixed field of conj is ℤ·1).
conj-sqrt5 : conj √5 ≡ negG √5
conj-sqrt5 = refl

-- **N(√5) = −5** — consistent with `√5² = 5` and `conj √5 = −√5`: N(√5) = √5·conj(√5) = √5·(−√5) = −5.
norm-sqrt5 : norm √5 ≡ - (pos 5)
norm-sqrt5 = refl

--------------------------------------------------------------------------------
-- The golden ratio is IRRATIONAL: no integer scalar satisfies the golden law
--------------------------------------------------------------------------------

-- **¬ ∃ c ∈ ℤ. c² = c + 1** — `no_scalar_golden` (SpectralNucleusBridge's deferred conjunct). The
-- golden eigenform escapes the scalars; it lives only in the 2-dimensional ℤ[φ] (or the 2×2 companion
-- of `SplitQuaternionGolden`). Constructive, by exhaustive sign cases on `c` (no LEM): `c ∈ {0,1}`
-- are direct (`injPos` + `znots`/`injSuc`); `c ≥ 2` contradicts `c² = c+1` by the bound `suc c < c·c`
-- (`<-+k` ∘ `≤-·k`); `c ≤ −1` gives `c·c > 0 ≥ c+1` (`negsuc·negsuc` is a `pos`, `c+1` a `negsuc`/0).
private
  nn : (n : ℕ) → negsuc n · negsuc n ≡ pos (suc n ·ℕ suc n)
  nn n = negsuc·negsuc n n ∙ sym (pos·pos (suc n) (suc n))

no-scalar-golden : ¬ (Σ ℤ (λ c → c · c ≡ c + pos 1))
no-scalar-golden (pos zero , h)          = znots (injPos (pos·pos 0 0 ∙ h))
no-scalar-golden (pos (suc zero) , h)    = znots (injSuc (injPos (pos·pos 1 1 ∙ h)))
no-scalar-golden (pos (suc (suc k)) , h) = <→≢ bound (sym (injPos (pos·pos N N ∙ h)))
  where
  N : ℕ
  N = suc (suc k)
  2≤N : 2 ≤ N
  2≤N = suc-≤-suc (suc-≤-suc zero-≤)
  2N≡N+N : 2 ·ℕ N ≡ N +ℕ N
  2N≡N+N = cong (N +ℕ_) (+-zero N)
  bound : suc N < N ·ℕ N
  bound = <≤-trans (<-+k {1} {N} {N} 2≤N) (subst (_≤ N ·ℕ N) 2N≡N+N (≤-·k {2} {N} {N} 2≤N))
no-scalar-golden (negsuc zero , h)       = snotz (injPos (sym (nn 0) ∙ h))
no-scalar-golden (negsuc (suc j) , h)    = posNotnegsuc _ _ (sym (nn (suc j)) ∙ h)

--------------------------------------------------------------------------------
-- The Fibonacci power law: φⁿ⁺¹ = Fₙ + Fₙ₊₁·φ  (the golden ratio REALIZES the Fibonacci recurrence)
--------------------------------------------------------------------------------

-- φ acts on `a + bφ` as the shift `(a , b) ↦ (b , a+b)` — the Fibonacci step itself: multiplying by φ
-- pushes the pair through one Fibonacci recurrence (this IS why φ governs Fibonacci growth).
φ-mul : (g : Gφ) → φ ·G g ≡ gφ (b g) (a g + b g)
φ-mul g = Gφ≡
  (cong₂ _+_ (·AnnihilL (a g)) (·IdL (b g)) ∙ sym (pos0+ (b g)))
  (cong (_+ (pos 1 · b g)) (cong₂ _+_ (·AnnihilL (b g)) (·IdL (a g)) ∙ sym (pos0+ (a g)))
    ∙ cong (a g +_) (·IdL (b g)))

infixl 8 _^G_
_^G_ : Gφ → ℕ → Gφ
g ^G zero    = 1G
g ^G (suc n) = g ·G (g ^G n)

-- the Fibonacci numbers, ℤ-valued (so the recurrence is ℤ-addition; `fibℤ = Zeckendorf.fib` embedded).
fibℤ : ℕ → ℤ
fibℤ zero          = pos 0
fibℤ (suc zero)    = pos 1
fibℤ (suc (suc k)) = fibℤ (suc k) + fibℤ k

-- **φⁿ⁺¹ = Fₙ + Fₙ₊₁·φ** (`fib_realizes_golden` / `RhombohedralCell`'s deferred conjunct, in FULL — the
-- ring-element form, not just the matrix `fib²=fib+I` shadow). By induction: the base is `·G-idR`; the
-- step is exactly `φ-mul` (the Fibonacci shift) composed with the recurrence `Fₙ₊₂ = Fₙ₊₁ + Fₙ`.
phi-pow : (n : ℕ) → (φ ^G (suc n)) ≡ gφ (fibℤ n) (fibℤ (suc n))
phi-pow zero    = ·G-idR φ
phi-pow (suc m) = cong (φ ·G_) (phi-pow m)
              ∙ φ-mul (gφ (fibℤ m) (fibℤ (suc m)))
              ∙ cong (gφ (fibℤ (suc m))) (+Comm (fibℤ m) (fibℤ (suc m)))

-- concrete: φ⁵ = 3 + 5φ = F₄ + F₅·φ (the law COMPUTES the golden powers, by `refl` ∼ via `phi-pow`).
golden-fib-5 : φ ^G 5 ≡ gφ (pos 3) (pos 5)
golden-fib-5 = phi-pow 4
