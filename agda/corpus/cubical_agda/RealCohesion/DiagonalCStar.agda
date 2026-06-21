{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 6 / D2 (the C*-norm).  The full operator norm of M_n needs ℝ-suprema;
-- but the COMMUTATIVE core -- the diagonal subalgebra C(Fin n) = (Fin n → ℚ),
-- the Gelfand spectrum -- carries a genuine rational-valued C*-norm: the sup
-- norm ‖f‖ = maxᵢ|fᵢ|, with the C*-identity ‖f★f‖ = ‖f‖² (here f★ = f, since ℚ
-- is a real C*-algebra with trivial involution).  This gives the AF tower's
-- diagonal Cartan subalgebra a genuine C*-norm -- no postulates.

module corpus.cubical_agda.RealCohesion.DiagonalCStar where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; <Dec; <-·o; ≤-·o; ≤-o+; ≤Monotone+; isTrans<; isTrans≤; isTrans≤<
        ; isTrans<≤; isIrrefl<; ≮→≥; <Weaken≤; isAntisym≤; isRefl≤)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import corpus.cubical_agda.RealCohesion.RealApprox using (neg-mult)
open import corpus.cubical_agda.RealCohesion.RealNegation using (neg-flip)

-- ── absolute value on ℚ ────────────────────────────────────────────────────
absℚ : ℚ → ℚ
absℚ x with <Dec x 0
... | yes _ = - x
... | no  _ = x

-0≡0 : (- 0) ≡ 0
-0≡0 = ·AnnihilR -1

0≤absℚ : (x : ℚ) → 0 ≤ absℚ x
0≤absℚ x with <Dec x 0
... | yes x<0 = <Weaken≤ 0 (- x) (subst (_< (- x)) -0≡0 (neg-flip x 0 x<0))
... | no ¬x<0 = ≮→≥ x 0 ¬x<0

absℚ-sq : (x : ℚ) → absℚ x · absℚ x ≡ x · x
absℚ-sq x with <Dec x 0
... | yes _ = neg-mult x (- x) ∙ cong -_ (·Comm x (- x) ∙ neg-mult x x) ∙ -Invol (x · x)
... | no  _ = refl

0≤sq-all : (x : ℚ) → 0 ≤ (x · x)
0≤sq-all x = subst (0 ≤_) (absℚ-sq x)
               (subst (_≤ (absℚ x · absℚ x)) (·AnnihilL (absℚ x))
                 (≤-·o 0 (absℚ x) (absℚ x) (0≤absℚ x) (0≤absℚ x)))

absℚ-of-nonneg : {z : ℚ} → 0 ≤ z → absℚ z ≡ z
absℚ-of-nonneg {z} 0≤z with <Dec z 0
... | yes z<0 = rec (isIrrefl< z (isTrans<≤ z 0 z z<0 0≤z))
... | no  _   = refl

absℚ-of-sq : (x : ℚ) → absℚ (x · x) ≡ x · x
absℚ-of-sq x = absℚ-of-nonneg (0≤sq-all x)

-- ── binary maximum on ℚ ────────────────────────────────────────────────────
maxℚ : ℚ → ℚ → ℚ
maxℚ a b with <Dec a b
... | yes _ = b
... | no  _ = a

maxℚ-yes : {a b : ℚ} → a < b → maxℚ a b ≡ b
maxℚ-yes {a} {b} a<b with <Dec a b
... | yes _ = refl
... | no ¬p = rec (¬p a<b)

maxℚ-no : {a b : ℚ} → ¬ (a < b) → maxℚ a b ≡ a
maxℚ-no {a} {b} ¬a<b with <Dec a b
... | yes p = rec (¬a<b p)
... | no  _ = refl

0≤maxℚ : {a b : ℚ} → 0 ≤ a → 0 ≤ b → 0 ≤ maxℚ a b
0≤maxℚ {a} {b} 0≤a 0≤b with <Dec a b
... | yes _ = 0≤b
... | no  _ = 0≤a

-- squaring is monotone on the nonnegatives
sq-mono : (x y : ℚ) → 0 ≤ x → x < y → (x · x) < (y · y)
sq-mono x y 0≤x x<y = isTrans≤< (x · x) (y · x) (y · y) xx≤yx yx<yy
  where
    0<y : 0 < y
    0<y = isTrans≤< 0 x y 0≤x x<y
    xx≤yx : (x · x) ≤ (y · x)
    xx≤yx = ≤-·o x y x 0≤x (<Weaken≤ x y x<y)
    yx<yy : (y · x) < (y · y)
    yx<yy = subst (_< (y · y)) (·Comm x y) (<-·o x y y 0<y x<y)

sq-mono-≤ : (x y : ℚ) → 0 ≤ x → x ≤ y → (x · x) ≤ (y · y)
sq-mono-≤ x y 0≤x x≤y = isTrans≤ (x · x) (y · x) (y · y) xx≤yx yx≤yy
  where
    0≤y : 0 ≤ y
    0≤y = isTrans≤ 0 x y 0≤x x≤y
    xx≤yx : (x · x) ≤ (y · x)
    xx≤yx = ≤-·o x y x 0≤x x≤y
    yx≤yy : (y · x) ≤ (y · y)
    yx≤yy = subst (_≤ (y · y)) (·Comm x y) (≤-·o x y y 0≤y x≤y)

-- THE CORE LEMMA: max commutes with squaring on the nonnegatives.
maxℚ-sq : (x y : ℚ) → 0 ≤ x → 0 ≤ y
        → maxℚ (x · x) (y · y) ≡ (maxℚ x y) · (maxℚ x y)
maxℚ-sq x y 0≤x 0≤y with <Dec x y
... | yes x<y = maxℚ-yes {x · x} {y · y} (sq-mono x y 0≤x x<y)
... | no ¬x<y = maxℚ-no {x · x} {y · y} ¬sq
      where
        y²≤x² : (y · y) ≤ (x · x)
        y²≤x² = sq-mono-≤ y x 0≤y (≮→≥ x y ¬x<y)
        ¬sq : ¬ ((x · x) < (y · y))
        ¬sq x²<y² = isIrrefl< (x · x) (isTrans<≤ (x · x) (y · y) (x · x) x²<y² y²≤x²)

-- ── the diagonal C*-algebra C(Fin (suc n)) = (Fin (suc n) → ℚ) ──────────────
-- sup-norm of f over the finite point-set (nonempty, by suc n).
‖_‖ : {n : ℕ} → (Fin (suc n) → ℚ) → ℚ
‖_‖ {zero}  f = absℚ (f zero)
‖_‖ {suc n} f = maxℚ (absℚ (f zero)) (‖ (λ i → f (suc i)) ‖)

0≤‖‖ : {n : ℕ} (f : Fin (suc n) → ℚ) → 0 ≤ ‖ f ‖
0≤‖‖ {zero}  f = 0≤absℚ (f zero)
0≤‖‖ {suc n} f = 0≤maxℚ {absℚ (f zero)} {‖ (λ i → f (suc i)) ‖}
                        (0≤absℚ (f zero)) (0≤‖‖ (λ i → f (suc i)))

-- THE C*-IDENTITY: ‖f★f‖ = ‖f‖².  Here (f★f)ᵢ = fᵢ·fᵢ (★ trivial over ℚ).
cstar-identity : {n : ℕ} (f : Fin (suc n) → ℚ)
               → ‖ (λ i → f i · f i) ‖ ≡ ‖ f ‖ · ‖ f ‖
cstar-identity {zero}  f = absℚ-of-sq (f zero) ∙ sym (absℚ-sq (f zero))
cstar-identity {suc n} f =
    cong₂ maxℚ (absℚ-of-sq (f zero) ∙ sym (absℚ-sq (f zero)))
               (cstar-identity (λ i → f (suc i)))
  ∙ maxℚ-sq (absℚ (f zero)) (‖ (λ i → f (suc i)) ‖)
      (0≤absℚ (f zero)) (0≤‖‖ (λ i → f (suc i)))

-- ── the diagonal AF tower: Bratteli inclusions are ISOMETRIES ───────────────
-- The corner Bratteli inclusion, on the diagonal, prepends a 0 entry.
ιD : {n : ℕ} → (Fin (suc n) → ℚ) → (Fin (suc (suc n)) → ℚ)
ιD f zero    = 0
ιD f (suc i) = f i

absℚ0 : absℚ 0 ≡ 0
absℚ0 = refl

maxℚ-0 : (c : ℚ) → 0 ≤ c → maxℚ 0 c ≡ c
maxℚ-0 c 0≤c with <Dec 0 c
... | yes _    = refl
... | no ¬0<c  = isAntisym≤ 0 c 0≤c (≮→≥ 0 c ¬0<c)

-- The Bratteli inclusion is ISOMETRIC: ‖ιD f‖ = ‖f‖ (the new 0 entry does not
-- change the sup norm).  Hence the diagonal C*-norm is well-defined on the AF
-- LIMIT -- the inductive limit of the diagonals is a genuine COMMUTATIVE AF
-- C*-algebra over ℚ, built from the SAME corner-inclusion Bratteli diagram as the
-- golden tower (its diagonal/Cartan pattern).  Scope note: this is a separate ℚ-
-- valued construction, not a formally-proven subalgebra-embedding C(Fin n) ↪ A∞.
ιD-isometric : {n : ℕ} (f : Fin (suc n) → ℚ) → ‖ ιD f ‖ ≡ ‖ f ‖
ιD-isometric f = cong (λ z → maxℚ z (‖ f ‖)) absℚ0 ∙ maxℚ-0 (‖ f ‖) (0≤‖‖ f)

-- ── submultiplicativity: ‖f·g‖ ≤ ‖f‖·‖g‖ ───────────────────────────────────
-- nonneg square-root is injective: a²=b² with a,b≥0 ⟹ a=b.
sq-inj : (a b : ℚ) → 0 ≤ a → 0 ≤ b → a · a ≡ b · b → a ≡ b
sq-inj a b 0≤a 0≤b a²≡b² = isAntisym≤ a b a≤b b≤a
  where
    a≤b : a ≤ b
    a≤b = ≮→≥ b a (λ b<a → isIrrefl< (b · b)
                    (subst (b · b <_) a²≡b² (sq-mono b a 0≤b b<a)))
    b≤a : b ≤ a
    b≤a = ≮→≥ a b (λ a<b → isIrrefl< (a · a)
                    (subst (a · a <_) (sym a²≡b²) (sq-mono a b 0≤a a<b)))

-- |·| is multiplicative (via the square characterization).
private
  rearr : (x y : ℚ) → (x · y) · (x · y) ≡ (x · x) · (y · y)
  rearr x y =
    (x · y) · (x · y)   ≡⟨ sym (·Assoc x y (x · y)) ⟩
    x · (y · (x · y))   ≡⟨ cong (x ·_) (·Assoc y x y) ⟩
    x · ((y · x) · y)   ≡⟨ cong (λ z → x · (z · y)) (·Comm y x) ⟩
    x · ((x · y) · y)   ≡⟨ cong (x ·_) (sym (·Assoc x y y)) ⟩
    x · (x · (y · y))   ≡⟨ ·Assoc x x (y · y) ⟩
    (x · x) · (y · y) ∎

absℚ-mult : (x y : ℚ) → absℚ (x · y) ≡ absℚ x · absℚ y
absℚ-mult x y = sq-inj (absℚ (x · y)) (absℚ x · absℚ y)
                  (0≤absℚ (x · y)) 0≤rhs sq-eq
  where
    0≤rhs : 0 ≤ (absℚ x · absℚ y)
    0≤rhs = subst (_≤ (absℚ x · absℚ y)) (·AnnihilL (absℚ y))
              (≤-·o 0 (absℚ x) (absℚ y) (0≤absℚ y) (0≤absℚ x))
    sq-eq : absℚ (x · y) · absℚ (x · y) ≡ (absℚ x · absℚ y) · (absℚ x · absℚ y)
    sq-eq = absℚ-sq (x · y) ∙ rearr x y
          ∙ cong₂ _·_ (sym (absℚ-sq x)) (sym (absℚ-sq y))
          ∙ sym (rearr (absℚ x) (absℚ y))

-- the sup-norm is an upper bound for each entry, and the least such.
a≤maxℚ : {a b : ℚ} → a ≤ maxℚ a b
a≤maxℚ {a} {b} with <Dec a b
... | yes a<b = <Weaken≤ a b a<b
... | no  _   = isRefl≤ a

b≤maxℚ : {a b : ℚ} → b ≤ maxℚ a b
b≤maxℚ {a} {b} with <Dec a b
... | yes _    = isRefl≤ b
... | no ¬a<b  = ≮→≥ a b ¬a<b

maxℚ-lub : {a b c : ℚ} → a ≤ c → b ≤ c → maxℚ a b ≤ c
maxℚ-lub {a} {b} {c} a≤c b≤c with <Dec a b
... | yes _ = b≤c
... | no  _ = a≤c

entry≤norm : {n : ℕ} (f : Fin (suc n) → ℚ) (i : Fin (suc n)) → absℚ (f i) ≤ ‖ f ‖
entry≤norm {zero}  f zero    = isRefl≤ (absℚ (f zero))
entry≤norm {suc n} f zero    = a≤maxℚ {absℚ (f zero)} {‖ (λ i → f (suc i)) ‖}
entry≤norm {suc n} f (suc j) =
  isTrans≤ (absℚ (f (suc j))) (‖ (λ i → f (suc i)) ‖) (‖ f ‖)
    (entry≤norm (λ i → f (suc i)) j)
    (b≤maxℚ {absℚ (f zero)} {‖ (λ i → f (suc i)) ‖})

norm-ub : {n : ℕ} {c : ℚ} (h : Fin (suc n) → ℚ)
        → ((i : Fin (suc n)) → absℚ (h i) ≤ c) → ‖ h ‖ ≤ c
norm-ub {zero}  h hb = hb zero
norm-ub {suc n} h hb = maxℚ-lub {absℚ (h zero)} {‖ (λ i → h (suc i)) ‖}
                         (hb zero) (norm-ub (λ i → h (suc i)) (λ j → hb (suc j)))

-- THE SUBMULTIPLICATIVE LAW: ‖f·g‖ ≤ ‖f‖·‖g‖ (pointwise product).
submult : {n : ℕ} (f g : Fin (suc n) → ℚ) → ‖ (λ i → f i · g i) ‖ ≤ ‖ f ‖ · ‖ g ‖
submult f g = norm-ub (λ i → f i · g i) bound
  where
    bound : (i : Fin _) → absℚ (f i · g i) ≤ ‖ f ‖ · ‖ g ‖
    bound i = subst (_≤ (‖ f ‖ · ‖ g ‖)) (sym (absℚ-mult (f i) (g i)))
                (isTrans≤ (absℚ (f i) · absℚ (g i)) (‖ f ‖ · absℚ (g i)) (‖ f ‖ · ‖ g ‖)
                  step1 step2)
      where
        step1 : (absℚ (f i) · absℚ (g i)) ≤ (‖ f ‖ · absℚ (g i))
        step1 = ≤-·o (absℚ (f i)) (‖ f ‖) (absℚ (g i)) (0≤absℚ (g i)) (entry≤norm f i)
        step2 : (‖ f ‖ · absℚ (g i)) ≤ (‖ f ‖ · ‖ g ‖)
        step2 = subst2 _≤_ (·Comm (absℚ (g i)) (‖ f ‖)) (·Comm (‖ g ‖) (‖ f ‖))
                  (≤-·o (absℚ (g i)) (‖ g ‖) (‖ f ‖) (0≤‖‖ f) (entry≤norm g i))

-- ── triangle inequality: ‖f+g‖ ≤ ‖f‖+‖g‖ ───────────────────────────────────
-- nonneg square-root is monotone (reverse): a²≤b² with 0≤b ⟹ a≤b.
sq-le-rev : (a b : ℚ) → 0 ≤ b → a · a ≤ b · b → a ≤ b
sq-le-rev a b 0≤b a²≤b² =
  ≮→≥ b a (λ b<a → isIrrefl< (b · b)
            (isTrans<≤ (b · b) (a · a) (b · b) (sq-mono b a 0≤b b<a) a²≤b²))

-- z ≤ |z| (and hence x·y ≤ |x|·|y|).
≤-absℚ : (z : ℚ) → z ≤ absℚ z
≤-absℚ z with <Dec z 0
... | yes z<0 = <Weaken≤ z (- z)
                  (isTrans< z 0 (- z) z<0 (subst (_< (- z)) -0≡0 (neg-flip z 0 z<0)))
... | no  _   = isRefl≤ z

private
  expand : (a b : ℚ) → (a + b) · (a + b) ≡ ((a · a + b · b) + (a · b + a · b))
  expand a b =
    (a + b) · (a + b)
      ≡⟨ ·DistL+ (a + b) a b ⟩
    ((a + b) · a) + ((a + b) · b)
      ≡⟨ cong₂ _+_ (·DistR+ a b a) (·DistR+ a b b) ⟩
    ((a · a + b · a) + (a · b + b · b))
      ≡⟨ cong (λ z → (a · a + z) + (a · b + b · b)) (·Comm b a) ⟩
    ((a · a + a · b) + (a · b + b · b))
      ≡⟨ sym (+Assoc (a · a) (a · b) (a · b + b · b)) ⟩
    (a · a + (a · b + (a · b + b · b)))
      ≡⟨ cong (a · a +_) (+Assoc (a · b) (a · b) (b · b)) ⟩
    (a · a + ((a · b + a · b) + b · b))
      ≡⟨ cong (a · a +_) (+Comm (a · b + a · b) (b · b)) ⟩
    (a · a + (b · b + (a · b + a · b)))
      ≡⟨ +Assoc (a · a) (b · b) (a · b + a · b) ⟩
    ((a · a + b · b) + (a · b + a · b)) ∎

absℚ-triangle : (x y : ℚ) → absℚ (x + y) ≤ absℚ x + absℚ y
absℚ-triangle x y = sq-le-rev (absℚ (x + y)) (absℚ x + absℚ y) 0≤sum sq-le
  where
    0≤sum : 0 ≤ (absℚ x + absℚ y)
    0≤sum = subst (_≤ (absℚ x + absℚ y)) (+IdR 0)
              (≤Monotone+ 0 (absℚ x) 0 (absℚ y) (0≤absℚ x) (0≤absℚ y))
    xy≤uv : (x · y) ≤ (absℚ x · absℚ y)
    xy≤uv = subst ((x · y) ≤_) (absℚ-mult x y) (≤-absℚ (x · y))
    sq-le : absℚ (x + y) · absℚ (x + y) ≤ (absℚ x + absℚ y) · (absℚ x + absℚ y)
    sq-le = subst2 _≤_ (sym lhs≡) (sym rhs≡) middle
      where
        lhs≡ : absℚ (x + y) · absℚ (x + y)
             ≡ ((x · x + y · y) + (x · y + x · y))
        lhs≡ = absℚ-sq (x + y) ∙ expand x y
        rhs≡ : (absℚ x + absℚ y) · (absℚ x + absℚ y)
             ≡ ((x · x + y · y) + (absℚ x · absℚ y + absℚ x · absℚ y))
        rhs≡ = expand (absℚ x) (absℚ y)
             ∙ cong (_+ (absℚ x · absℚ y + absℚ x · absℚ y))
                    (cong₂ _+_ (absℚ-sq x) (absℚ-sq y))
        middle : ((x · x + y · y) + (x · y + x · y))
               ≤ ((x · x + y · y) + (absℚ x · absℚ y + absℚ x · absℚ y))
        middle = ≤-o+ (x · y + x · y) (absℚ x · absℚ y + absℚ x · absℚ y) (x · x + y · y)
                   (≤Monotone+ (x · y) (absℚ x · absℚ y) (x · y) (absℚ x · absℚ y) xy≤uv xy≤uv)

-- THE TRIANGLE INEQUALITY for the sup-norm.
norm-triangle : {n : ℕ} (f g : Fin (suc n) → ℚ)
              → ‖ (λ i → f i + g i) ‖ ≤ ‖ f ‖ + ‖ g ‖
norm-triangle f g = norm-ub (λ i → f i + g i) bound
  where
    bound : (i : Fin _) → absℚ (f i + g i) ≤ ‖ f ‖ + ‖ g ‖
    bound i = isTrans≤ (absℚ (f i + g i)) (absℚ (f i) + absℚ (g i)) (‖ f ‖ + ‖ g ‖)
                (absℚ-triangle (f i) (g i))
                (≤Monotone+ (absℚ (f i)) (‖ f ‖) (absℚ (g i)) (‖ g ‖)
                  (entry≤norm f i) (entry≤norm g i))

-- ── definiteness: ‖f‖ = 0 ⟹ f = 0 ──────────────────────────────────────────
absℚ-zero→ : {z : ℚ} → absℚ z ≡ 0 → z ≡ 0
absℚ-zero→ {z} az≡0 with <Dec z 0
... | yes _ = sym (-Invol z) ∙ cong -_ az≡0 ∙ -0≡0
... | no  _ = az≡0

norm-definite : {n : ℕ} (f : Fin (suc n) → ℚ) → ‖ f ‖ ≡ 0
              → (i : Fin (suc n)) → f i ≡ 0
norm-definite f n≡0 i = absℚ-zero→ (isAntisym≤ (absℚ (f i)) 0 |fi|≤0 (0≤absℚ (f i)))
  where
    |fi|≤0 : absℚ (f i) ≤ 0
    |fi|≤0 = subst (absℚ (f i) ≤_) n≡0 (entry≤norm f i)
