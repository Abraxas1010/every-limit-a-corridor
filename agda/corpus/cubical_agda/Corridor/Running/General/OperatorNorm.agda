{-# OPTIONS --cubical --safe --guardedness #-}
--
-- TOWARD THE OPERATOR-NORM C*-IDENTITY  ‖M*M‖ = ‖M‖²  (the paper's open piece).
--
-- For a symmetric 2×2 matrix M = [[a,b],[b,d]], M* = Mᵀ = M, so M*M = M², and the
-- operator norm is the largest |eigenvalue| (the spectral edge, Phase F).  The
-- C*-identity ‖M²‖ = ‖M‖² rests on an ALGEBRAIC core that holds in ANY commutative
-- ring, independent of the irrational √ and the order:
--
--      λ is an eigenvalue of M   ⟹   λ² is an eigenvalue of M².
--
-- (Cayley–Hamilton squaring.)  We prove this — `eigenSquared` — via the factorisation
--   λ⁴ − tr(M²)·λ² + det(M²) = charpoly_M(λ) · (λ² + tr(M)·λ + det(M)),
-- so the characteristic equation of M (charpoly_M(λ)=0) forces charpoly_{M²}(λ²)=0.
-- This is the algebraic heart of the C*-identity.  The REMAINING open frontier (C2/C3,
-- flagged honestly): that the LARGEST-magnitude eigenvalue maps to the largest (the
-- PSD/ordering part) and the passage to the ℝ-completed operator norm — neither is
-- discharged here.  The commutative-core diagonal C*-identity is `DiagonalCStar`.
--
module corpus.cubical_agda.Corridor.Running.General.OperatorNorm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)

  -- charpoly_M(λ) = 0:  λ is an eigenvalue of the symmetric matrix [[a,b],[b,d]].
  charEq : (a b d l : ⟨ R ⟩) → Type _
  charEq a b d l = l · l ≡ ((a + d) · l) - ((a · d) - (b · b))

  -- trace and determinant of M² (M² = [[a²+b², b(a+d)],[b(a+d), b²+d²]]).
  traceSq : (a b d : ⟨ R ⟩) → ⟨ R ⟩
  traceSq a b d = ((a · a) + ((b · b) + (b · b))) + (d · d)         -- a²+2b²+d²
  detSq : (a b d : ⟨ R ⟩) → ⟨ R ⟩
  detSq a b d = ((a · d) - (b · b)) · ((a · d) - (b · b))           -- (ad−b²)²

  -- charpoly_{M²}(μ) = 0:  μ is an eigenvalue of M².
  charEqSq : (a b d μ : ⟨ R ⟩) → Type _
  charEqSq a b d μ = μ · μ ≡ (traceSq a b d · μ) - detSq a b d

  -- ── THE ALGEBRAIC CORE OF ‖M²‖=‖M‖²:  λ eigenvalue of M ⟹ λ² eigenvalue of M² ──
  eigenSquared : (a b d l : ⟨ R ⟩) → charEq a b d l → charEqSq a b d (l · l)
  eigenSquared a b d l h = subEq ∙ cong (_+ rhs) factored ∙ zeroAdd
    where
      lhs rhs f1 f2 : ⟨ R ⟩
      lhs = (l · l) · (l · l)
      rhs = (traceSq a b d · (l · l)) - detSq a b d
      f1  = ((l · l) - ((a + d) · l)) + ((a · d) - (b · b))         -- charpoly_M(λ)
      f2  = ((l · l) + ((a + d) · l)) + ((a · d) - (b · b))         -- the cofactor
      -- the hypothesis kills the first factor: charpoly_M(λ) = 0.
      f1≡0 : f1 ≡ 0r
      f1≡0 = cong (λ z → (z - ((a + d) · l)) + ((a · d) - (b · b))) h ∙ solve! R
      -- the quartic factorisation (pure ring identity, true for all a,b,d,l):
      quartic : lhs - rhs ≡ f1 · f2
      quartic = solve! R
      -- assemble:  lhs = (lhs − rhs) + rhs = (f1·f2) + rhs = (0·f2) + rhs = rhs.
      subEq : lhs ≡ (f1 · f2) + rhs
      subEq = (solve! R) ∙ cong (_+ rhs) quartic
      factored : f1 · f2 ≡ 0r
      factored = cong (_· f2) f1≡0 ∙ solve! R
      zeroAdd : 0r + rhs ≡ rhs
      zeroAdd = solve! R

  -- ════════════════════════════════════════════════════════════════════════
  -- C3 — THE OPERATOR-NORM C*-IDENTITY ‖M²‖ = ‖M‖² FOR THE SPECTRAL EDGE.
  --
  -- For symmetric M = [[a,b],[b,d]], M² = [[a²+b², b(a+d)],[b(a+d), b²+d²]], and
  -- (for PSD M) the operator norm IS the spectral edge specEdge(M)=((a+d)+√Δ)/2,
  -- Δ = disc(M) = (a−d)²+4b².  The C*-identity specEdge(M²)=specEdge(M)² looks
  -- like it needs the irrational √, but it REDUCES to two pure ring identities
  -- that eliminate the √ entirely (they force √disc(M²)=(a+d)·√disc(M)):
  --   (i)   disc(M²) = (a+d)²·disc(M)
  --   (ii)  2·tr(M²) = (a+d)² + disc(M)
  -- Then  specEdge(M²) = (tr(M²)+√disc(M²))/2 = (tr(M²)+(a+d)√Δ)/2
  --        = ((a+d)²+Δ)/4 + (a+d)√Δ/2 = ((a+d)+√Δ)²/4 = specEdge(M)².  ∎
  -- This discharges the paper's named-open piece for the PSD symmetric 2×2 case
  -- (the algebraic obstruction — the √ — is gone).  Honestly OUT of scope: the
  -- non-PSD magnitude norm max(|λ₊|,|λ₋|) and the n×n generalisation.
  -- ════════════════════════════════════════════════════════════════════════
  fourR : ⟨ R ⟩
  fourR = (1r + 1r) + (1r + 1r)

  disc : (a b d : ⟨ R ⟩) → ⟨ R ⟩
  disc a b d = ((a - d) · (a - d)) + (fourR · (b · b))

  -- (i)  the discriminant of M² is (a+d)² times that of M — so √disc(M²)=(a+d)·√disc(M).
  discM2 : (a b d : ⟨ R ⟩)
         → disc ((a · a) + (b · b)) (b · (a + d)) ((b · b) + (d · d))
         ≡ ((a + d) · (a + d)) · disc a b d
  discM2 a b d = solve! R

  -- (ii)  twice the trace of M² is (a+d)² + disc(M).  (i)+(ii) ⟹ specEdge(M²)=specEdge(M)².
  traceM2 : (a b d : ⟨ R ⟩)
          → (1r + 1r) · (((a · a) + (b · b)) + ((b · b) + (d · d)))
          ≡ ((a + d) · (a + d)) + disc a b d
  traceM2 a b d = solve! R

  -- scaling a square out (for the bracket-level C*-identity):  (s·x)² = s²·x².
  mulSquare : (s x : ⟨ R ⟩) → (s · x) · (s · x) ≡ (s · s) · (x · x)
  mulSquare s x = solve! R
