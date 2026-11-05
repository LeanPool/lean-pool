/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateTotalDegree
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import LeanPool.CCDN.Plane.GridHeight

/-! Integral norm polynomials and the two signed plane equations
needed to count square-norm generators. The norm polynomial retains the full
number-field degree even when its parameter lies in a proper subfield. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField Polynomial

variable (K : Type*) [Field K] [NumberField K]

/-- The integer norm polynomial of `β ∈ 𝓞 K`: the characteristic polynomial of multiplication by
`β`, whose value at `x ∈ ℤ` is the norm `N(x - β)`. -/
def integerNormPolynomial (β : 𝓞 K) : ℤ[X] :=
  (Algebra.lmul ℤ (𝓞 K) β).charpoly

/-- The integer norm polynomial of an algebraic integer is monic. -/
lemma integerNormPolynomial_monic (β : 𝓞 K) :
    (integerNormPolynomial K β).Monic :=
  LinearMap.charpoly_monic _

/-- The integer norm polynomial of an algebraic integer of `K` has degree `[K : ℚ]`. -/
lemma integerNormPolynomial_natDegree (β : 𝓞 K) :
    (integerNormPolynomial K β).natDegree = Module.finrank ℚ K := by
  rw [integerNormPolynomial, LinearMap.charpoly_natDegree, RingOfIntegers.rank]

/-- The integer norm polynomial of `β` evaluated at `x ∈ ℤ` is the norm `N(x - β)`. -/
lemma integerNormPolynomial_eval (β : 𝓞 K) (x : ℤ) :
    (integerNormPolynomial K β).eval x =
      Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) := by
  rw [integerNormPolynomial, LinearMap.eval_charpoly, Algebra.norm_apply,
    map_sub (Algebra.lmul ℤ (𝓞 K)), Algebra.lmul_algebraMap]
  rfl

/-- The signed norm-curve polynomial `y ^ 2 - ε * N(x - β)` in the plane coordinates `(y, x)`,
where `N(x - β)` is the integer norm polynomial of `β`: on an integral point the first
coordinate is a square root of the norm and the second is the integral translation parameter. -/
def signedNormCurvePolynomial (β : 𝓞 K) (ε : ℤ) : MvPolynomial (Fin 2) ℤ :=
  (bivariatePolynomialEquiv ℤ).symm
    (X ^ 2 - C (C ε * integerNormPolynomial K β))

private lemma signedNormCurvePolynomial_eval (β : 𝓞 K) (ε x y : ℤ) :
    MvPolynomial.eval ![y, x] (signedNormCurvePolynomial K β ε) =
      y ^ 2 - ε * Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) := by
  rw [← bivariatePolynomialEquiv_eval _ y x]
  simp [signedNormCurvePolynomial, integerNormPolynomial_eval]

/-- If `|N(x - β)| = m ^ 2`, then `(m, x)` is an integral point on one of the two signed norm curves
`y ^ 2 = N(x - β)` or `y ^ 2 = -N(x - β)`. -/
lemma square_norm_yields_signedNormCurve_point
    (β : 𝓞 K) (x : ℤ) (m : ℕ)
    (h : (Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β)).natAbs = m ^ 2) :
    MvPolynomial.eval ![(m : ℤ), x] (signedNormCurvePolynomial K β 1) = 0 ∨
      MvPolynomial.eval ![(m : ℤ), x] (signedNormCurvePolynomial K β (-1)) = 0 := by
  have ha : |Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β)| = (m : ℤ) ^ 2 := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow]
      using congrArg (Nat.cast : ℕ → ℤ) h
  rcases (abs_eq (by positivity)).mp ha with hp | hn
  · left
    rw [signedNormCurvePolynomial_eval, hp]
    ring
  · right
    rw [signedNormCurvePolynomial_eval, hn]
    ring

end
end CCDN
