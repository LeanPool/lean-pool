/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.MonomialEvaluationMatrix

/-!
# Coefficient bounds for interpolation polynomials

A polynomial assembled by `polynomialOfCoefficients` from an integer coefficient vector
bounded by `R` has every coefficient bounded by `R`. The Bombieri–Vaaler auxiliary
constructions of the determinant method use this to bound the coefficients of the auxiliary
polynomial. Nondivisibility by the defining polynomial is a separate step, proved from the
global determinant lower bound in Section 3.3.
-/

@[expose] public section

namespace CCDN

open Matrix

/-- If the monomials `mon` are distinct and the integer coefficient vector `v` lies in the box
of radius `R ≥ 0`, then every coefficient of `polynomialOfCoefficients mon v` has absolute
value at most `R`. -/
theorem abs_coefficient_polynomialOfCoefficients_le {n N : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (hmon : Function.Injective mon)
    (v : Fin N → ℤ) {R : ℝ} (hR : 0 ≤ R) (hv : InBox v R)
    (e : Fin n →₀ ℕ) :
    |((polynomialOfCoefficients mon v).coeff e : ℝ)| ≤ R := by
  classical
  by_cases he : ∃ j, mon j = e
  · obtain ⟨j, rfl⟩ := he
    rw [coefficient_polynomialOfCoefficients mon hmon]
    exact hv j
  · have hz : (polynomialOfCoefficients mon v).coeff e = 0 := by
      simp [polynomialOfCoefficients, MvPolynomial.coeff_monomial, not_exists.mp he]
    simpa [hz] using hR

end CCDN
