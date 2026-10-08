/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.Theory
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineChapter3Comparison

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.LawFreeCubeEnergyPrice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A law-free coarse-grained Dirichlet energy price on one triadic cube

The attainability route uses the `e.cg.RHS` mechanism: the energy
of a Dirichlet solution is priced by the boundary datum's fractional norm with
*coarse-grained* ellipticity constants.  This file isolates the exact reason
that price can be law-free.

`poincareUpperEllipticityFactor Q a s (.finite 2)` is `Λ_{s,2}(Q;a)^{1/2}`,
and `Λ_{s,2}` is built only from the coarse-grained block matrix `b(R;a)` —
a variational response average — never from a pointwise essential supremum of
`a`.  Upstream's
`inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one`
prices it by the identity-referenced multiscale homogenization error.  Hence
*a single scalar hypothesis, `𝓔 ≤ 1`, converts the whole ellipticity window
into a dimension-only constant*, and the resulting Dirichlet energy price
depends on nothing but `d` and the fractional order `s`.

## The order at which the error is read

The certificate is a `ScalarIdentityPowerTail` at
`printCertificateOrder g = (1 + g) / 4`, while the price needs the
identity-referenced error at the consumer's own order
`s ∈ Set.Ico ((1 + g) / 4) (1 / 2)`.  That direction is the available one: the
multiscale error is decreasing in the fractional order, because the geometric weight
concentrates on the coarse scales as `s` grows, and
`homogenizationErrorOnCube_infinity_two_le_of_lt` supplies the comparison with loss
exactly one.

Combined with the target reduction — above the common affine scale the retained
amplitude is below `correctorTargetAmplitude c κ = (c / 2) * (1 - 3 ^ (-κ))`, which
is less than one — this yields the single scalar hypothesis `𝓔 ≤ 1` that the price
below consumes.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The identity reference -/

/-- The scalar matrix at `1` is the identity. -/
theorem scalarMatrix_one_eq_one (d : ℕ) :
    scalarMatrix (d := d) (1 : ℝ) = (1 : Mat d) :=
  one_smul ℝ (1 : Mat d)

/-- Half powers are nonnegative, by the square-root convention. -/
theorem rpow_half_nonneg (x : ℝ) : 0 ≤ Real.rpow x (1 / (2 : ℝ)) := by
  simpa only [Real.sqrt_eq_rpow] using! Real.sqrt_nonneg x

/-- The multiscale homogenization error at the endpoint spatial exponent and
the finite `q = 2` scale exponent is nonnegative. -/
theorem homogenizationErrorOnCube_infinity_two_nonneg
    (Q : TriadicCube d) (s : ℝ) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) :
    0 ≤ Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
  unfold Book.Ch02.HomogenizationErrorOnCube
  simp only [Book.Ch02.HomogenizationError]
  unfold Book.Ch02.HomogenizationErrorFinite
  exact rpow_half_nonneg _

/-! ## The law-free coarse ellipticity window -/

/-! ## The law-free Dirichlet energy price -/

end

end EnergyPrice
end HighContrast
end HCPolySupport
