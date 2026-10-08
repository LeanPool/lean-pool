/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.DeterminantLoss
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import LeanPool.HighContrastHomogenization.Setup.TransportObjects

/-!
# High-contrast homogenization: Provider.ShortHop.PathStep

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The candidate of the short test

The candidate witness of `p.successful.short.bridge` is the next point
on the fixed constant-speed projective path from the current witness to the
canonical metric of the old grid's terminal block: the path point at parameter
`min{c_hop/d_pr, 1}`, and the endpoint itself when the two projective classes
already agree.  Two of the three candidate clauses of the proposition are proved
here — the candidate is a positive witness, and the projective jump to it is at
most the hop length.  The third, the bound on the cross-grid factor, is the hop
distortion read at those two facts.

The path point `m(θ) = m₀^{1/2}(m₀^{-1/2}m₁m₀^{-1/2})^θm₀^{1/2}` is a congruence
of the real power of the normalized pair, so normalizing it by `m₀^{-1/2}` gives
back that real power exactly.  Positive definiteness is then the positive
definiteness of the real power carried across the congruence, and the printed
form of the projective distance — half the sum of the logarithms of the sizes of
the normalized pair and of its inverse — turns the constant-speed bound into the
two size bounds of the real power.  This is where the path is *constant speed*:
each of the two logarithms is multiplied by `θ`, so the distance is at most `θ`
times the distance to the endpoint.

The zero branch costs nothing: the candidate is the endpoint, and the distance to
it is the vanishing distance itself.
-/

namespace HCPolySupport
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The path point as a congruence -/

/-- **Normalizing the path point returns the real power.**  The path point is the
congruence of `(m₀^{-1/2}m₁m₀^{-1/2})^θ` by `m₀^{1/2}`, and conjugating back by
`m₀^{-1/2}` undoes it. -/
theorem normalize_projPath {m0 m1 : Mat d} (h0 : m0.PosDef) (theta : ℝ) :
    matSqrt m0⁻¹ * projPath m0 m1 theta * matSqrt m0⁻¹ =
      matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) := by
  have hu : IsUnit (matSqrt m0).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt h0)
  have hleft : matSqrt m0⁻¹ * matSqrt m0 = 1 := by
    rw [matSqrt_inv h0]; exact Matrix.nonsing_inv_mul _ hu
  have hright : matSqrt m0 * matSqrt m0⁻¹ = 1 := by
    rw [matSqrt_inv h0]; exact Matrix.mul_nonsing_inv _ hu
  calc matSqrt m0⁻¹ * projPath m0 m1 theta * matSqrt m0⁻¹
      = matSqrt m0⁻¹ * matSqrt m0 *
          matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) *
          (matSqrt m0 * matSqrt m0⁻¹) := by
        simp only [projPath]; noncomm_ring
    _ = matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) := by
        rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]

/-! ## The constant-speed bound -/

/-! ## The candidate -/

/-- The canonical metric of a positive definite doubled block is a positive
witness. -/
theorem posDef_canonicalMetric {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) :
    (canonicalMetric E).PosDef := posDef_canonMetric hE

end

end ShortHop
end HighContrast
end HCPolySupport
