/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeEuclideanHsConstantMatrix
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity

/-!
# High-contrast homogenization: Provider.Regularity.CenteredCubeEuclideanHsFullNormConstantMatrix

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant matrices on the physical centered-cube Euclidean Hs full norm

The physical homogeneous full norm combines a scale-weighted normalized
Euclidean `L2` term with the square root of the Gagliardo energy.  Constant
matrix multiplication acts on both terms with the Euclidean matrix operator
norm, so the resulting estimate is dimension-free.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- The Euclidean operator norm controls pointwise constant-matrix
multiplication in the explicit Euclidean vector magnitude. -/
theorem euclideanNorm_matVecMul_le_l2_opNorm
    (A : Mat d) (x : Vec d) :
    euclideanNorm (matVecMul A x) ≤ ‖A‖ * euclideanNorm x := by
  apply (sq_le_sq₀
    (euclideanNorm_nonneg (matVecMul A x))
    (mul_nonneg (norm_nonneg A) (euclideanNorm_nonneg x))).mp
  rw [euclideanNorm_sq, mul_pow, euclideanNorm_sq]
  exact vecNormSq_matVecMul_le A x

/-- Constant matrix multiplication scales the normalized physical Euclidean
`L2` term by at most the Euclidean matrix operator norm. -/
theorem centeredCubeNormalizedEuclideanLpENorm_constMatrixMul_le
    (A : Mat d) (F : CenteredCubeEuclideanL2Field d m) :
    (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (centeredCubeEuclideanL2FieldConstMatrixMul A F) ≤
      ENNReal.ofReal ‖A‖ *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (centeredCubeEuclideanL2FieldConstMatrixMul A F).euclideanMagnitudeMemL2.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [centeredCubeEuclideanL2FieldConstMatrixMul_apply,
        Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _)] using
          euclideanNorm_matVecMul_le_l2_opNorm A (F x)

end

end HighContrast
end HCPolySupport
