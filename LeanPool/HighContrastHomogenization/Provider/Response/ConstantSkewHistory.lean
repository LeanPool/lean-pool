/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewProfiles

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewHistory

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew invariance of nonlinear histories and drift

Common shear congruence preserves the trace of a relative mean, determinant
increments, and the inverse-times-increment trace used by the fixed-grid
drift.  These identities complete the passage between hatted terminal data
and the portable histories.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal Matrix

noncomputable section

variable {d : ℕ}

/-- The trace of inverse times numerator is invariant under a common shear
congruence. -/
theorem trace_inv_mul_skewBlockCongr (g : Mat d) (A E : BlockMat d) :
    Matrix.trace
        ((toFullBlockMat (skewBlockCongr g E))⁻¹ *
          toFullBlockMat (skewBlockCongr g A)) =
      Matrix.trace ((toFullBlockMat E)⁻¹ * toFullBlockMat A) := by
  let C : FullBlockMat d := fullBlockShear g
  have hCdet : IsUnit C.det :=
    (Matrix.isUnit_iff_isUnit_det C).mp (isUnit_fullBlockShear g)
  have hCHdet : IsUnit Cᴴ.det :=
    (Matrix.isUnit_iff_isUnit_det Cᴴ).mp (isUnit_fullBlockShear g).star
  simp only [toFullBlockMat_skewBlockCongr]
  change Matrix.trace
      ((Cᴴ * toFullBlockMat E * C)⁻¹ *
        (Cᴴ * toFullBlockMat A * C)) = _
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    Matrix.trace
        ((C⁻¹ * ((toFullBlockMat E)⁻¹ * (Cᴴ)⁻¹)) *
          (Cᴴ * toFullBlockMat A * C)) =
        Matrix.trace
          (C⁻¹ * (toFullBlockMat E)⁻¹ * ((Cᴴ)⁻¹ * Cᴴ) *
            toFullBlockMat A * C) := by
              congr 1
              noncomm_ring
    _ = Matrix.trace
        (C⁻¹ * (toFullBlockMat E)⁻¹ * toFullBlockMat A * C) := by
          rw [Matrix.nonsing_inv_mul _ hCHdet, Matrix.mul_one]
    _ = Matrix.trace
        (C * (C⁻¹ * (toFullBlockMat E)⁻¹) * toFullBlockMat A) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace ((toFullBlockMat E)⁻¹ * toFullBlockMat A) := by
          rw [← Matrix.mul_assoc C C⁻¹ (toFullBlockMat E)⁻¹,
            Matrix.mul_nonsing_inv _ hCdet, Matrix.one_mul]

end

end HCPolySupport.HighContrast.Response
