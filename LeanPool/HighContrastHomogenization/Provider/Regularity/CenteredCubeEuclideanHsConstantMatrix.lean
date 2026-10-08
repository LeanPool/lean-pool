/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalKernel
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientFieldHilbert
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.CenteredCubeEuclideanH2

/-!
# High-contrast homogenization: Provider.Regularity.CenteredCubeEuclideanHsConstantMatrix

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant matrices on the physical centered-cube Euclidean Hs carrier

The rounded reference is controlled in the Euclidean matrix operator norm.
This module keeps that norm all the way through the physical fractional
carrier: constant matrix multiplication preserves the stored Euclidean `L2`
field, multiplies its squared Gagliardo energy by at most the square of the
matrix norm, and therefore preserves `MemCenteredCubeEuclideanHs`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- Pointwise constant-matrix multiplication, packaged as a centered-cube
Euclidean `L2` field. -/
@[expose]
noncomputable def centeredCubeEuclideanL2FieldConstMatrixMul
    (A : Mat d) (F : CenteredCubeEuclideanL2Field d m) :
    CenteredCubeEuclideanL2Field d m where
  toField := fun x ↦ matVecMul A (F x)
  euclideanMemL2 := by
    have h := F.euclideanMemL2.continuousLinearMap_comp (HilbertVec.applyMat A)
    simpa only [Function.comp_apply, HilbertVec.applyMat_apply,
      HilbertVec.toVec_ofVec] using h

@[simp] theorem centeredCubeEuclideanL2FieldConstMatrixMul_apply
    (A : Mat d) (F : CenteredCubeEuclideanL2Field d m) (x : Vec d) :
    centeredCubeEuclideanL2FieldConstMatrixMul A F x = matVecMul A (F x) :=
  rfl

end

end HighContrast
end HCPolySupport
