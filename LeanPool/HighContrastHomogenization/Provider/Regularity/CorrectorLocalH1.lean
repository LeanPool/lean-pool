/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalLimit

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorLocalH1

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local Sobolev representatives of projective limits

The projective local carrier stores value and gradient `L²` classes together
with membership in the closed weak-gradient graph.  This module recovers the
canonical `H¹` representative on each exhaustion cube and records its exact
class-level characterization.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

namespace NormalizedLocalH1Carrier

/-- The canonical local `H¹` representative determined by the value-gradient
pair on the `n`th exhaustion cube. -/
@[expose]
noncomputable def localH1Function {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    H1Function (localGradientCube d n) :=
  toH1FunctionOfMemH1Graph
    (z.valueComponent n, z.gradientComponent n) (z.graph n)

/-- The scalar `L²` class of the recovered local function is the stored value
component. -/
@[simp] theorem localH1Function_toScalarL2 {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    (z.localH1Function n).toScalarL2 = z.valueComponent n := by
  exact toH1FunctionOfMemH1Graph_toScalarL2
    (z.valueComponent n, z.gradientComponent n) (z.graph n)

/-- The Hilbert-vector `L²` gradient class of the recovered local function is
the stored gradient component. -/
@[simp] theorem localH1Function_gradToHilbertVectorL2 {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    (z.localH1Function n).gradToHilbertVectorL2 = z.gradientComponent n := by
  exact toH1FunctionOfMemH1Graph_gradToHilbertVectorL2
    (z.valueComponent n, z.gradientComponent n) (z.graph n)

/-- The recovered value representative agrees almost everywhere with the
stored scalar class. -/
theorem localH1Function_toFun_ae {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    (z.localH1Function n).toFun =ᵐ[volumeMeasureOn (localGradientCube d n)]
      z.valueComponent n := by
  have h := (z.localH1Function n).coeFn_toScalarL2
  rw [localH1Function_toScalarL2] at h
  exact h.symm

/-- The unit-cube local representative has the normalization stored by the
projective carrier. -/
theorem localH1Function_zero_mean {d : ℕ}
    (z : NormalizedLocalH1Carrier d) :
    MeanZeroOn (localGradientCube d 0) (z.localH1Function 0).toFun := by
  have hmean := z.unitMeanZero
  rw [scalarIntegralCLM_apply] at hmean
  calc
    ∫ x in localGradientCube d 0, (z.localH1Function 0).toFun x
        ∂volume =
        ∫ x in localGradientCube d 0, z.valueComponent 0 x
          ∂volume := by
            exact integral_congr_ae (z.localH1Function_toFun_ae 0)
    _ = 0 := hmean

end NormalizedLocalH1Carrier

end

end HighContrast
end HCPolySupport
