/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakLp

/-!
# High-contrast homogenization: Provider.Response.ProfileCenterMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of metric center fluctuations

The diagonal metric quadratic form is a continuous polynomial on the finite
product carrier.  Consequently every measurable optimizer average has a
measurable metric fluctuation about a deterministic center.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The canonical diagonal metric quadratic form is continuous. -/
theorem continuous_metricBlockNormSq (m : Mat d) :
    Continuous (metricBlockNormSq m) := by
  have hfst (i : Fin d) : Continuous (fun X : BlockVec d ↦ X.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hsnd (i : Fin d) : Continuous (fun X : BlockVec d ↦ X.2 i) :=
    (continuous_apply i).comp continuous_snd
  rw [show metricBlockNormSq m = fun X : BlockVec d ↦
      ∑ i, X.1 i * ∑ j, m i j * X.1 j +
        ∑ i, X.2 i * ∑ j, m⁻¹ i j * X.2 j by
    funext X
    rw [metricBlockNormSq_eq]
    simp only [vecDot, matVecMul]]
  exact (continuous_finsetSum _ fun i _ ↦
      (hfst i).mul (continuous_finsetSum _ fun j _ ↦
        continuous_const.mul (hfst j))).add
    (continuous_finsetSum _ fun i _ ↦
      (hsnd i).mul (continuous_finsetSum _ fun j _ ↦
        continuous_const.mul (hsnd j)))

/-- The square-root metric fluctuation of an a.e. measurable doubled vector
about a deterministic center is a.e. measurable. -/
theorem AEMeasurable.sqrt_metricBlockNormSq_sub_const
    {P : Measure (CoeffSpace d)} {X : CoeffSpace d → BlockVec d}
    (hX : AEMeasurable X P) (m : Mat d) (center : BlockVec d) :
    AEMeasurable (fun a ↦
      Real.sqrt (metricBlockNormSq m (X a - center))) P := by
  have hsub : AEMeasurable (fun a ↦ X a - center) P :=
    hX.sub aemeasurable_const
  exact ((continuous_metricBlockNormSq m).measurable.comp_aemeasurable hsub).sqrt

end

end HCPolySupport.HighContrast.Response
