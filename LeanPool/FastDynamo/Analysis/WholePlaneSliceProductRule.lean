/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleSlices

/-!
# Product rule along whole-plane coordinate slices

This file supplies the generic calculus bridge used by the slice integration-by-parts argument.
A Fréchet derivative of a concrete field at a point on a coordinate slice becomes an ordinary
derivative along that slice, whose velocity is `wholePlaneBasis j`.  Combining this chain rule
with the derivative of a Schwartz test function gives exactly the product-rule expression used
by `hasWholePlaneIntegralWeakDerivative_of_ae_fiberwise_product`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped LineDeriv SchwartzMap

/-- Chain and product rule for a Schwartz scalar times a concrete vector-valued field along a
whole-plane coordinate slice. -/
theorem hasDerivAt_schwartz_smul_wholePlaneSliceEquiv
    {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    (φ : SchwartzMap WholePlane ℂ) (u : WholePlane → F)
    (Du : WholePlane →L[ℝ] F) (j : Fin 2) (x t : ℝ)
    (hu : HasFDerivAt u Du (wholePlaneSliceEquiv j (x, t))) :
    HasDerivAt
      (fun v : ℝ ↦
        φ (wholePlaneSliceEquiv j (x, v)) •
          u (wholePlaneSliceEquiv j (x, v)))
      (((∂_{wholePlaneBasis j} φ) (wholePlaneSliceEquiv j (x, t))) •
          u (wholePlaneSliceEquiv j (x, t)) +
        φ (wholePlaneSliceEquiv j (x, t)) • Du (wholePlaneBasis j)) t := by
  have hslice := wholePlaneSliceEquiv_hasDerivAt j x t
  have hφ_comp : HasDerivAt
      (φ ∘ fun v : ℝ ↦ wholePlaneSliceEquiv j (x, v))
      ((∂_{wholePlaneBasis j} φ) (wholePlaneSliceEquiv j (x, t))) t := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      ((φ.hasFDerivAt (wholePlaneSliceEquiv j (x, t))).comp t hslice).hasDerivAt
  have hφ : HasDerivAt
      (fun v : ℝ ↦ φ (wholePlaneSliceEquiv j (x, v)))
      ((∂_{wholePlaneBasis j} φ) (wholePlaneSliceEquiv j (x, t))) t :=
    hφ_comp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hu_comp : HasDerivAt
      (u ∘ fun v : ℝ ↦ wholePlaneSliceEquiv j (x, v))
      (Du (wholePlaneBasis j)) t := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (hu.comp t hslice).hasDerivAt
  have hu_slice : HasDerivAt
      (fun v : ℝ ↦ u (wholePlaneSliceEquiv j (x, v)))
      (Du (wholePlaneBasis j)) t :=
    hu_comp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  exact ((hφ.smul hu_slice).congr_deriv (by rw [add_comm])).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)

end

end FastDynamo
