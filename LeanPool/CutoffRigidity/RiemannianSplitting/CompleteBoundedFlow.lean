/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedVectorField

/-! # The canonical global flow of an actual complete bounded field
The map is chosen from the proved global ODE existence theorem. All identities
follow from actual manifold integral-curve uniqueness, not supplied action laws.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)

/-- The actual canonical flow of a bounded C¹ field on a complete manifold. -/
noncomputable def completeBoundedFlow (x : M) (t : ℝ) : M :=
  (exists_global_integralCurve_of_bounded hX hbound x).choose t

theorem completeBoundedFlow_zero (x : M) : completeBoundedFlow hX hbound x 0 = x :=
  (exists_global_integralCurve_of_bounded hX hbound x).choose_spec.1

theorem completeBoundedFlow_isMIntegralCurve (x : M) :
    IsMIntegralCurve (completeBoundedFlow hX hbound x) X :=
  (exists_global_integralCurve_of_bounded hX hbound x).choose_spec.2

/-- Every actual global integral curve is this canonical flow through its
initial point. -/
theorem completeBoundedFlow_unique {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) :
    γ = completeBoundedFlow hX hbound (γ 0) :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hX hγ
    (completeBoundedFlow_isMIntegralCurve hX hbound (γ 0))
    (completeBoundedFlow_zero hX hbound (γ 0)).symm

/-- The flow group law, proved from the actual ODE. -/
theorem completeBoundedFlow_add (x : M) (s t : ℝ) :
    completeBoundedFlow hX hbound x (t + s) =
      completeBoundedFlow hX hbound (completeBoundedFlow hX hbound x s) t := by
  have h := completeBoundedFlow_unique hX hbound
    ((completeBoundedFlow_isMIntegralCurve hX hbound x).comp_add s)
  simpa using congrFun h t

theorem completeBoundedFlow_neg_cancel (x : M) (t : ℝ) :
    completeBoundedFlow hX hbound (completeBoundedFlow hX hbound x t) (-t) = x := by
  rw [← completeBoundedFlow_add, neg_add_cancel, completeBoundedFlow_zero]

/-- Each time slice is bijective with inverse the negative-time slice. -/
noncomputable def completeBoundedFlowEquiv (t : ℝ) : M ≃ M where
  toFun x := completeBoundedFlow hX hbound x t
  invFun x := completeBoundedFlow hX hbound x (-t)
  left_inv x := completeBoundedFlow_neg_cancel hX hbound x t
  right_inv x := by simpa using completeBoundedFlow_neg_cancel hX hbound x (-t)

/-- Time dependence of each actual orbit is continuous. Joint initial/time
continuity is proved separately from coordinate Picard dependence. -/
theorem continuous_completeBoundedFlow_orbit (x : M) :
    Continuous (completeBoundedFlow hX hbound x) :=
  (completeBoundedFlow_isMIntegralCurve hX hbound x).continuous

end CutoffRigidity
