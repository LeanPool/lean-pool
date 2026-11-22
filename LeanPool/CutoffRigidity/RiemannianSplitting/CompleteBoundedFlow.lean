/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedVectorField
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow

/-! # Global flow of a bounded field on a complete Riemannian manifold -/

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

include hX hbound in
/-- A bounded `C¹` field on a complete Riemannian manifold is complete. -/
theorem isCompleteVectorField_of_bounded : TauCeti.IsCompleteVectorField X :=
  TauCeti.isCompleteVectorField_of_forall_exists_isMIntegralCurve
    (exists_global_integralCurve_of_bounded hX hbound)

/-- The canonical flow of a bounded `C¹` field on a complete manifold. -/
noncomputable def completeBoundedFlow (x : M) (t : ℝ) : M :=
  TauCeti.globalFlow X hX (isCompleteVectorField_of_bounded hX hbound) t x

theorem completeBoundedFlow_zero (x : M) : completeBoundedFlow hX hbound x 0 = x :=
  (TauCeti.globalFlow X hX (isCompleteVectorField_of_bounded hX hbound)).map_zero_apply x

theorem completeBoundedFlow_isMIntegralCurve (x : M) :
    IsMIntegralCurve (completeBoundedFlow hX hbound x) X :=
  TauCeti.isMIntegralCurve_globalFlow hX (isCompleteVectorField_of_bounded hX hbound) x

theorem completeBoundedFlow_add (x : M) (s t : ℝ) :
    completeBoundedFlow hX hbound x (t + s) =
      completeBoundedFlow hX hbound (completeBoundedFlow hX hbound x s) t :=
  (TauCeti.globalFlow X hX (isCompleteVectorField_of_bounded hX hbound)).map_add t s x

theorem completeBoundedFlow_neg_cancel (x : M) (t : ℝ) :
    completeBoundedFlow hX hbound (completeBoundedFlow hX hbound x t) (-t) = x := by
  rw [← completeBoundedFlow_add, neg_add_cancel, completeBoundedFlow_zero]

end CutoffRigidity
