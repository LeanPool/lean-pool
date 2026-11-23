/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedFlow

/-! # The complete flow of a smooth bounded field is `C^∞` jointly in point and time
-/

@[expose] public section
open Bundle
open scoped Manifold ContDiff NNReal ENNReal

namespace CutoffRigidity.Riemann
open CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX1 : ContMDiff I I.tangent 1 (T% X))
  (hXinf : ContMDiff I I.tangent ∞ (T% X))
  {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)

include hXinf in
/-- The complete flow of a smooth bounded field is jointly `C^∞` in the initial point and time. -/
theorem contMDiff_completeBoundedFlow_joint_infty :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : M × ℝ ↦ completeBoundedFlow hX1 hbound p.1 p.2) := by
  exact (TauCeti.contMDiff_globalFlow_uncurry (isCompleteVectorField_of_bounded hX1 hbound)
    (by simp : 1 ≤ (⊤ : ℕ∞)) hXinf).comp
      (contMDiff_snd.prodMk contMDiff_fst : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod I) ∞ (fun p : M × ℝ ↦ (p.2, p.1)))

end CutoffRigidity.Riemann
