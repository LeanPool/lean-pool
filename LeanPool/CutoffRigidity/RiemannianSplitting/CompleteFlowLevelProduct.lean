/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedFlowContinuity
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFields

/-! # The actual flow and its zero-level cross section form a topological product
The scalar coordinate is derived by the actual manifold chain rule. The inverse
uses the actual negative-time flow to reach the zero level. This constructs a
homeomorphism; it does not yet assert the Riemannian isometry needed later.
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
  {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
  {c : ℝ} (hc : ∀ x, mvfderiv I f x (X x) = c)
include hf hc

/-- The actual scalar coordinate along the canonical flow is linear. -/
theorem completeBoundedFlow_scalar_eq (x : M) (t : ℝ) :
    f (completeBoundedFlow hX hbound x t) = f x + c * t := by
  simpa [completeBoundedFlow_zero] using scalar_integralCurve_eq_add
    (completeBoundedFlow_isMIntegralCurve hX hbound x) hf hc t

/-- Following the actual flow backwards to the unique zero-level intersection. -/
noncomputable def completeFlowZeroProjection (hpos : 0 < c) (x : M) : {y : M // f y = 0} :=
  ⟨completeBoundedFlow hX hbound x (-f x / c), by
    rw [completeBoundedFlow_scalar_eq hX hbound hf hc]
    field_simp
    ring⟩

/-- The actual bounded-field flow constructs a topological product with the
actual zero level when the potential has positive constant directional rate. -/
noncomputable def completeFlowLevelHomeomorph (hpos : 0 < c) :
    (ℝ × {y : M // f y = 0}) ≃ₜ M where
  toFun p := completeBoundedFlow hX hbound p.2.val p.1
  invFun x := (f x / c, completeFlowZeroProjection hX hbound hf hc hpos x)
  left_inv p := by
    apply Prod.ext
    · change f (completeBoundedFlow hX hbound p.2.val p.1) / c = p.1
      rw [completeBoundedFlow_scalar_eq hX hbound hf hc, p.2.property]
      field_simp
      ring
    · apply Subtype.ext
      change completeBoundedFlow hX hbound
        (completeBoundedFlow hX hbound p.2.val p.1)
        (-f (completeBoundedFlow hX hbound p.2.val p.1) / c) = p.2.val
      rw [completeBoundedFlow_scalar_eq hX hbound hf hc, p.2.property]
      have htime : -(0 + c * p.1) / c = -p.1 := by field_simp; ring
      rw [htime, completeBoundedFlow_neg_cancel]
  right_inv x := by
    change completeBoundedFlow hX hbound
      (completeBoundedFlow hX hbound x (-f x / c)) (f x / c) = x
    rw [← completeBoundedFlow_add]
    have htime : f x / c + -f x / c = 0 := by ring
    rw [htime, completeBoundedFlow_zero]
  continuous_toFun := (continuous_completeBoundedFlow hX hbound).comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact hf.continuous.div_const c
    · apply Continuous.subtype_mk
      exact (continuous_completeBoundedFlow hX hbound).comp
        (continuous_id.prodMk ((hf.continuous.neg).div_const c))

/-- The constructed product coordinate agrees with the actual potential. -/
theorem completeFlowLevelHomeomorph_scalar (hpos : 0 < c)
    (p : ℝ × {y : M // f y = 0}) :
    f (completeFlowLevelHomeomorph hX hbound hf hc hpos p) = c * p.1 := by
  change f (completeBoundedFlow hX hbound p.2.val p.1) = c * p.1
  rw [completeBoundedFlow_scalar_eq hX hbound hf hc, p.2.property, zero_add]

end CutoffRigidity
