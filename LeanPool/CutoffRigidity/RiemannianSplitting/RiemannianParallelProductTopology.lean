/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteFlowLevelProduct
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFlow

/-! # The genuine parallel-gradient topological product
The source parallelism and gradient equations supply every premise of the
actual canonical-flow construction. The resulting product is a homeomorphism;
its Riemannian isometry and the level manifold structure remain separate.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
  {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
  (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
include hX hpX

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The true uniform norm bound of the unit-normalized actual parallel field. -/
theorem unitParallelField_enorm_le_one (x₀ : M) (hne : X x₀ ≠ 0) (x : M) :
    ‖(‖X x₀‖⁻¹ • X) x‖ₑ ≤ (1 : ℝ≥0) := by
  apply eNorm_le_coe.mpr
  have hnorm : ‖(‖X x₀‖⁻¹ • X) x‖ = 1 := by
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [norm_parallel_eq_of_preconnected hX hpX x x₀,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  exact_mod_cast hnorm.le

include hgrad in
omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The actual potential has constant directional rate along its normalized
parallel gradient; the rate is derived from metric compatibility. -/
theorem unitParallelGradient_rate (x₀ : M) (hne : X x₀ ≠ 0) (x : M) :
    mvfderiv I f x ((‖X x₀‖⁻¹ • X) x) = ‖X x₀‖ := by
  simp only [Pi.smul_apply, hgrad, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [norm_parallel_eq_of_preconnected hX hpX x x₀]
  have hc : 0 < ‖X x₀‖ := norm_pos_iff.mpr hne
  field_simp

/-- The actual global normalized parallel-gradient flow constructs a genuine
homeomorphism from the real line times the actual zero level onto the manifold.
No splitting, flow existence, or flow continuity is a premise. -/
noncomputable def unitParallelGradientLevelHomeomorph (x₀ : M) (hne : X x₀ ≠ 0) :
    (ℝ × {y : M // f y = 0}) ≃ₜ M :=
  completeFlowLevelHomeomorph (hX.const_smul_section (a := ‖X x₀‖⁻¹))
    (unitParallelField_enorm_le_one hX hpX x₀ hne) hf
    (unitParallelGradient_rate hX hpX hgrad x₀ hne) (norm_pos_iff.mpr hne)

/-- In the constructed product, the original potential is exactly linear in
the real coordinate, with the source normalization. -/
theorem unitParallelGradientLevelHomeomorph_scalar
    (x₀ : M) (hne : X x₀ ≠ 0) (p : ℝ × {y : M // f y = 0}) :
    f (unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne p) = ‖X x₀‖ * p.1 :=
  completeFlowLevelHomeomorph_scalar (hX.const_smul_section (a := ‖X x₀‖⁻¹))
    (unitParallelField_enorm_le_one hX hpX x₀ hne) hf
    (unitParallelGradient_rate hX hpX hgrad x₀ hne) (norm_pos_iff.mpr hne) p

end CutoffRigidity
