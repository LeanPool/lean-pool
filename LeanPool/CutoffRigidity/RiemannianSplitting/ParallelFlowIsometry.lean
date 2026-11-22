/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ParallelFlowTangentMetric
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianTangentIsometry
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFlow

/-! # Actual complete parallel flows are genuine Riemannian isometries
The original tangent metric preservation has been derived from the actual
Levi-Civita parallelism and actual ODE. Genuine path lengths give distance
control, and the genuine inverse flow gives equality of actual distances.
-/

@[expose] public section
open Bundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C)
  (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)

include hpX

/-- Every actual time slice of a complete parallel field's actual flow is an
isometry for the original Riemannian distance. No isometry or tangent-norm
preservation is assumed. -/
theorem isometry_completeBoundedFlow_of_parallel (t : ℝ) :
    Isometry (fun x ↦ completeBoundedFlow hX hbound x t) := by
  intro x y
  have hle := edist_le_of_norm_mfderiv_eq
    (contMDiff_completeBoundedFlow_timeSlice hX hbound t)
    (fun x v ↦ norm_mfderiv_completeBoundedFlow_eq_of_parallel hX hbound hpX x v t) x y
  have hge := edist_le_of_norm_mfderiv_eq
    (contMDiff_completeBoundedFlow_timeSlice hX hbound (-t))
    (fun x v ↦ norm_mfderiv_completeBoundedFlow_eq_of_parallel hX hbound hpX x v (-t))
    (completeBoundedFlow hX hbound x t) (completeBoundedFlow hX hbound y t)
  rw [completeBoundedFlow_neg_cancel, completeBoundedFlow_neg_cancel] at hge
  exact le_antisymm hle hge

/-- The actual parallel flow gives genuine isometry equivalences, whose inverse
is the actual negative-time flow. -/
noncomputable def completeParallelFlowIsometryEquiv (t : ℝ) : M ≃ᵢ M where
  toEquiv := completeBoundedFlowEquiv hX hbound t
  isometry_toFun := isometry_completeBoundedFlow_of_parallel hX hbound hpX t

/-- Connectedness supplies the genuine norm bound, so a source parallel field
has actual isometry flow slices without a separate bounded-field premise. -/
noncomputable def parallelFlowIsometryEquiv [PreconnectedSpace M] (x₀ : M) (t : ℝ) : M ≃ᵢ M :=
  completeParallelFlowIsometryEquiv hX (C := ‖X x₀‖₊) (fun x ↦ by
    apply eNorm_le_coe.mpr
    exact_mod_cast (norm_parallel_eq_of_preconnected hX hpX x x₀).le) hpX t

/-- The unit-normalized nonzero source parallel field has true isometry slices
of its actual complete flow, with every norm/parallelism obligation derived. -/
noncomputable def unitParallelFlowIsometryEquiv [PreconnectedSpace M]
    (x₀ : M) (hne : X x₀ ≠ 0) (t : ℝ) : M ≃ᵢ M := by
  let c := ‖X x₀‖⁻¹
  have hY : ContMDiff I I.tangent 1 (T% (c • X)) := hX.const_smul_section
  have hpY (x : M) : CovariantDerivative.leviCivitaConnection I M (c • X) x = 0 := by
    have hh := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOn.smul_const
        (s := Set.univ)
      c ((hX.mdifferentiable one_ne_zero) x)
    simpa only [hpX x, smul_zero] using hh
  have hYbound (x : M) : ‖(c • X) x‖ₑ ≤ (1 : ℝ≥0) := by
    apply eNorm_le_coe.mpr
    have hn : ‖(c • X) x‖ = 1 := by
      simp only [Pi.smul_apply, norm_smul, c, Real.norm_eq_abs, abs_inv, abs_norm]
      rw [norm_parallel_eq_of_preconnected hX hpX x x₀,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
    exact_mod_cast hn.le
  exact completeParallelFlowIsometryEquiv hY hYbound hpY t

end CutoffRigidity
