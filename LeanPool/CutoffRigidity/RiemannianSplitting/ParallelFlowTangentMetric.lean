/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ParallelFlowInfinitesimalMetric
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Actual parallel flows preserve the original tangent metric globally
The actual group law and actual manifold derivative chain rule propagate the
proved time-zero Gram derivative to every time. The ordinary mean value theorem
then gives genuine metric preservation, without an isometry premise.
-/

@[expose] public section
open Bundle Set Filter Function
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

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x] in
/-- The actual group law yields the actual tangent Gram composition law. -/
theorem completeBoundedFlow_gram_add
    (x : M) (u v : TangentSpace I x) (s t : ℝ) :
    inner ℝ ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y (s + t)) x) u)
      ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y (s + t)) x) v) =
    inner ℝ
      ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y s)
        (completeBoundedFlow hX hbound x t))
        ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x) u))
      ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y s)
        (completeBoundedFlow hX hbound x t))
        ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x) v)) := by
  have hmap : (fun y ↦ completeBoundedFlow hX hbound y (s + t)) =ᶠ[𝓝 x]
      ((fun y ↦ completeBoundedFlow hX hbound y s) ∘
        (fun y ↦ completeBoundedFlow hX hbound y t)) :=
    Filter.Eventually.of_forall (fun y ↦ completeBoundedFlow_add hX hbound y t s)
  rw [inner_mfderiv_eq_of_eventuallyEq hmap u v]
  have hs := (contMDiff_completeBoundedFlow_timeSlice hX hbound s).mdifferentiable one_ne_zero
  have ht := (contMDiff_completeBoundedFlow_timeSlice hX hbound t).mdifferentiable one_ne_zero
  rw [mfderiv_comp x (hs _) (ht _)]
  rfl

/-- Every actual time slice of the actual parallel flow preserves the original
Riemannian tangent inner product. -/
theorem inner_mfderiv_completeBoundedFlow_eq_of_parallel
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (x : M) (u v : TangentSpace I x) (t : ℝ) :
    inner ℝ ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x) u)
      ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x) v) = inner ℝ u v := by
  let q : ℝ → ℝ := fun s ↦ inner ℝ
    ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y s) x) u)
    ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y s) x) v)
  have hD (s : ℝ) : HasDerivAt q 0 s := by
    let uₛ := (mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y s) x) u
    let vₛ := (mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y s) x) v
    have hzero := hasDerivAt_completeBoundedFlow_gram_zero_of_parallel
      hX hbound hpX (completeBoundedFlow hX hbound x s) uₛ vₛ
    have hzero' := hzero.comp_of_eq s ((hasDerivAt_id s).sub_const s) (by simp)
    simp only [zero_mul] at hzero'
    apply hzero'.congr_of_eventuallyEq
    filter_upwards [] with r
    have heq := completeBoundedFlow_gram_add hX hbound x u v (r - s) s
    change q (r - s + s) = _ at heq
    exact (congrArg q (sub_add_cancel r s)).symm.trans heq
  have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hD s).differentiableAt)
    (fun s ↦ (hD s).deriv) t 0
  have hzeroGerm : (fun y ↦ completeBoundedFlow hX hbound y 0) =ᶠ[𝓝 x] (id : M → M) :=
    Filter.Eventually.of_forall (fun y ↦ completeBoundedFlow_zero hX hbound y)
  have hzeroGram := inner_mfderiv_eq_of_eventuallyEq hzeroGerm u v
  change q t = inner ℝ u v
  rw [hconst]
  rw [mfderiv_id] at hzeroGram
  convert! hzeroGram using 1

/-- Actual tangent norms are preserved by every actual parallel flow slice. -/
theorem norm_mfderiv_completeBoundedFlow_eq_of_parallel
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (x : M) (u : TangentSpace I x) (t : ℝ) :
    ‖(mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x) u‖ = ‖u‖ := by
  have h := inner_mfderiv_completeBoundedFlow_eq_of_parallel hX hbound hpX x u u t
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg ((mfderiv I I (fun y ↦ completeBoundedFlow hX hbound y t) x) u),
    norm_nonneg u]

end CutoffRigidity
