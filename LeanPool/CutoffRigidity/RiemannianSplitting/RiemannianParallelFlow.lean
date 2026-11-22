/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFields
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldZeroDifferential
public import LeanPool.CutoffRigidity.RiemannianSplitting.CompleteBoundedVectorField
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-! # Complete parallel fields have actual global flows
Metric compatibility and connectedness first prove constant norm. Global
existence then follows from the actual complete bounded-field theorem.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The Gram function of two actual parallel fields is globally constant on a
connected manifold. -/
theorem inner_parallel_eq_of_preconnected
    {X Y : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (T% X)) (hY : ContMDiff I I.tangent 1 (T% Y))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (hpY : ∀ x, CovariantDerivative.leviCivitaConnection I M Y x = 0)
    (x y : M) : inner ℝ (X x) (Y x) = inner ℝ (X y) (Y y) := by
  have hdX := hX.mdifferentiable one_ne_zero
  have hdY := hY.mdifferentiable one_ne_zero
  have hf : MDifferentiable I 𝓘(ℝ, ℝ) (fun z ↦ inner ℝ (X z) (Y z)) :=
    fun z ↦ MDifferentiableAt.inner_bundle (E := TangentSpace I) (hdX z) (hdY z)
  apply eq_of_mvfderiv_eq_zero hf _ x y
  intro z
  ext v
  exact mvfderiv_inner_parallel_eq_zero (CovariantDerivative.leviCivitaConnection I M)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) hdX hdY hpX hpY z v

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- The norm of an actual parallel tangent field is globally constant. -/
theorem norm_parallel_eq_of_preconnected
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (x y : M) : ‖X x‖ = ‖X y‖ := by
  have h := inner_parallel_eq_of_preconnected hX hX hpX hpX x y
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (X x), norm_nonneg (X y)]

/-- Actual parallel fields have globally defined integral curves on a complete
connected Riemannian manifold. -/
theorem exists_global_integralCurve_parallel
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0) (x₀ : M) :
    ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurve γ X := by
  apply exists_global_integralCurve_of_bounded (C := ‖X x₀‖₊) hX
  intro x
  apply eNorm_le_coe.mpr
  exact_mod_cast (norm_parallel_eq_of_preconnected hX hpX x x₀).le

/-- The unit normalization of a nonzero parallel field has actual globally
defined unit-speed integral curves, as used in `lem_rig`. -/
theorem exists_global_integralCurve_unit_parallel
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    ∃ γ : ℝ → M, γ 0 = x₀ ∧
      IsMIntegralCurve γ (‖X x₀‖⁻¹ • X) ∧
      ∀ t, ‖(‖X x₀‖⁻¹ • X) (γ t)‖ = 1 := by
  have hnorm (x : M) : ‖(‖X x₀‖⁻¹ • X) x‖ = 1 := by
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [norm_parallel_eq_of_preconnected hX hpX x x₀,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  obtain ⟨γ, hzero, hγ⟩ := exists_global_integralCurve_of_bounded
    (C := 1) (hX.const_smul_section (a := ‖X x₀‖⁻¹)) (fun x ↦ by
      apply eNorm_le_coe.mpr
      exact_mod_cast (hnorm x).le) x₀
  exact ⟨γ, hzero, hγ, fun t ↦ hnorm (γ t)⟩

/-- The exact flow-line step of `lem_rig`: the unit normalization of a nonzero
parallel gradient has a global flow line, the potential increases at the
constant rate `‖X x₀‖`, and the line meets the zero level exactly once. -/
theorem exists_unit_parallel_gradient_curve_unique_zero
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurve γ (‖X x₀‖⁻¹ • X) ∧
      (∀ t, f (γ t) = f x₀ + ‖X x₀‖ * t) ∧ (∃! t : ℝ, f (γ t) = 0) := by
  obtain ⟨γ, hzero, hγ, _⟩ := exists_global_integralCurve_unit_parallel hX hpX x₀ hne
  have hc : 0 < ‖X x₀‖ := norm_pos_iff.mpr hne
  have hrate (x : M) : mvfderiv I f x ((‖X x₀‖⁻¹ • X) x) = ‖X x₀‖ := by
    simp only [Pi.smul_apply, hgrad, inner_smul_right, real_inner_self_eq_norm_sq]
    rw [norm_parallel_eq_of_preconnected hX hpX x x₀]
    field_simp
  have hlinear (t : ℝ) : f (γ t) = f x₀ + ‖X x₀‖ * t := by
    simpa [hzero] using scalar_integralCurve_eq_add hγ hf hrate t
  refine ⟨γ, hzero, hγ, hlinear, -f x₀ / ‖X x₀‖, ?_, ?_⟩
  · change f (γ (-f x₀ / ‖X x₀‖)) = 0
    rw [hlinear (-f x₀ / ‖X x₀‖)]
    field_simp
    ring
  · intro t ht
    rw [hlinear t] at ht
    apply (eq_div_iff (ne_of_gt hc)).mpr
    linarith

end CutoffRigidity
