/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EigenfunctionCaccioppoli
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual directional difference quotients on compact sets

C¹ Banach-valued functions have locally uniformly bounded directional
difference quotients. The explicit sequence of positive steps tends to zero,
and the quotients converge to the actual directional derivative.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- An explicit positive step sequence for compact difference-quotient tests. -/
@[expose] noncomputable def differenceStep (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem differenceStep_pos (n : ℕ) : 0 < differenceStep n := by
  unfold differenceStep
  positivity

theorem differenceStep_le_one (n : ℕ) : differenceStep n ≤ 1 := by
  unfold differenceStep
  apply (inv_le_one₀ (by positivity : (0 : ℝ) < n + 1)).2
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem differenceStep_tendsto_zero : Tendsto differenceStep atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact tendsto_inv_atTop_zero.comp hden

/-- Genuine finite difference in a fixed direction. -/
@[expose] noncomputable def directionalDifferenceQuotient
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E → F) (v : E) (h : ℝ) (x : E) : F :=
  h⁻¹ • (G (x + h • v) - G x)

/-- Pointwise convergence of the explicit difference quotients to the
actual Fréchet directional derivative. -/
theorem directionalDifferenceQuotient_tendsto
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : E → F} (hG : Differentiable ℝ G) (v x : E) :
    Tendsto (fun n => directionalDifferenceQuotient G v (differenceStep n) x)
      atTop (𝓝 (fderiv ℝ G x v)) := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hder : HasDerivAt (fun t : ℝ => G (x + t • v)) (fderiv ℝ G x v) 0 := by
    exact (hG x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hstep : Tendsto differenceStep atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨differenceStep_tendsto_zero,
      Filter.Eventually.of_forall (fun n => differenceStep_pos n)⟩
  have hh := hder.tendsto_slope_zero_right.comp hstep
  simpa only [directionalDifferenceQuotient, Function.comp_def, zero_add, zero_smul,
    add_zero] using hh

/-- The actual C¹ derivative bounds all directional difference quotients
uniformly on a given compact set, for steps in `(0,1]`. -/
theorem directionalDifferenceQuotient_bounded_on_compact
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : E → F} (hG : ContDiff ℝ 1 G) (v : E) {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖directionalDifferenceQuotient G v h x‖ ≤ M := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous
    (fun x : E => x)).continuousOn
  let B := Metric.closedBall (0 : E) (max R 0 + ‖v‖)
  have hB : IsCompact B := isCompact_closedBall _ _
  have hDG : Continuous (fderiv ℝ G) :=
    (hG.fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨C, hC⟩ := hB.exists_bound_of_continuousOn hDG.continuousOn
  refine ⟨max C 0 * ‖v‖, mul_nonneg (le_max_right _ _) (norm_nonneg _), ?_⟩
  intro x hx h hh0 hh1
  have hRx : ‖x‖ ≤ R := by simpa using hR x hx
  have hxB : x ∈ B := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hRx.trans (by linarith [norm_nonneg v, le_max_left R 0])
  have hyB : x + h • v ∈ B := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ ‖x‖ + ‖h • v‖ := norm_add_le _ _
      _ = ‖x‖ + h * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh0]
      _ ≤ max R 0 + ‖v‖ := by nlinarith [hRx, le_max_left R 0, norm_nonneg v]
  have hLip := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ B) => ((hG.differentiable (by norm_num)) y))
    (fun y hy => (hC y hy).trans (le_max_left C 0)) (convex_closedBall (0 : E) _) hxB hyB
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh0] at hLip
  unfold directionalDifferenceQuotient
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh0]
  calc
    _ ≤ h⁻¹ * (max C 0 * (h * ‖v‖)) := mul_le_mul_of_nonneg_left hLip (inv_nonneg.mpr hh0.le)
    _ = _ := by field_simp

/-- The actual gradient of a C² function is C¹, via the actual Riesz map. -/
theorem contDiff_gradient_of_c2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (gradient f) := by
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.contDiff.comp (hf.fderiv_right (m := 1) (by norm_num))

/-- Spatial regularity of a scalar difference quotient, for each fixed step. -/
theorem contDiff_directionalDifferenceQuotient {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (v : E) (h : ℝ) :
    ContDiff ℝ 2 (directionalDifferenceQuotient f v h) := by
  unfold directionalDifferenceQuotient
  fun_prop

/-- The actual gradient commutes with a finite directional difference. -/
theorem gradient_directionalDifferenceQuotient {f : E → ℝ}
    (hf : Differentiable ℝ f) (v : E) (h : ℝ) (x : E) :
    gradient (directionalDifferenceQuotient f v h) x =
      directionalDifferenceQuotient (gradient f) v h x := by
  have ht := ((hf (x + h • v)).hasFDerivAt).comp x ((hasFDerivAt_id x).add_const (h • v))
  have hd := (ht.sub (hf x).hasFDerivAt).const_smul (h⁻¹)
  have hder : HasFDerivAt (directionalDifferenceQuotient f v h)
      (h⁻¹ • (fderiv ℝ f (x + h • v) - fderiv ℝ f x)) x := by
    unfold directionalDifferenceQuotient
    simpa only [Function.comp_def,
      ContinuousLinearMap.comp_id, Pi.sub_def, Pi.smul_def, id_eq] using hd
  have hg := hder.hasGradientAt.gradient
  change gradient (directionalDifferenceQuotient f v h) x =
    (InnerProductSpace.toDual ℝ E).symm (h⁻¹ • (fderiv ℝ f (x + h • v) - fderiv ℝ f x)) at hg
  simp only [map_smul, map_sub] at hg
  exact hg

/-- Bilinear form of the derivative of the actual gradient. -/
theorem inner_fderiv_gradient_apply_pair {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    inner ℝ (fderiv ℝ (gradient f) x v) w = fderiv ℝ (fderiv ℝ f) x v w := by
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hder : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have heq : gradient f = fun y => R (fderiv ℝ f y) := rfl
  rw [heq, fderiv_fun_comp x R.differentiableAt hder, R.fderiv]
  change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x v)) w = _
  exact InnerProductSpace.toDual_symm_apply

/-- At C² regularity the derivative of the gradient in coordinate i is the
actual gradient of the coordinate derivative, by Hessian symmetry. -/
theorem fderiv_gradient_coordinate {f : E → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin d) (x : E) :
    fderiv ℝ (gradient f) x (EuclideanSpace.single i 1) = gradient (coordinateDerivative i f) x
      := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  apply ext_inner_right ℝ
  intro w
  rw [inner_fderiv_gradient_apply_pair hf, inner_gradient_left]
  unfold coordinateDerivative
  rw [second_fderiv_apply_const hd]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- The coordinate difference quotients converge in actual gradient at each
point under only C² regularity of the original function. -/
theorem gradient_directionalDifferenceQuotient_tendsto {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (i : Fin d) (x : E) :
    Tendsto (fun n => gradient
      (directionalDifferenceQuotient f (EuclideanSpace.single i 1) (differenceStep n)) x)
      atTop (𝓝 (gradient (coordinateDerivative i f) x)) := by
  have h := directionalDifferenceQuotient_tendsto
    ((contDiff_gradient_of_c2 hf).differentiable (by norm_num)) (EuclideanSpace.single i 1) x
  rw [fderiv_gradient_coordinate hf i x] at h
  simpa only [gradient_directionalDifferenceQuotient (hf.differentiable (by norm_num))] using h

end CutoffRigidity
