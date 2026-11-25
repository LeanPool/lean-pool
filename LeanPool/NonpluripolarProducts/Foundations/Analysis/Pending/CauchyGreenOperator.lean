/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CauchyPompeiu
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WirtingerCalculus
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Cauchy–Green operator in a complex direction, with parameters

For a finite-dimensional complex normed space `E`, a nonzero direction `v`, and
a smooth compactly supported `g : E → ℂ`, put
`T_v g (x) = (1/π) ∫_ℂ g(x - w v) / w dA(w)`.
Then `T_v g` is smooth, every real directional derivative commutes with `T_v`,
and the Wirtinger derivative of `T_v g` in the complex line `ℂ v` is `g`.
All other variables of `E` are parameters of the one-variable operator.
-/

@[expose] public section

open MeasureTheory Set Filter Complex Metric
open scoped Topology Real ContDiff

namespace SGPT.Foundations.Analysis.Pending.CauchyGreen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The Cauchy–Green operator along the complex line spanned by `v`. -/
def cauchyGreen (v : E) (g : E → ℂ) (x : E) : ℂ :=
  (π : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ • g (x - w • v)

omit [FiniteDimensional ℂ E] in
/-- A compactly supported function vanishes along `x - w v` for large `w`,
uniformly for `x` near a given point. -/
theorem exists_radius_notMem_tsupport {G : Type*} [NormedAddCommGroup G]
    {h : E → G} (hc : HasCompactSupport h) {v : E} (hv : v ≠ 0) (x₀ : E) :
    ∃ K > 0, ∀ x ∈ closedBall x₀ 1, ∀ w : ℂ, K < ‖w‖ → x - w • v ∉ tsupport h := by
  obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨(|M| + ‖x₀‖ + 1) / ‖v‖ + 1, by positivity, fun x hx w hw hmem ↦ ?_⟩
  have h1 := hM hmem
  rw [mem_closedBall, dist_zero_right] at h1
  rw [mem_closedBall, dist_eq_norm] at hx
  have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' x x₀
    linarith
  have htri : ‖w • v‖ ≤ ‖x - w • v‖ + ‖x‖ := by
    have := norm_sub_norm_le (w • v) x
    rw [← norm_neg (w • v - x), neg_sub] at this
    linarith [norm_le_insert' (w • v) x, norm_sub_rev x (w • v)]
  rw [norm_smul] at htri
  have hK : (|M| + ‖x₀‖ + 1) < ‖w‖ * ‖v‖ := by
    have := mul_lt_mul_of_pos_right hw hvpos
    rw [add_mul, div_mul_cancel₀ _ hvpos.ne'] at this
    linarith
  linarith [le_abs_self M]

/-- The locally integrable dominating function `C ‖w‖⁻¹` on a ball. -/
theorem integrable_indicator_inv_norm (C K : ℝ) :
    Integrable ((ball (0 : ℂ) K).indicator fun w ↦ C * ‖w‖⁻¹) := by
  rw [integrable_indicator_iff measurableSet_ball]
  refine Integrable.const_mul ?_ C
  refine integrableOn_ball_of_norm_le_rpow (E := ℂ) (C := 1) (α := 1)
    (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex])
    (Eventually.of_forall fun w ↦ ?_) measurable_norm.inv.aestronglyMeasurable
  simp [Real.rpow_neg_one]

omit [FiniteDimensional ℂ E] in
/-- The Cauchy–Green integrand of a continuous compactly supported function is
integrable on `ℂ`. -/
theorem integrable_inv_smul_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {h : E → G} (hh : Continuous h) (hc : HasCompactSupport h) {v : E} (hv : v ≠ 0)
    (x : E) : Integrable (fun w : ℂ ↦ w⁻¹ • h (x - w • v)) := by
  obtain ⟨K, -, hK⟩ := exists_radius_notMem_tsupport hc hv x
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hh
  have hmeas : AEStronglyMeasurable (fun w : ℂ ↦ w⁻¹ • h (x - w • v)) :=
    measurable_inv.aestronglyMeasurable.smul
      (hh.comp (continuous_const.sub (continuous_id.smul continuous_const))).aestronglyMeasurable
  refine (integrable_indicator_inv_norm C (K + 1)).mono' hmeas (Eventually.of_forall fun w ↦ ?_)
  by_cases hw : ‖w‖ < K + 1
  · rw [indicator_of_mem (by simpa using hw), norm_smul, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (inv_nonneg.mpr (norm_nonneg w))
  · have hzero : h (x - w • v) = 0 :=
      image_eq_zero_of_notMem_tsupport (hK x (mem_closedBall_self zero_le_one) w (by linarith))
    rw [indicator_of_notMem (by simpa using hw), hzero, smul_zero, norm_zero]

omit [FiniteDimensional ℂ E] in
/-- Differentiation of the Cauchy–Green integral under the integral sign. -/
theorem hasFDerivAt_integral_inv_smul_comp {g : E → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) {v : E} (hv : v ≠ 0) (x₀ : E) :
    HasFDerivAt (fun x ↦ ∫ w : ℂ, w⁻¹ • g (x - w • v))
      (∫ w : ℂ, w⁻¹ • fderiv ℝ g (x₀ - w • v)) x₀ := by
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hDs : HasCompactSupport (fderiv ℝ g) := hc.fderiv ℝ
  obtain ⟨K, -, hK⟩ := exists_radius_notMem_tsupport hDs hv x₀
  obtain ⟨C, hC⟩ := hDs.exists_bound_of_continuous hDc
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x w ↦ w⁻¹ • fderiv ℝ g (x - w • v)) (ball_mem_nhds x₀ zero_lt_one)
    (Eventually.of_forall fun x ↦
      (integrable_inv_smul_comp hg.continuous hc hv x).aestronglyMeasurable)
    (integrable_inv_smul_comp hg.continuous hc hv x₀)
    (integrable_inv_smul_comp hDc hDs hv x₀).aestronglyMeasurable
    (bound := (ball (0 : ℂ) (K + 1)).indicator fun w ↦ C * ‖w‖⁻¹)
    (Eventually.of_forall fun w x hx ↦ ?_) (integrable_indicator_inv_norm C (K + 1))
    (Eventually.of_forall fun w x _ ↦ ?_)
  · by_cases hw : ‖w‖ < K + 1
    · rw [indicator_of_mem (by simpa using hw), norm_smul, norm_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (inv_nonneg.mpr (norm_nonneg w))
    · have hzero : fderiv ℝ g (x - w • v) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (hK x (ball_subset_closedBall hx) w (by linarith))
      rw [indicator_of_notMem (by simpa using hw), hzero]
      simp
  · have hcomp : HasFDerivAt (fun y ↦ g (y - w • v)) (fderiv ℝ g (x - w • v)) x := by
      have := ((hg.differentiable one_ne_zero) (x - w • v)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const (w • v))
      simp only [ContinuousLinearMap.comp_id] at this
      exact this
    exact hcomp.const_smul w⁻¹

omit [FiniteDimensional ℂ E] in
theorem hasFDerivAt_cauchyGreen {g : E → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) {v : E} (hv : v ≠ 0) (x : E) :
    HasFDerivAt (cauchyGreen v g)
      ((π : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • fderiv ℝ g (x - w • v)) x :=
  (hasFDerivAt_integral_inv_smul_comp hg hc hv x).const_mul _

omit [FiniteDimensional ℂ E] in
/-- Real directional derivatives commute with the Cauchy–Green operator. -/
theorem fderiv_cauchyGreen_apply {g : E → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) {v : E} (hv : v ≠ 0) (x u : E) :
    fderiv ℝ (cauchyGreen v g) x u = cauchyGreen v (fun y ↦ fderiv ℝ g y u) x := by
  rw [(hasFDerivAt_cauchyGreen hg hc hv x).fderiv, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.integral_apply
      (integrable_inv_smul_comp (hg.continuous_fderiv one_ne_zero) (hc.fderiv ℝ) hv x)]
  simp [cauchyGreen]

omit [FiniteDimensional ℂ E] in
theorem hasCompactSupport_fderiv_apply {g : E → ℂ} (hc : HasCompactSupport g) (u : E) :
    HasCompactSupport (fun y ↦ fderiv ℝ g y u) :=
  (hc.fderiv ℝ).mono fun y hy h ↦ hy (by simp [h])

/-- The Cauchy–Green operator maps smooth compactly supported functions to
smooth functions. -/
theorem contDiff_cauchyGreen {g : E → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) {v : E} (hv : v ≠ 0) :
    ContDiff ℝ ∞ (cauchyGreen v g) := by
  rw [contDiff_infty]
  intro m
  induction m generalizing g with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x ↦
      (hasFDerivAt_cauchyGreen (hg.of_le (by simp)) hc hv x).continuousAt)
  | succ m ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x ↦ (hasFDerivAt_cauchyGreen (hg.of_le (by simp)) hc hv x).differentiableAt,
      fun h ↦ absurd h (by simp), fun u ↦ ?_⟩
    have heq : (fun x ↦ fderiv ℝ (cauchyGreen v g) x u) =
        cauchyGreen v (fun y ↦ fderiv ℝ g y u) :=
      funext fun x ↦ fderiv_cauchyGreen_apply (hg.of_le (by simp)) hc hv x u
    rw [heq]
    exact ih ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
      (hasCompactSupport_fderiv_apply hc u)

omit [FiniteDimensional ℂ E] in
/-- **Cauchy–Green inversion.**  The Wirtinger derivative of `T_v g` along the
complex line of `v` is `g`. -/
theorem dbarDir_cauchyGreen {g : E → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) {v : E} (hv : v ≠ 0) (x : E) :
    dbarDir v (cauchyGreen v g) x = g x := by
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hint (u : E) := integrable_inv_smul_comp (hDc.clm_apply continuous_const)
    (hasCompactSupport_fderiv_apply hc u) hv x
  let φ : ℂ → ℂ := fun w ↦ g (x - w • v)
  have hφderiv (w : ℂ) : HasFDerivAt φ
      (-((fderiv ℝ g (x - w • v)).comp ((ContinuousLinearMap.id ℝ ℂ).smulRight v))) w := by
    have hlin : HasFDerivAt (fun w : ℂ ↦ x - w • v)
        (-((ContinuousLinearMap.id ℝ ℂ).smulRight v)) w :=
      ((ContinuousLinearMap.id ℝ ℂ).smulRight v).hasFDerivAt.const_sub x
    have := ((hg.differentiable one_ne_zero) (x - w • v)).hasFDerivAt.comp w hlin
    rw [ContinuousLinearMap.comp_neg] at this
    exact this
  have hφ : ContDiff ℝ 1 φ := hg.comp (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have hφc : HasCompactSupport φ := by
    obtain ⟨K, -, hK⟩ := exists_radius_notMem_tsupport hc hv x
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) K) fun w hw ↦ ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hw
    change g (x - w • v) = 0
    exact image_eq_zero_of_notMem_tsupport (hK x (mem_closedBall_self zero_le_one) w hw)
  have hdbar (w : ℂ) : dbar φ w = -dbarDir v g (x - w • v) := by
    simp only [dbar, dbarDir, wirt, (hφderiv w).fderiv]
    simp
    ring
  have hP := integral_inv_mul_dbar hφ hφc
  simp_rw [hdbar, mul_neg, integral_neg] at hP
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hval : ∫ w : ℂ, w⁻¹ * dbarDir v g (x - w • v) = π * g x := by
    have := neg_inj.mp (hP.trans (neg_mul _ _))
    simpa [φ] using this
  set A := ∫ w : ℂ, w⁻¹ • fderiv ℝ g (x - w • v) v
  set B := ∫ w : ℂ, w⁻¹ • fderiv ℝ g (x - w • v) (I • v)
  have hAB : ∫ w : ℂ, w⁻¹ * dbarDir v g (x - w • v) = (A + I * B) / 2 := by
    rw [← integral_const_mul I, ← integral_add (hint v) ((hint _).const_mul I),
      ← integral_div]
    congr 1
    funext w
    simp only [dbarDir, wirt, smul_eq_mul]
    ring
  have key : A + I * B = 2 * (π * g x) := by
    rw [← hval, hAB]
    ring
  simp only [dbarDir, wirt, fderiv_cauchyGreen_apply hg hc hv, cauchyGreen]
  calc ((π : ℂ)⁻¹ * A + I * ((π : ℂ)⁻¹ * B)) / 2 = (π : ℂ)⁻¹ * (A + I * B) / 2 := by ring
    _ = g x := by
      rw [key]
      field_simp

end

end SGPT.Foundations.Analysis.Pending.CauchyGreen
