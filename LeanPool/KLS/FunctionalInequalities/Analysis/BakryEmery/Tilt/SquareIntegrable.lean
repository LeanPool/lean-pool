/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Tilt averages of square-integrable functions

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 3 and Proposition 7.1: for a probability measure
`μ` with all exponential moments, the tilt average `F_f` of every `f ∈ L²(μ)` is smooth, the Taylor
tensor `T_d f` is linear in `f`, and `f ↦ T_d f` is continuous on `L²(μ)`:
`‖T_d f‖ ≤ C_d ‖f‖_{L²(μ)}` (operator norm of the multilinear map). The derivatives of the
Laplace-type integral `z ↦ ∫ e^{⟪z, x⟫} g(x) dμ(x)` are the weighted moments
`∫ e^{⟪z, x⟫} ⟪x, h₁⟫ ⋯ ⟪x, h_d⟫ g(x) dμ(x)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The derivative amplitude `x ↦ ⟪·, x⟫ • g x` of `w ↦ e^{⟪w, x⟫} g(x)`. -/
def weightedExpD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (x : E) : E →L[ℝ] F :=
  (innerSL ℝ x).smulRight (g x)

section IntegralCalculus

omit [CompleteSpace E]

section NormedSpace

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Measurability of the derivative amplitude. -/
theorem weightedExpD_meas
    {μ : Measure E} {g : E → F} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (weightedExpD g) μ := by
  exact (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp_aestronglyMeasurable
    ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.aestronglyMeasurable.prodMk hg)

private theorem weightedExpD_integrable {μ : Measure E} {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) :
    ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖weightedExpD g x‖) μ := by
  intro r
  refine (hgi (r + 1)).mono' ?_ ?_
  · exact ((by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖))).aestronglyMeasurable).mul
      (weightedExpD_meas hg).norm
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (by positivity)]
    have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
      le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
    calc
      Real.exp (r * ‖x‖) * ‖weightedExpD g x‖ =
          Real.exp (r * ‖x‖) * (‖x‖ * ‖g x‖) := by
        simp [weightedExpD, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      _ ≤ Real.exp (r * ‖x‖) * (Real.exp ‖x‖ * ‖g x‖) := by gcongr
      _ = Real.exp ((r + 1) * ‖x‖) * ‖g x‖ := by
        rw [add_mul, one_mul, Real.exp_add]
        ring

omit [FiniteDimensional ℝ E] in
/-- Integrability of `e^{⟪z, x⟫} g(x)` under integrability against every exponential weight. -/
theorem weightedExp_integrable (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫ • g x) μ := by
  refine (hgi ‖z‖).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable.smul hg
  · filter_upwards [] with x
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    gcongr
    exact real_inner_le_norm z x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise derivative of `w ↦ e^{⟪w, x⟫} g(x)`. -/
theorem weightedExp_hasFDeriv (g : E → F) (x z : E) :
    HasFDerivAt (fun w => Real.exp ⟪w, x⟫ • g x)
      (Real.exp ⟪z, x⟫ • weightedExpD g x) z := by
  have hl : HasFDerivAt (fun w : E => ⟪w, x⟫) (innerSL ℝ x) z := by
    convert (innerSL ℝ x).hasFDerivAt (x := z) using 1
    ext w
    simpa only [innerSL_apply_apply] using (real_inner_comm w x).symm
  convert hl.exp.smul_const (g x) using 1
  ext y
  simp [weightedExpD, ContinuousLinearMap.smulRight_apply, mul_smul]

/-- Differentiation under the integral sign for exponential weights (first derivative): the
derivative of `z ↦ ∫ e^{⟪z, x⟫} g(x) dμ` at `z` is `∫ e^{⟪z, x⟫} (⟪x, ·⟫ g(x)) dμ`. -/
theorem weightedExp_integral_hasFDeriv [CompleteSpace F] (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (z : E) :
    HasFDerivAt (fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • weightedExpD g x ∂μ) z := by
  have hdi := weightedExpD_integrable hg hgi
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun w x => Real.exp ⟪w, x⟫ • g x)
    (F' := fun w x => Real.exp ⟪w, x⟫ • weightedExpD g x)
    (bound := fun x => Real.exp ((‖z‖ + 2) * ‖x‖) * ‖g x‖)
    (Metric.ball_mem_nhds z zero_lt_one)
    ?_ (weightedExp_integrable μ hg hgi z) ?_ ?_ (hgi _) ?_
  · exact Eventually.of_forall fun w => (weightedExp_integrable μ hg hgi w).1
  · exact (weightedExp_integrable μ (weightedExpD_meas hg) hdi z).1
  · filter_upwards with x w hw
    have hd : ‖w - z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have := norm_le_insert' w z
      linarith
    have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
      le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
    calc
      ‖Real.exp ⟪w, x⟫ • weightedExpD g x‖ =
          Real.exp ⟪w, x⟫ * (‖x‖ * ‖g x‖) := by
        simp [weightedExpD, norm_smul, ContinuousLinearMap.norm_smulRight_apply,
          innerSL_apply_norm, Real.norm_of_nonneg (Real.exp_pos _).le]
      _ ≤ Real.exp ((‖z‖ + 1) * ‖x‖) * (Real.exp ‖x‖ * ‖g x‖) := by
        gcongr
        exact (real_inner_le_norm w x).trans
          (mul_le_mul_of_nonneg_right hw' (norm_nonneg _))
      _ = Real.exp ((‖z‖ + 2) * ‖x‖) * ‖g x‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · exact ae_of_all μ (fun x w _ => weightedExp_hasFDeriv g x w)

end NormedSpace

private theorem weightedExp_integral_contDiff_nat.{v} {F : Type (max u v)}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) (n : ℕ) {g : E → F} (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) :
    ContDiff ℝ n (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2
      (fun z => (weightedExp_integral_hasFDeriv μ hg hgi z).continuousAt))
  | succ n IH =>
    apply contDiff_succ_iff_hasFDerivAt.2
    refine ⟨(fun z => ∫ x, Real.exp ⟪z, x⟫ • weightedExpD g x ∂μ), ?_, ?_⟩
    · exact IH (weightedExpD_meas hg) (weightedExpD_integrable hg hgi)
    · exact weightedExp_integral_hasFDeriv μ hg hgi

section NormedSpace

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Differentiation under the integral sign for exponential weights, for integrands integrable
against every exponential weight. -/
theorem contDiff_integral_exp_inner_smul_of_integrable (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) :
    ContDiff ℝ ∞ (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  let L : ULift.{u} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  have hgl : AEStronglyMeasurable (fun x => L.symm (g x)) μ :=
    L.symm.toContinuousLinearEquiv.toContinuousLinearMap.continuous.comp_aestronglyMeasurable hg
  have hgil : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖) * ‖L.symm (g x)‖) μ := by
    simpa only [L.symm.norm_map] using hgi
  have hs := (contDiff_infty.2 (fun n =>
    weightedExp_integral_contDiff_nat μ n hgl hgil)).continuousLinearMap_comp
      L.toContinuousLinearEquiv.toContinuousLinearMap
  have heq :
      (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) =
        (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
    funext z
    change L.toContinuousLinearEquiv.toContinuousLinearMap
      (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ) = _
    rw [← L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (weightedExp_integrable μ hgl hgil z)]
    simp
  change ContDiff ℝ ∞
    (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) at hs
  rwa [heq] at hs

/-- The iterated derivatives of the Laplace-type integral are weighted moments. -/
theorem iteratedFDeriv_integral_exp_inner_smul (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (d : ℕ) (z : E)
    (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) z h =
      ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by
  classical
    induction d generalizing g with
  | zero => simp
  | succ d IH =>
    let N : E → F := fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ
    let a := h (Fin.last d)
    let ev : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F a
    let g' : E → F := fun x => weightedExpD g x a
    have hg' : AEStronglyMeasurable g' μ :=
      ev.continuous.comp_aestronglyMeasurable (weightedExpD_meas hg)
    have hgi' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g' x‖) μ := by
      intro r
      refine ((weightedExpD_integrable hg hgi r).const_mul ‖a‖).mono' ?_ ?_
      · exact
          (by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖))).aestronglyMeasurable.mul
            hg'.norm
      · filter_upwards [] with x
        rw [Real.norm_of_nonneg (by positivity)]
        calc
          Real.exp (r * ‖x‖) * ‖g' x‖ ≤ Real.exp (r * ‖x‖) * (‖weightedExpD g x‖ * ‖a‖) := by
            gcongr
            exact (weightedExpD g x).le_opNorm a
          _ = ‖a‖ * (Real.exp (r * ‖x‖) * ‖weightedExpD g x‖) := by ring
    have hN : ContDiff ℝ ∞ N := contDiff_integral_exp_inner_smul_of_integrable μ hg hgi
    have hfd : fderiv ℝ N = fun w => ∫ x, Real.exp ⟪w, x⟫ • weightedExpD g x ∂μ := by
      funext w
      exact (weightedExp_integral_hasFDeriv μ hg hgi w).fderiv
    have heval : ev ∘ fderiv ℝ N = fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ := by
      funext w
      rw [Function.comp_apply, hfd]
      change (∫ x, Real.exp ⟪w, x⟫ • weightedExpD g x ∂μ) a = _
      rw [ContinuousLinearMap.integral_apply
          (weightedExp_integrable μ (weightedExpD_meas hg) (weightedExpD_integrable hg hgi) w)]
      rfl
    rw [iteratedFDeriv_succ_apply_right]
    change ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) = _
    calc
      ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) =
          iteratedFDeriv ℝ d (ev ∘ fderiv ℝ N) z (Fin.init h) := by
        have hN' : ContDiff ℝ ∞ (fderiv ℝ N) := hN.fderiv_right (by simp)
        have H :=
          ev.iteratedFDeriv_comp_left (hN'.contDiffAt (x := z)) (i := d)
            (by exact_mod_cast le_top (a := (d : ℕ∞)))
        exact (congrArg (fun T => T (Fin.init h)) H).symm
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, Fin.init h j⟫) • g' x ∂μ := by
        rw [heval]
        exact IH hg' hgi' (Fin.init h)
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g', weightedExpD, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
          smul_smul]
        rw [Fin.prod_univ_castSucc]
        simp only [a, Fin.init_def, mul_assoc]

end NormedSpace

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Square-integrable functions are integrable against every exponential weight when `μ` has
all exponential moments. The moment at rate `0` already implies that `μ` is finite. -/
theorem integrable_exp_mul_norm_of_memLp (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ)
    (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖) * ‖f x‖) μ := by
  have hmeas : AEStronglyMeasurable (fun x : E => Real.exp (r * ‖x‖)) μ :=
    (Real.continuous_exp.comp
        (continuous_const.mul
          (continuous_norm : Continuous (fun x : E => ‖x‖)))).aestronglyMeasurable
  have hsquare : Integrable (fun x => (Real.exp (r * ‖x‖)) ^ (2 : ℕ)) μ := by
    convert hexp (2 * r) using 1
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hg : MemLp (fun x : E => Real.exp (r * ‖x‖)) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas).2 hsquare
  have hprod : Integrable ((fun x : E => Real.exp (r * ‖x‖)) * (fun x : E => ‖f x‖)) μ :=
    hg.integrable_mul hf.norm
  have heq :
    (fun x : E => Real.exp (r * ‖x‖)) * (fun x : E => ‖f x‖) =
      (fun x : E => Real.exp (r * ‖x‖) * ‖f x‖) := by
    funext x
    rfl
  exact heq ▸ hprod

omit [FiniteDimensional ℝ E] in
private lemma integrable_exp_inner_of_all_exp (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
  have hmeas : AEStronglyMeasurable (fun x : E => Real.exp ⟪z, x⟫) μ :=
    (Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ‖Real.exp ⟪z, x⟫‖ ≤ Real.exp (‖z‖ * ‖x‖) := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact le_trans (le_abs_self _) (abs_real_inner_le_norm z x)
  exact (hexp ‖z‖).mono' hmeas hbound

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `F_f(z) · ∫ e^{⟪z,x⟫} dμ = ∫ e^{⟪z,x⟫} f(x) dμ` whenever `∫ e^{⟪z,x⟫} dμ ≠ 0`. -/
theorem tiltAverage_mul_integral_exp (μ : Measure E) (f : E → ℝ) (z : E)
    (hz : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0) :
    tiltAverage μ f z * ∫ x, Real.exp ⟪z, x⟫ ∂μ = ∫ x, Real.exp ⟪z, x⟫ * f x ∂μ := by
    rw [tiltAverage, expTilt, integral_tilted]
    simp only [smul_eq_mul]
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div]
    exact div_mul_cancel₀ _ hz

/-- Tilt averages of square-integrable functions are smooth. -/
theorem contDiff_tiltAverage_of_memLp (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ) :
    ContDiff ℝ ∞ (tiltAverage μ f) := by
    let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ
    let D : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
    have hN : ContDiff ℝ ∞ N := by
      dsimp [N]
      exact contDiff_integral_exp_inner_smul_of_integrable
        (μ := μ) (g := f) hf.aestronglyMeasurable
        (fun r => integrable_exp_mul_norm_of_memLp μ hexp hf r)
    have hD : ContDiff ℝ ∞ D := by
      dsimp [D]
      exact contDiff_integral_exp_inner_smul_of_integrable
        (μ := μ) (g := (1 : E → ℝ))
        stronglyMeasurable_const.aestronglyMeasurable
        (fun r => by simpa using hexp r)
    have hDpos : ∀ z : E, 0 < D z := by
      intro z
      dsimp [D]
      simpa using
        (integral_exp_pos (μ := μ) (f := fun x : E => ⟪z, x⟫)
          (hf := integrable_exp_inner_of_all_exp μ hexp z))
    have hDinv : ContDiff ℝ ∞ (fun z => (D z)⁻¹) :=
      hD.inv (fun z => ne_of_gt (hDpos z))
    have hmul : ContDiff ℝ ∞ (fun z => (D z)⁻¹ * N z) := by
      convert hDinv.smul hN using 1
    have htilt : tiltAverage μ f = (fun z => (D z)⁻¹ * N z) := by
      funext z
      simp only [tiltAverage, MeasureTheory.integral_tilted, expTilt, D, N,
        div_eq_mul_inv, smul_eq_mul]
      have hden :
          (∫ x : E, Real.exp ⟪z, x⟫ * 1 ∂μ) =
            ∫ x : E, Real.exp ⟪z, x⟫ ∂μ := by
        simp
      rw [hden]
      calc
        ∫ x : E, Real.exp ⟪z, x⟫ *
            (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ * f x ∂μ =
            ∫ x : E, (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ •
              (Real.exp ⟪z, x⟫ * f x) ∂μ := by
                apply integral_congr_ae
                filter_upwards with x
                simp only [smul_eq_mul]
                ring
        _ = (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ •
            ∫ x : E, Real.exp ⟪z, x⟫ * f x ∂μ := by
              rw [integral_smul]
        _ = (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ *
            ∫ x : E, Real.exp ⟪z, x⟫ * f x ∂μ := by
              simp [smul_eq_mul]
    rw [htilt]
    exact hmul

/-- `T_d` is additive on `L²(μ)`. -/
theorem taylorTensor_add (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f g : E → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (d : ℕ) :
    taylorTensor μ (fun x => f x + g x) d = taylorTensor μ f d + taylorTensor μ g d := by
  have hint : ∀ φ : E → ℝ, MemLp φ 2 μ → ∀ z : E, Integrable φ (expTilt μ z) := by
    intro φ hφ z
    have hc : Continuous fun x : E => Real.exp ⟪z, x⟫ := by fun_prop
    have hez : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
      refine (hexp ‖z‖).mono' hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (real_inner_le_norm z x)
    unfold expTilt
    rw [integrable_tilted_iff hez]
    refine (integrable_exp_mul_norm_of_memLp μ hexp hφ ‖z‖).mono'
      (hc.aestronglyMeasurable.mul hφ.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
    exact real_inner_le_norm z x
  have hsum : tiltAverage μ (fun x => f x + g x) = tiltAverage μ f + tiltAverage μ g := by
    funext z
    simp only [tiltAverage, Pi.add_apply]
    exact integral_add (hint f hf z) (hint g hg z)
  unfold taylorTensor
  rw [hsum, iteratedFDeriv_add_apply
    ((contDiff_tiltAverage_of_memLp μ hexp hf).contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiff_tiltAverage_of_memLp μ hexp hg).contDiffAt.of_le (by exact_mod_cast le_top)),
    smul_add]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `T_d` is homogeneous. -/
theorem taylorTensor_const_mul (μ : Measure E) (c : ℝ) (f : E → ℝ) (d : ℕ) :
    taylorTensor μ (fun x => c * f x) d = c • taylorTensor μ f d := by
  have hT : tiltAverage μ (fun x => c * f x) = fun z => c * tiltAverage μ f z := by
    funext z
    simp only [tiltAverage]
    exact integral_const_mul c _
  unfold taylorTensor
  rw [hT]
  by_cases hc : c = 0
  · subst hc
    ext h
    simp
  · have key := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := ℝ) (f := tiltAverage μ f)
      (x := 0) (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)) (i := d)
    have hfun : (⇑(ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)) ∘ tiltAverage μ f) =
        fun z => c * tiltAverage μ f z := by
      funext z
      simp [ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
    rw [hfun] at key
    ext h
    rw [smul_apply, key, smul_apply,
      smul_apply]
    simp [ContinuousLinearEquiv.unitsEquivAut_apply, smul_eq_mul]
    ring

section NormWeights

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem tiltExp_memLp_two (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (r : ℝ) :
    MemLp (fun x => Real.exp (r * ‖x‖)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖))).aestronglyMeasurable).2
  convert hexp (2 * r) using 1
  funext x
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem tiltExp_cauchy_schwarz (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f : E → ℝ} (hf : MemLp f 2 μ) (r : ℝ) :
    (∫ x, Real.exp (r * ‖x‖) * ‖f x‖ ∂μ) ≤
      (eLpNorm (fun x => Real.exp (r * ‖x‖)) 2 μ).toReal * (eLpNorm f 2 μ).toReal := by
  have hw := tiltExp_memLp_two μ hexp r
  have heq :
      (∫ x, Real.exp (r * ‖x‖) * ‖f x‖ ∂μ) =
        ⟪hw.toLp (fun x => Real.exp (r * ‖x‖)), hf.norm.toLp (fun x => ‖f x‖)⟫ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, hf.norm.coeFn_toLp] with x hx hfx
    rw [hx, hfx]
    simp [mul_comm]
  rw [heq]
  calc
    ⟪hw.toLp (fun x => Real.exp (r * ‖x‖)), hf.norm.toLp (fun x => ‖f x‖)⟫ ≤
        ‖hw.toLp (fun x => Real.exp (r * ‖x‖))‖ *
          ‖hf.norm.toLp (fun x => ‖f x‖)‖ := real_inner_le_norm _ _
    _ = _ := by rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable]

end NormWeights

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem tiltMoment_product_bound (d : ℕ) (h : Fin d → E) (x : E) :
    ‖∏ j, ⟪x, h j⟫‖ ≤ Real.exp ((d : ℝ) * ‖x‖) * ∏ j, ‖h j‖ := by
  classical
  have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
    le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
  calc
    ‖∏ j, ⟪x, h j⟫‖ = ∏ j, ‖⟪x, h j⟫‖ := norm_prod _ _
    _ ≤ ∏ j, (Real.exp ‖x‖ * ‖h j‖) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact (norm_inner_le_norm x (h j)).trans
          (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    _ = Real.exp ((d : ℝ) * ‖x‖) * ∏ j, ‖h j‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_nat_mul]

private theorem tiltNumerator_deriv_bound (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f : E → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) 0‖ ≤
      (eLpNorm (fun x => Real.exp ((d : ℝ) * ‖x‖)) 2 μ).toReal *
        (eLpNorm f 2 μ).toReal := by
  classical
  have hgi := integrable_exp_mul_norm_of_memLp μ hexp hf
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro h
  rw [iteratedFDeriv_integral_exp_inner_smul μ hf.aestronglyMeasurable hgi d 0 h]
  simp only [inner_zero_left, Real.exp_zero, one_mul, smul_eq_mul]
  calc
    ‖∫ x, (∏ j, ⟪x, h j⟫) * f x ∂μ‖ ≤
        ∫ x, (Real.exp ((d : ℝ) * ‖x‖) * ‖f x‖) * (∏ j, ‖h j‖) ∂μ := by
      apply norm_integral_le_of_norm_le ((hgi d).mul_const _)
      filter_upwards [] with x
      rw [norm_mul]
      calc
        ‖∏ j, ⟪x, h j⟫‖ * ‖f x‖ ≤
            (Real.exp ((d : ℝ) * ‖x‖) * ∏ j, ‖h j‖) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right (tiltMoment_product_bound d h x) (norm_nonneg _)
        _ = _ := by ring
    _ = (∫ x, Real.exp ((d : ℝ) * ‖x‖) * ‖f x‖ ∂μ) * ∏ j, ‖h j‖ := by
      rw [integral_mul_const]
    _ ≤ ((eLpNorm (fun x => Real.exp ((d : ℝ) * ‖x‖)) 2 μ).toReal *
        (eLpNorm f 2 μ).toReal) * ∏ j, ‖h j‖ :=
      mul_le_mul_of_nonneg_right (tiltExp_cauchy_schwarz μ hexp hf d)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- **Continuity of `T_d` on `L²(μ)`**: for a probability measure with all exponential moments,
`‖T_d f‖ ≤ C_d ‖f‖_{L²(μ)}` for every `f ∈ L²(μ)`. -/
theorem exists_norm_taylorTensor_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ → ‖taylorTensor μ f d‖ ≤ C * (eLpNorm f 2 μ).toReal := by
  classical
  let D : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ
  let A : E → ℝ := fun z => (D z)⁻¹
  let B : ℕ → ℝ := fun j => (eLpNorm (fun x : E => Real.exp ((j : ℝ) * ‖x‖)) 2 μ).toReal
  have hD : ContDiff ℝ ∞ D := by
    simpa [D] using contDiff_integral_exp_inner_smul μ hexp
      (g := fun _ : E => (1 : ℝ)) measurable_const.aestronglyMeasurable
      (M := 1) (k := 0) (by intro x; simp)
  have hDi (z : E) : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
    refine (hexp ‖z‖).mono' ?_ ?_
    · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
  have hA : ContDiff ℝ ∞ A :=
    hD.inv (fun z => (integral_exp_pos (hDi z)).ne')
  let C : ℝ := ‖(d.factorial : ℝ)⁻¹‖ *
    ∑ i ∈ Finset.range (d + 1),
      (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i A 0‖ * B (d - i)
  refine ⟨C, ?_⟩
  intro f hf
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ
  have hN : ContDiff ℝ ∞ N :=
    contDiff_integral_exp_inner_smul_of_integrable μ hf.aestronglyMeasurable
      (integrable_exp_mul_norm_of_memLp μ hexp hf)
  have hformula : tiltAverage μ f = fun z => A z * N z := by
    funext z
    rw [tiltAverage, expTilt, integral_tilted]
    change (∫ x, (Real.exp ⟪z, x⟫ / D z) • f x ∂μ) = A z * N z
    simp_rw [div_eq_mul_inv, mul_comm (Real.exp ⟪z, _⟫), mul_smul]
    rw [integral_smul]
    rfl
  calc
    ‖taylorTensor μ f d‖ =
        ‖(d.factorial : ℝ)⁻¹‖ * ‖iteratedFDeriv ℝ d (fun z => A z * N z) 0‖ := by
      rw [taylorTensor, norm_smul, hformula]
    _ ≤ ‖(d.factorial : ℝ)⁻¹‖ *
        ∑ i ∈ Finset.range (d + 1),
          (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i A 0‖ *
            ‖iteratedFDeriv ℝ (d - i) N 0‖ := by
      gcongr
      exact norm_iteratedFDeriv_mul_le hA hN 0
        (n := d) (by exact_mod_cast le_top (a := (d : ℕ∞)))
    _ ≤ ‖(d.factorial : ℝ)⁻¹‖ *
        ∑ i ∈ Finset.range (d + 1),
          (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i A 0‖ *
            (B (d - i) * (eLpNorm f 2 μ).toReal) := by
      gcongr with i hi
      exact tiltNumerator_deriv_bound μ hexp hf (d - i)
    _ = C * (eLpNorm f 2 μ).toReal := by
      dsimp [C]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, mul_assoc]

/-- **Continuity of `T_d` on `L²(μ)` in the Hilbert–Schmidt norm** of the coefficient array (the
norm of BKL (29)), for a probability measure with all exponential moments. -/
theorem exists_norm_coordTensor_taylorTensor_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ →
      ‖coordTensor b (taylorTensor μ f d)‖ ≤ C * (eLpNorm f 2 μ).toReal := by
    obtain ⟨C, hC⟩ := exists_norm_taylorTensor_le μ hexp d
    refine ⟨(Real.sqrt n) ^ d * C, ?_⟩
    intro f hf
    calc
      ‖coordTensor b (taylorTensor μ f d)‖
          ≤ (Real.sqrt n) ^ d * ‖taylorTensor μ f d‖ :=
        norm_coordTensor_le b (taylorTensor μ f d)
      _ ≤ (Real.sqrt n) ^ d * (C * (eLpNorm f 2 μ).toReal) :=
        mul_le_mul_of_nonneg_left (hC f hf) (by positivity)
      _ = ((Real.sqrt n) ^ d * C) * (eLpNorm f 2 μ).toReal := by
        rw [mul_assoc]

end IntegralCalculus

/-! ### Tilt averages of `L²` classes -/

section Lp

section ScalarLp

omit [CompleteSpace E] [FiniteDimensional ℝ E]

section NormedSpace

variable {G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]

section CompleteSpace

variable [CompleteSpace G]

omit [BorelSpace E]
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)

/-- Taylor tensors only see the `μ`-class of a function. -/
theorem taylorTensor_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    taylorTensor μ f d = taylorTensor μ g d := by
  unfold taylorTensor
  rw [show tiltAverage μ f = tiltAverage μ g from funext (tiltAverage_congr_ae μ hfg)]

end CompleteSpace

/-- With all exponential moments, `e^{⟪z, ·⟫} ∈ L²(μ)`. -/
theorem memLp_exp_inner (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    MemLp (fun x => Real.exp ⟪z, x⟫) 2 μ := by
  have hc : Continuous fun x : E => Real.exp ⟪z, x⟫ := by fun_prop
  refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 ?_
  refine (hexp (2 * ‖z‖)).mono' (hc.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have := real_inner_le_norm z x
  push_cast
  nlinarith

/-- Square-integrable functions are integrable against every exponential tilt of a finite measure
with all exponential moments. -/
theorem integrable_expTilt_of_memLp
    (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → G}
    (hg : MemLp g 2 μ) (z : E) : Integrable g (expTilt μ z) := by
  have hc : Continuous fun x : E => Real.exp ⟪z, x⟫ := by fun_prop
  have hez : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
    refine (hexp ‖z‖).mono' hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (real_inner_le_norm z x)
  unfold expTilt
  rw [integrable_tilted_iff hez]
  refine (integrable_exp_mul_norm_of_memLp μ hexp hg.norm ‖z‖).mono'
    (hc.aestronglyMeasurable.smul hg.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_norm]
  gcongr
  exact real_inner_le_norm z x

end NormedSpace

/-- The tilt average of a class `g ∈ L²(μ)` at `z` is `(∫ e^{⟪z, x⟫} dμ)⁻¹ ⟪e^{⟪z, ·⟫}, g⟫`. -/
theorem tiltAverage_Lp_eq_inner (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (g : Lp ℝ 2 μ) (z : E) :
    tiltAverage μ (⇑g) z =
      (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ * ⟪(memLp_exp_inner μ hexp z).toLp _, g⟫ := by
  rw [tiltAverage, expTilt, integral_tilted, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(memLp_exp_inner μ hexp z).coeFn_toLp] with x hx
  rw [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial, div_eq_mul_inv]
  ring

/-- For fixed `z`, `g ↦ F_g(z)` is continuous on `L²(μ)`. -/
theorem continuous_tiltAverage_Lp (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Continuous fun g : Lp ℝ 2 μ => tiltAverage μ (⇑g) z := by
  simp_rw [tiltAverage_Lp_eq_inner μ hexp _ z]
  exact continuous_const.mul (continuous_const.inner continuous_id)

end ScalarLp

omit [FiniteDimensional ℝ E] in
/-- Pairing the tilt average of a vector class `G ∈ L²(μ; E)` with `w` is the tilt average of the
scalar class `⟪w, G⟫`. -/
theorem inner_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) (w z : E) :
    ⟪w, tiltAverage μ (⇑G) z⟫ = tiltAverage μ (⇑((innerSL ℝ w).compLpL 2 μ G)) z := by
  rw [tiltAverage_congr_ae μ ((innerSL ℝ w).coeFn_compLpL G) z]
  unfold tiltAverage
  simp only [innerSL_apply_apply]
  exact (integral_inner (integrable_expTilt_of_memLp μ hexp (Lp.memLp G) z) w).symm

/-- The tilt average of a vector class `G ∈ L²(μ; E)` is smooth. -/
theorem contDiff_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) :
    ContDiff ℝ ∞ (tiltAverage μ (⇑G)) := by
  let b := stdOrthonormalBasis ℝ E
  have h : tiltAverage μ (⇑G) =
      fun z => ∑ i, tiltAverage μ (⇑((innerSL ℝ (b i)).compLpL 2 μ G)) z • b i := by
    funext z
    simp_rw [← inner_tiltAverage_Lp μ hexp G _ z]
    exact (b.sum_repr' _).symm
  rw [h]
  exact ContDiff.sum fun i _ =>
    (contDiff_tiltAverage_of_memLp μ hexp (Lp.memLp _)).smul contDiff_const

end Lp

end FunctionalInequalities.Analysis.BakryEmery
