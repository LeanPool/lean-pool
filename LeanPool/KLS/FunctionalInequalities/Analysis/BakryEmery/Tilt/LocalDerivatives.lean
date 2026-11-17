/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Norm
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Local
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Local all-order derivatives of exponentially weighted integrals

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: inside a single
exponential radius `r` (integrability of `e^{t‖x‖}‖g(x)‖` for `t < r`), the function
`z ↦ ∫ e^{⟪z,x⟫} g(x) dμ` has all derivatives given by the moment tensors `∫ e^{⟪z,x⟫} ∏⟪x,h_j⟫ g
dμ`
for `‖z‖ < r`; at `z = 0` the Laplace transform of a probability law has `D^d L_μ(0)(h) = ∫ ∏⟪x,h_j⟫
dμ`
with operator norm at most the norm moment `∫ ‖x‖^d dμ`. This extends the one-radius calculus of
`Tilt.Local` (it must not import the Borell moment module, which depends on this family).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section WeightedIntegrals

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
/-- Inside the exponential radius the weighted integrand `e^{⟪z,x⟫} g(x)` is integrable. -/
theorem integrable_exp_inner_smul_of_lt (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ)
    {z : E} (hz : ‖z‖ < r) : Integrable (fun x => Real.exp ⟪z, x⟫ • g x) μ := by
  refine (hgi ‖z‖ hz).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable.smul hg
  · filter_upwards [] with x
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    gcongr
    exact real_inner_le_norm z x

/--
**All-order derivatives of `z ↦ ∫ e^{⟪z,x⟫} g(x) dμ` inside the exponential radius**: for `‖z‖ < r`,
`D^d(…)(z)(h) = ∫ e^{⟪z,x⟫} ∏_j ⟪x, h_j⟫ g(x) dμ`, given `∫ e^{t‖x‖}‖g‖ < ∞` for all `t < r`. -/
theorem iteratedFDeriv_weightedExp_integral_of_lt [CompleteSpace F] (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {r : ℝ}
    (hgi : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ) (d : ℕ) (z : E)
    (hz : ‖z‖ < r) (h : Fin d → E) :
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
    have hgi' : ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g' x‖) μ := by
      intro t htr
      refine ((weightedExpD_integrable_lt hg hgi t htr).const_mul ‖a‖).mono' ?_ ?_
      · exact
          (by fun_prop : Continuous (fun x : E => Real.exp (t * ‖x‖))).aestronglyMeasurable.mul
            hg'.norm
      · filter_upwards [] with x
        rw [Real.norm_of_nonneg (by positivity)]
        calc
          Real.exp (t * ‖x‖) * ‖g' x‖ ≤ Real.exp (t * ‖x‖) * (‖weightedExpD g x‖ * ‖a‖) := by
            gcongr
            exact (weightedExpD g x).le_opNorm a
          _ = ‖a‖ * (Real.exp (t * ‖x‖) * ‖weightedExpD g x‖) := by ring
    have hzmem : z ∈ Metric.ball (0 : E) r := by simpa using hz
    have hball : Metric.ball (0 : E) r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hzmem
    have hN : ContDiffAt ℝ ∞ N z := (weighted_integral_contDiffOn μ hg hgi).contDiffAt hball
    have heval : ev ∘ fderiv ℝ N =ᶠ[𝓝 z] fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ := by
      filter_upwards [hball] with w hw
      have hw' : ‖w‖ < r := by simpa using hw
      rw [Function.comp_apply, (weightedExp_integral_hasFDerivAt_of_lt μ hg hgi hw').fderiv]
      change (∫ x, Real.exp ⟪w, x⟫ • weightedExpD g x ∂μ) a = _
      rw [ContinuousLinearMap.integral_apply
          (integrable_exp_inner_smul_of_lt μ (weightedExpD_meas hg)
            (weightedExpD_integrable_lt hg hgi) hw')]
      rfl
    have hevalD :
      iteratedFDeriv ℝ d (ev ∘ fderiv ℝ N) z =
        iteratedFDeriv ℝ d (fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ) z := by
      have heval' : ev ∘ fderiv ℝ N =ᶠ[𝓝[Set.univ] z] fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ := by
        simpa using heval
      simpa only [iteratedFDerivWithin_univ] using
        heval'.iteratedFDerivWithin_eq heval.self_of_nhds d
    rw [iteratedFDeriv_succ_apply_right]
    change ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) = _
    calc
      ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) =
          iteratedFDeriv ℝ d (ev ∘ fderiv ℝ N) z (Fin.init h) := by
        have hN' : ContDiffAt ℝ ∞ (fderiv ℝ N) z := hN.fderiv_right (by simp)
        have H :=
          ev.iteratedFDeriv_comp_left hN' (i := d) (by exact_mod_cast le_top (a := (d : ℕ∞)))
        exact (congrArg (fun T => T (Fin.init h)) H).symm
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, Fin.init h j⟫) • g' x ∂μ := by
        rw [hevalD]
        exact IH hg' hgi' (Fin.init h)
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g', weightedExpD, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
          smul_smul]
        rw [Fin.prod_univ_castSucc]
        simp only [a, Fin.init_def, mul_assoc]

end WeightedIntegrals

/-- The `d`-th derivative of the Laplace transform at `0` is the degree-`d` moment tensor
`h ↦ ∫ ∏_j ⟪x, h_j⟫ dμ`, given one exponential moment `∫ e^{r‖x‖} dμ < ∞`. -/
theorem iteratedFDeriv_laplace_zero (μ : Measure E)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (d : ℕ) (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) 0 h =
      ∫ x, ∏ j, ⟪x, h j⟫ ∂μ := by
  have hgi : ∀ t < r, Integrable (fun x : E => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
    intro t ht
    refine hexp.mono' (by fun_prop) ?_
    filter_upwards [] with x
    simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ht.le (norm_nonneg x))
  simpa only [smul_eq_mul, mul_one, inner_zero_left, Real.exp_zero, one_mul] using
    iteratedFDeriv_weightedExp_integral_of_lt μ measurable_const.aestronglyMeasurable hgi d 0
      (by simpa using hr) h


/-- `‖D^d L_μ(0)‖ ≤ ∫ ‖x‖^d dμ` (operator norm; `d = 0` gives `1`). -/
theorem norm_iteratedFDeriv_laplace_zero_le (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ}
    (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) 0‖ ≤ ∫ x, ‖x‖ ^ d ∂μ := by
  have hm : Integrable (fun x : E => ‖x‖ ^ d) μ :=
    FunctionalInequalities.Probability.integrable_norm_pow_of_exp μ hr hexp d
  apply
    ContinuousMultilinearMap.opNorm_le_bound
      (integral_nonneg fun x => pow_nonneg (norm_nonneg x) d)
  intro h
  rw [iteratedFDeriv_laplace_zero μ hr hexp d h]
  have hpi : Integrable (fun x : E => ∏ j, ⟪x, h j⟫) μ :=
    (hm.mul_const (∏ j, ‖h j‖)).mono' (by fun_prop)
      (ae_of_all _ fun x => FunctionalInequalities.Analysis.Tensor.norm_prod_inner_le d h x)
  calc
    ‖∫ x, ∏ j, ⟪x, h j⟫ ∂μ‖ ≤ ∫ x, ‖∏ j, ⟪x, h j⟫‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂μ :=
      integral_mono hpi.norm (hm.mul_const _)
        (fun x => FunctionalInequalities.Analysis.Tensor.norm_prod_inner_le d h x)
    _ = (∫ x, ‖x‖ ^ d ∂μ) * ∏ j, ‖h j‖ := integral_mul_const _ _

/-- **The first Taylor tensor is the centered first moment**: for `f ∈ L²(μ)`,
`T_1 f (w) = ∫ ⟪w, x⟫ f(x) dμ − (∫ f dμ) ∫ ⟪w, x⟫ dμ` (BKL p. 30, the `d = 1` coefficient). -/
theorem taylorTensor_one_apply (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) (w : E) :
    taylorTensor μ f 1 (fun _ => w) =
      (∫ x, ⟪w, x⟫ * f x ∂μ) - (∫ x, f x ∂μ) * ∫ x, ⟪w, x⟫ ∂μ := by
    let A : E → ℝ := tiltAverage μ f
    let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ
    let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ
    have hint (z : E) : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
      exact (hexp ‖z‖).mono' (by fun_prop) (by
        filter_upwards [] with x
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (real_inner_le_norm z x))
    have hprod : (fun z => A z * Z z) = N := by
      funext z
      simpa [A, Z, N, smul_eq_mul] using
        (tiltAverage_mul_integral_exp μ f z
          (integral_exp_pos (hint z)).ne')
    have hA : ContDiff ℝ ∞ A := by
      simpa [A] using (contDiff_tiltAverage_of_memLp μ hexp hf)
    have hZ : ContDiff ℝ ∞ Z := by
      simpa [Z, smul_eq_mul, mul_one] using
        (contDiff_integral_exp_inner_smul_of_integrable μ
          (g := fun _ : E => (1 : ℝ))
          (Measurable.aestronglyMeasurable measurable_const)
          (by simpa using hexp))
    have hN : ContDiff ℝ ∞ N := by
      simpa [N, smul_eq_mul] using
        (contDiff_integral_exp_inner_smul_of_integrable μ
          (g := f) hf.aestronglyMeasurable
          (integrable_exp_mul_norm_of_memLp μ hexp hf))
    have hA' : DifferentiableAt ℝ A 0 := hA.differentiable (by simp) 0
    have hZ' : DifferentiableAt ℝ Z 0 := hZ.differentiable (by simp) 0
    have hfun : (A * Z : E → ℝ) = (fun z => A z * Z z) := by
      funext z
      rfl
    have hprod' :
        fderiv ℝ N 0 =
          A 0 • fderiv ℝ Z 0 + Z 0 • fderiv ℝ A 0 := by
      calc
        fderiv ℝ N 0 =
            fderiv ℝ (fun z => A z * Z z) 0 := by
              rw [hprod]
        _ = A 0 • fderiv ℝ Z 0 + Z 0 • fderiv ℝ A 0 := by
          rw [← hfun]
          exact (hA'.hasFDerivAt.mul hZ'.hasFDerivAt).fderiv
    have hprodw :
        fderiv ℝ N 0 w =
          A 0 * fderiv ℝ Z 0 w + Z 0 * fderiv ℝ A 0 w := by
      simpa only [add_apply, smul_apply, smul_eq_mul] using
        congrArg (fun L : E →L[ℝ] ℝ => L w) hprod'
    have hZw :
        fderiv ℝ Z 0 w = ∫ x, ⟪w, x⟫ ∂μ := by
      calc
        fderiv ℝ Z 0 w =
            iteratedFDeriv ℝ 1 Z 0 (fun _ => w) := by
              rw [iteratedFDeriv_one_apply]
        _ = ∫ x, ⟪w, x⟫ ∂μ := by
          dsimp [Z]
          simpa [real_inner_comm] using
            (iteratedFDeriv_laplace_zero μ (by norm_num : (0 : ℝ) < 1)
              (hexp 1) 1 (fun _ => w))
    have hgi :
        ∀ t : ℝ, t < 1 →
          Integrable (fun x => Real.exp (t * ‖x‖) * ‖f x‖) μ :=
      fun t _ => integrable_exp_mul_norm_of_memLp μ hexp hf t
    have hNw :
        fderiv ℝ N 0 w = ∫ x, ⟪w, x⟫ * f x ∂μ := by
      calc
        fderiv ℝ N 0 w =
            iteratedFDeriv ℝ 1 N 0 (fun _ => w) := by
              rw [iteratedFDeriv_one_apply]
        _ = ∫ x, (Real.exp ⟪0, x⟫ *
                ∏ j : Fin 1, ⟪x, w⟫) • f x ∂μ := by
          dsimp [N]
          exact iteratedFDeriv_weightedExp_integral_of_lt μ
            (g := f) hf.aestronglyMeasurable hgi 1 0 (by simp) (fun _ => w)
        _ = ∫ x, ⟪w, x⟫ * f x ∂μ := by
          simp [smul_eq_mul, real_inner_comm]
    have hA0 : A 0 = ∫ x, f x ∂μ := by
      simp [A, tiltAverage, expTilt]
    have hZ0 : Z 0 = 1 := by
      simp [Z]
    simp only [taylorTensor, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
    rw [iteratedFDeriv_one_apply]
    change fderiv ℝ A 0 w =
      (∫ x, ⟪w, x⟫ * f x ∂μ) -
        (∫ x, f x ∂μ) * ∫ x, ⟪w, x⟫ ∂μ
    rw [hNw, hA0, hZ0, hZw] at hprodw
    linarith

end FunctionalInequalities.Analysis.BakryEmery
