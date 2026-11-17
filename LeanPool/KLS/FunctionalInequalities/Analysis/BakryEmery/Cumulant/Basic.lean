/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Norm
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Local
public import Mathlib.Probability.Moments.Variance

/-!
# The logarithmic Laplace transform and cumulant tensors

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 4 and the linear step of Proposition 7.1. For a
nonzero finite measure `μ` with all exponential moments, `Λ_μ(z) = log ∫ e^{⟪z, x⟫} dμ(x)` is
smooth,
the tilt average of a linear function is a directional derivative, `F_{⟪v,·⟫}(z) = DΛ_μ(z) v`, and
the Taylor tensors of linear functions are cumulant tensors,
`T_d ⟪v, ·⟫ = κ_{d+1}(v, ·, …, ·) / d!` with `κ_m = ∇^m Λ_μ(0)`.

The third cumulant of a centered law is its third moment. Conditionally on the quadratic-form
estimate of Letwin (2026, Theorem 1.2), stated as the explicit premise `LetwinQuadraticBound`, a
centered isotropic probability law with all exponential moments satisfies `R^μ_3 ≤ 8 Id`
(BKL Lemma 4.2 in that conditional, restricted form; the Letwin estimate is not proved here).

Cumulants of order `k ≥ 2` transform along affine maps `x ↦ T(x − a)` through the adjoint of `T`
(`cumulant_map_affine`, BKL (77)).

`LetwinQuadraticBound` is closed under convergence of mixed moments of degree at most four
(`letwinQuadraticBound_of_tendsto_moments`, Letwin arXiv:2607.24164v1, last sentence of Lemma A.1).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The logarithmic Laplace transform `Λ_μ(z) = log ∫ e^{⟪z, x⟫} dμ(x)` (BKL Section 4). -/
def logLaplace (μ : Measure E) (z : E) : ℝ :=
  Real.log (∫ x, Real.exp ⟪z, x⟫ ∂μ)

/-- The cumulant tensor `κ_m^μ = ∇^m Λ_μ(0)` (BKL Section 4), as a continuous `m`-linear form. -/
def cumulant (μ : Measure E) (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  iteratedFDeriv ℝ n (logLaplace μ) 0

section LaplaceCalculus

omit [CompleteSpace E]

/-- The logarithmic Laplace transform is smooth for a nonzero measure with all exponential
moments. -/
theorem contDiff_logLaplace (μ : Measure E) [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiff ℝ ∞ (logLaplace μ) := by
    have hZ : ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := by
      simpa [smul_eq_mul, mul_one] using
        (contDiff_integral_exp_inner_smul μ hexp
          (g := fun _ : E => (1 : ℝ))
          (M := 1) (k := 0)
          (hg := measurable_const.aestronglyMeasurable)
          (hgb := by
            intro x
            simp))
    have hpos : ∀ z : E, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
      intro z
      have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
        refine (hexp ‖z‖).mono' ?_ ?_
        · exact
            (Real.continuous_exp.comp
              (continuous_const.inner continuous_id)).aestronglyMeasurable
        · filter_upwards [] with x
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
      exact integral_exp_pos hzint
    change ContDiff ℝ ∞
      (fun z : E => Real.log (∫ x, Real.exp ⟪z, x⟫ ∂μ))
    exact hZ.log (fun z => (hpos z).ne')

omit [FiniteDimensional ℝ E] in
private lemma bkl_integrable_exp_inner (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
  refine (hexp ‖z‖).mono'
    ((continuous_const.inner continuous_id).rexp.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (real_inner_le_norm z x)

private lemma bkl_hasFDerivAt_laplace (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    HasFDerivAt (fun y => ∫ x, Real.exp ⟪y, x⟫ ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • innerSL ℝ x ∂μ) z := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y x => Real.exp ⟪y, x⟫)
    (F' := fun y x => Real.exp ⟪y, x⟫ • innerSL ℝ x)
    (s := Metric.ball z 1)
    (bound := fun x => Real.exp ((‖z‖ + 2) * ‖x‖))
    (Metric.ball_mem_nhds z zero_lt_one) ?_
    (bkl_integrable_exp_inner μ hexp z) ?_ ?_
    (hexp (‖z‖ + 2)) ?_
  · exact Filter.Eventually.of_forall fun y =>
      (continuous_const.inner continuous_id).rexp.aestronglyMeasurable
  · exact ((continuous_const.inner continuous_id).rexp.smul
      (innerSL ℝ).continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x y hy => by
      have hy' : ‖y‖ ≤ ‖z‖ + 1 := by
        have hdist : ‖y - z‖ < 1 := by
          simpa [dist_eq_norm] using hy
        calc
          ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
            simpa [add_comm, norm_sub_rev] using norm_le_norm_add_norm_sub z y
          _ ≤ ‖z‖ + 1 := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        innerSL_apply_norm]
      calc
        Real.exp ⟪y, x⟫ * ‖x‖ ≤
            Real.exp ((‖z‖ + 1) * ‖x‖) * Real.exp ‖x‖ := by
          exact mul_le_mul
            (Real.exp_le_exp.mpr
              ((real_inner_le_norm y x).trans
                (mul_le_mul_of_nonneg_right hy' (norm_nonneg x))))
            (le_trans (by linarith : ‖x‖ ≤ ‖x‖ + 1)
              (Real.add_one_le_exp ‖x‖))
            (norm_nonneg x) (Real.exp_pos _).le
        _ = Real.exp ((‖z‖ + 2) * ‖x‖) := by
          rw [← Real.exp_add]
          congr 1
          ring
  · exact Filter.Eventually.of_forall fun x y _ => by
      simpa only [innerSL_apply_apply, real_inner_comm] using
        (innerSL ℝ x).hasFDerivAt.exp

/-- The tilt average of a linear function is a derivative of `Λ_μ`: `F_ℓ(z) = ⟪v, ∇Λ_μ(z)⟫` for
`ℓ = ⟪v, ·⟫` (proof of BKL Proposition 7.1). -/
theorem tiltAverage_inner_eq_fderiv_logLaplace (μ : Measure E) [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v z : E) :
    tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v := by
  have hi := bkl_integrable_exp_inner μ hexp z
  have hd := bkl_hasFDerivAt_laplace μ hexp z
  have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 := (integral_exp_pos hi).ne'
  have hlog := hd.log hp
  change tiltAverage μ (fun x => ⟪v, x⟫) z =
    fderiv ℝ (fun y => Real.log (∫ x, Real.exp ⟪y, x⟫ ∂μ)) z v
  rw [hlog.fderiv]
  change (∫ x, ⟪v, x⟫ ∂(μ.tilted fun x => ⟪z, x⟫)) =
    (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ *
      (∫ x, Real.exp ⟪z, x⟫ • innerSL ℝ x ∂μ) v
  rw [integral_tilted]
  have hdi : Integrable (fun x => Real.exp ⟪z, x⟫ • innerSL ℝ x) μ := by
    refine (hexp (‖z‖ + 1)).mono' ?_ ?_
    · exact ((continuous_const.inner continuous_id).rexp.smul
        (innerSL ℝ).continuous).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          innerSL_apply_norm]
        calc
          Real.exp ⟪z, x⟫ * ‖x‖ ≤
              Real.exp (‖z‖ * ‖x‖) * Real.exp ‖x‖ :=
            mul_le_mul
              (Real.exp_le_exp.mpr (real_inner_le_norm z x))
              (le_trans (by linarith : ‖x‖ ≤ ‖x‖ + 1)
                (Real.add_one_le_exp ‖x‖))
              (norm_nonneg x) (Real.exp_pos _).le
          _ = Real.exp ((‖z‖ + 1) * ‖x‖) := by
            rw [← Real.exp_add]
            congr 1
            ring
  rw [ContinuousLinearMap.integral_apply hdi]
  simp_rw [smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_comm,
    div_eq_mul_inv]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- **Local tilt-average/derivative identity**: `F_{⟪v,·⟫}(z) = ∂_v Λ_μ(z)` for `‖z‖ < r`, assuming
only the single exponential moment `∫ e^{r‖x‖} dμ < ∞`. -/
theorem tiltAverage_inner_eq_fderiv_logLaplace_of_lt (μ : Measure E) [NeZero μ]
    {r : ℝ} (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) {z : E} (hz : ‖z‖ < r) (v : E) :
    tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v := by
      let g : E → ℝ := fun _ => 1
      have hg : AEStronglyMeasurable g μ := by
        exact aestronglyMeasurable_const
      have hr : 0 ≤ r := by
        linarith [norm_nonneg z]
      have hgi :
          ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ := by
        intro t ht
        apply hexp.mono' (by fun_prop)
        filter_upwards with x
        simp only [g, norm_one, mul_one]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        by_cases h : 0 ≤ t
        · apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (le_of_lt ht) (norm_nonneg x)
        · have htx : t * ‖x‖ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (norm_nonneg x)
          have hzero : 0 ≤ r * ‖x‖ :=
            mul_nonneg hr (norm_nonneg x)
          calc
            Real.exp (t * ‖x‖) ≤ 1 := by
              simpa using Real.exp_le_one_iff.mpr htx
            _ ≤ Real.exp (r * ‖x‖) := by
              simpa using Real.one_le_exp_iff.mpr hzero
      have hd := weightedExp_integral_hasFDerivAt_of_lt
        (μ := μ) hg hgi hz
      have hd' :
          HasFDerivAt
            (fun w : E => ∫ x, Real.exp ⟪w, x⟫ ∂μ)
            (∫ x, Real.exp ⟪z, x⟫ • weightedExpD g x ∂μ) z := by
        simpa [g, smul_eq_mul, mul_one] using hd
      have hi : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
        apply hexp.mono' (by fun_prop)
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          ⟪z, x⟫ ≤ ‖z‖ * ‖x‖ := real_inner_le_norm z x
          _ ≤ r * ‖x‖ := by
            exact mul_le_mul_of_nonneg_right hz.le (norm_nonneg x)
      have hp : 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ :=
        integral_exp_pos hi
      have hlog := hd'.log hp.ne'
      change
        tiltAverage μ (fun x => ⟪v, x⟫) z =
          (fderiv ℝ (fun w : E => Real.log (∫ x, Real.exp ⟪w, x⟫ ∂μ)) z) v
      rw [hlog.fderiv]
      have hwd :
          Integrable
            (fun x =>
              Real.exp (‖z‖ * ‖x‖) * ‖weightedExpD g x‖) μ :=
        (weightedExpD_integrable_lt (μ := μ) hg hgi) ‖z‖ hz
      have hwi :
          Integrable
            (fun x => Real.exp ⟪z, x⟫ • weightedExpD g x) μ := by
        refine hwd.mono' ?_ ?_
        · change AEStronglyMeasurable
            (fun x => Real.exp ⟪z, x⟫ •
              (innerSL ℝ x).smulRight (1 : ℝ)) μ
          fun_prop
        · filter_upwards with x
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact
            mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr (real_inner_le_norm z x))
              (norm_nonneg (weightedExpD g x))
      unfold tiltAverage expTilt
      rw [integral_tilted]
      conv_rhs =>
        rw [smul_apply]
      rw [ContinuousLinearMap.integral_apply hwi]
      simp_rw [smul_eq_mul, div_eq_mul_inv]
      rw [← integral_const_mul]
      congr 1
      funext x
      simp [g, weightedExpD, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        smul_eq_mul, real_inner_comm]
      ring

section NormedSpace

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section DerivativeSymmetry

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma bkl_cumulant_swap_front {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v w : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) g x (Fin.cons v (Fin.cons w h)) =
      iteratedFDeriv ℝ (n + 2) g x (Fin.cons w (Fin.cons v h)) := by
  have hd : ContDiff ℝ ∞ (iteratedFDeriv ℝ n g) :=
    hg.iteratedFDeriv_right (m := ∞) (by norm_cast)
  have ha : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ n g y h) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F h).contDiff.comp hd
  have heq (a : E) :
      (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons a h)) =
        fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ n g z h) y a := by
    funext y
    simpa using (hd.differentiable (by simp) y).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons a h)
  have hleft :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons v (Fin.cons w h))
  have hright :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons w (Fin.cons v h))
  rw [hleft, hright]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [heq w, heq v]
  rw [fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const w),
    fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const v)]
  simpa using
    ((ha.of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).contDiffAt.isSymmSndFDerivAt
      (by simp)).eq v w

private lemma bkl_cumulant_cons_snoc {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) g x (Fin.cons v h) =
      iteratedFDeriv ℝ (n + 1) g x (Fin.snoc h v) := by
  induction n generalizing x with
  | zero =>
      congr 1
      ext i
      fin_cases i
      simp [Fin.snoc_zero]
  | succ n ih =>
      rw [← Fin.cons_self_tail h]
      rw [bkl_cumulant_swap_front hg n x v (h 0) (Fin.tail h)]
      rw [← Fin.cons_snoc_eq_snoc_cons]
      have heq :
          (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons v (Fin.tail h))) =
            fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.snoc (Fin.tail h) v) := by
        funext y
        exact ih y (Fin.tail h)
      rw [(hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left',
        (hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left']
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        congrArg (fun a : E → F => fderiv ℝ a x (h 0)) heq

end DerivativeSymmetry

end NormedSpace

/-- **Taylor tensors of linear functions are cumulants** (proof of BKL Proposition 7.1):
for `ℓ = ⟪v, ·⟫`, `T_d ℓ = κ_{d+1}(v, ·, …, ·) / d!`. -/
theorem taylorTensor_inner_eq_cumulant (μ : Measure E) [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) (d : ℕ)
    (h : Fin d → E) :
    taylorTensor μ (fun x => ⟪v, x⟫) d h =
      (d.factorial : ℝ)⁻¹ * cumulant μ (d + 1) (Fin.cons v h) := by
  have heq : tiltAverage μ (fun x => ⟪v, x⟫) = fun z => fderiv ℝ (logLaplace μ) z v := by
    funext z
    exact tiltAverage_inner_eq_fderiv_logLaplace μ hexp v z
  have hL := contDiff_logLaplace μ hexp
  have hd : ContDiff ℝ ∞ (fderiv ℝ (logLaplace μ)) := hL.fderiv_right (by simp)
  have hder :
    iteratedFDeriv ℝ d (fun z => fderiv ℝ (logLaplace μ) z v) 0 h =
      iteratedFDeriv ℝ d (fderiv ℝ (logLaplace μ)) 0 h v :=
    iteratedFDeriv_clm_apply_const_apply hd (by norm_cast; simp)
  simp only [taylorTensor, smul_apply, smul_eq_mul, heq]
  rw [hder]
  have hs := bkl_cumulant_cons_snoc hL d 0 v h
  have ht :=
    iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := logLaplace μ) (x := (0 : E)) (Fin.snoc h v)
  simp only [Fin.init_snoc, Fin.snoc_last] at ht
  rw [ht] at hs
  exact congrArg (fun a : ℝ => (d.factorial : ℝ)⁻¹ * a) hs.symm

end LaplaceCalculus

section ThirdCumulant

/-- The quadratic-form estimate of Letwin (2026, Theorem 1.2), stated as a property of the law `μ`:
`Var_μ⟨Mx, x⟩ ≤ 8 |M|²_HS` for every self-adjoint `M`, with `|M|²_HS = ∑_{i,j} ⟪M e_i, e_j⟫²` in an
orthonormal basis. This names the hypothesis; it is not proved here. -/
def LetwinQuadraticBound (μ : Measure E) : Prop :=
  ∀ M : E →L[ℝ] E, IsSelfAdjoint M →
    ∫ x, (⟪M x, x⟫ - ∫ y, ⟪M y, y⟫ ∂μ) ^ 2 ∂μ ≤
      8 * ∑ i, ∑ j, ⟪M (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E j⟫ ^ 2

variable (μ : Measure E) [IsProbabilityMeasure μ]
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)

section ThirdMomentIdentities

omit [CompleteSpace E]

include hexp in
/-- The first derivative of the logarithmic Laplace transform at `0` is the mean. -/
theorem fderiv_logLaplace_zero_apply (v : E) :
    fderiv ℝ (logLaplace μ) 0 v = ∫ x, ⟪v, x⟫ ∂μ := by
    calc
      fderiv ℝ (logLaplace μ) 0 v =
          tiltAverage μ (fun x => ⟪v, x⟫) 0 :=
        (tiltAverage_inner_eq_fderiv_logLaplace μ hexp v 0).symm
      _ = ∫ x, ⟪v, x⟫ ∂μ := by
        simp [tiltAverage, expTilt]

section ThirdSecondCumulants

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma third_second_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v w : E) :
    iteratedFDeriv ℝ 2 f x ![v, w] =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [(hf.differentiable_iteratedFDeriv (m := 1) (by norm_num) x).iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Fin.tail, Matrix.cons_val_zero, Matrix.cons_val_succ]

private lemma third_second_mul {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x v w : E) (hf0 : f x = 0) (hg0 : g x = 1)
    (hg1 : fderiv ℝ g x = 0) :
    iteratedFDeriv ℝ 2 (fun y => f y * g y) x ![v, w] =
      iteratedFDeriv ℝ 2 f x ![v, w] := by
  have hdf := hf.fderiv_right (m := ∞) (by simp)
  have hdg := hg.fderiv_right (m := ∞) (by simp)
  have hfw : Differentiable ℝ (fun y => fderiv ℝ f y w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp hdf).differentiable (by simp)
  have hgw : Differentiable ℝ (fun y => fderiv ℝ g y w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp hdg).differentiable (by simp)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =
      fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w := by
    funext y
    rw [fderiv_fun_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    simp
  rw [third_second_apply (hf.mul hg), third_second_apply hf, heq]
  rw [fderiv_fun_add (f := fun y => f y * fderiv ℝ g y w)
    (g := fun y => g y * fderiv ℝ f y w)
    ((hf.differentiable (by simp) x).mul (hgw x))
    ((hg.differentiable (by simp) x).mul (hfw x))]
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hgw x),
    fderiv_fun_mul (hg.differentiable (by simp) x) (hfw x)]
  simp [hf0, hg0, hg1]

end ThirdSecondCumulants

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
include hexp in
private lemma third_exp_inner_integrable (u : E) (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖) * ‖⟪u, x⟫‖) μ := by
  refine ((hexp (r + 1)).const_mul ‖u‖).mono'
    (by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖) * ‖⟪u, x⟫‖)).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
    le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
  calc
    Real.exp (r * ‖x‖) * ‖⟪u, x⟫‖ ≤
        Real.exp (r * ‖x‖) * (‖u‖ * Real.exp ‖x‖) := by
      gcongr
      exact (norm_inner_le_norm u x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg u))
    _ = ‖u‖ * Real.exp ((r + 1) * ‖x‖) := by
      rw [add_mul, one_mul, Real.exp_add]
      ring

include hexp in
/-- For a centered law, the second Taylor tensor of a linear function is half the third moment:
`T_2⟪u, ·⟫(v, w) = ½ ∫ ⟪u, x⟫ ⟪v, x⟫ ⟪w, x⟫ dμ`. -/
theorem taylorTensor_two_inner_eq_of_centered (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
    taylorTensor μ (fun x => ⟪u, x⟫) 2 ![v, w] =
      (1 / 2 : ℝ) * ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
  let F := tiltAverage μ (fun x => ⟪u, x⟫)
  let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • ⟪u, x⟫ ∂μ
  have hF : ContDiff ℝ ∞ F := by
    have heq : F = fun z => fderiv ℝ (logLaplace μ) z u :=
      funext (tiltAverage_inner_eq_fderiv_logLaplace μ hexp u)
    rw [heq]
    exact
      (ContinuousLinearMap.apply ℝ ℝ u).contDiff.comp
        ((contDiff_logLaplace μ hexp).fderiv_right (by simp))
  have hZ : ContDiff ℝ ∞ Z :=
    contDiff_integral_exp_inner_smul_of_integrable μ measurable_const.aestronglyMeasurable
      (by simpa using hexp)
  have hZ0 : Z 0 = 1 := by simp [Z]
  have hF0 : F 0 = 0 := by simpa [F, tiltAverage, expTilt] using hc u
  have hZ1 : fderiv ℝ Z 0 = 0 := by
    ext a
    have h :=
      iteratedFDeriv_integral_exp_inner_smul μ (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (by simpa using hexp) 1 0 ![a]
    have h' : fderiv ℝ Z 0 a = ∫ x, ⟪a, x⟫ ∂μ := by
      simpa [Z, iteratedFDeriv_one_apply, real_inner_comm] using h
    exact h'.trans (hc a)
  have hNZ : N = fun z => F z * Z z := by
    funext z
    have hi : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
      refine
        (hexp ‖z‖).mono'
          (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable ?_
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 := (integral_exp_pos hi).ne'
    dsimp [N, F, Z]
    rw [tiltAverage, expTilt, integral_tilted]
    simp only [smul_eq_mul, mul_one, div_eq_mul_inv]
    rw [show
        (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * ⟪u, x⟫) =
          (fun x => (Real.exp ⟪z, x⟫ * ⟪u, x⟫) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹)
        by funext x; ring]
    rw [integral_mul_const]
    field_simp
  have hsecond := third_second_mul hF hZ 0 v w hF0 hZ0 hZ1
  rw [← hNZ] at hsecond
  have hm :=
    iteratedFDeriv_integral_exp_inner_smul μ (g := fun x => ⟪u, x⟫)
      (by fun_prop : Continuous (fun x : E => ⟪u, x⟫)).aestronglyMeasurable
      (third_exp_inner_integrable μ hexp u) 2 0 ![v, w]
  have hm' : iteratedFDeriv ℝ 2 N 0 ![v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
    simpa [N, Fin.prod_univ_two, smul_eq_mul, real_inner_comm, mul_comm, mul_left_comm,
      mul_assoc] using hm
  simp only [taylorTensor, smul_apply, smul_eq_mul]
  change (Nat.factorial 2 : ℝ)⁻¹ * iteratedFDeriv ℝ 2 F 0 ![v, w] = _
  rw [← hsecond, hm']
  norm_num

include hexp in
/-- The third cumulant of a centered law is its third moment. -/
theorem cumulant_three_eq_integral (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
    cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
  have hvec : Fin.cons u ![v, w] = ![u, v, w] := by
    funext i
    fin_cases i <;> rfl
  have h := taylorTensor_inner_eq_cumulant μ hexp u 2 ![v, w]
  rw [taylorTensor_two_inner_eq_of_centered μ hexp hc u v w] at h
  rw [hvec] at h
  norm_num [Nat.factorial] at h
  linarith

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
omit [InnerProductSpace ℝ E] in
include hexp in
private lemma third_memLp_poly {g : E → ℝ} (hg : Continuous g)
    {C : ℝ} {k : ℕ} (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    MemLp g 2 μ := by
  apply (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
  refine ((hexp (2 * (k : ℝ))).const_mul (C ^ 2)).mono'
    (hg.pow 2).aestronglyMeasurable ?_
  filter_upwards [] with x
  have he : (1 + ‖x‖) ^ k ≤ Real.exp ((k : ℝ) * ‖x‖) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      (by simpa [add_comm] using Real.add_one_le_exp ‖x‖) k
  calc
    ‖g x ^ 2‖ = ‖g x‖ ^ 2 := norm_pow _ _
    _ ≤ (C * Real.exp ((k : ℝ) * ‖x‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((hb x).trans (mul_le_mul_of_nonneg_left he hC)) 2
    _ = C ^ 2 * Real.exp (2 * (k : ℝ) * ‖x‖) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
include hexp in
private lemma third_memLp_inner (v : E) :
    MemLp (fun x => ⟪v, x⟫) 2 μ := by
  apply third_memLp_poly μ hexp (by fun_prop) (norm_nonneg v) (k := 1)
  intro x
  simpa only [pow_one] using
    (norm_inner_le_norm v x).trans
      (mul_le_mul_of_nonneg_left (by linarith : ‖x‖ ≤ 1 + ‖x‖) (norm_nonneg v))

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
include hexp in
private lemma third_memLp_inner_mul (v w : E) :
    MemLp (fun x => ⟪v, x⟫ * ⟪w, x⟫) 2 μ := by
  apply third_memLp_poly μ hexp (by fun_prop)
    (mul_nonneg (norm_nonneg v) (norm_nonneg w)) (k := 2)
  intro x
  calc
    ‖⟪v, x⟫ * ⟪w, x⟫‖ ≤ (‖v‖ * ‖x‖) * (‖w‖ * ‖x‖) := by
      rw [norm_mul]
      exact mul_le_mul (norm_inner_le_norm v x) (norm_inner_le_norm w x)
        (norm_nonneg _) (by positivity)
    _ = (‖v‖ * ‖w‖) * ‖x‖ ^ 2 := by ring
    _ ≤ (‖v‖ * ‖w‖) * (1 + ‖x‖) ^ 2 := by gcongr; linarith

end ThirdMomentIdentities

omit [BorelSpace E] in
/-- The Letwin quadratic estimate contracts the centered isotropic third moments.
Only linear and quadratic L2 membership is used, independently of its producer. -/
theorem sum_sq_thirdMoment_le_of_letwin
    (hlin : ∀ v : E, MemLp (fun x => ⟪v, x⟫) 2 μ)
    (hquad : ∀ v w : E, MemLp (fun x => ⟪v, x⟫ * ⟪w, x⟫) 2 μ)
    (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫)
    (hL : LetwinQuadraticBound μ) (u : E) :
    ∑ j, ∑ k, (∫ x, ⟪u, x⟫ * ⟪stdOrthonormalBasis ℝ E j, x⟫ *
      ⟪stdOrthonormalBasis ℝ E k, x⟫ ∂μ) ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let C := fun j k => ∫ x, ⟪u, x⟫ * ⟪b j, x⟫ * ⟪b k, x⟫ ∂μ
  let S : ℝ := ∑ j, ∑ k, C j k ^ 2
  let M : E →L[ℝ] E := ∑ j, ∑ k, C j k • (innerSL ℝ (b k)).smulRight (b j)
  let Q : E → ℝ := fun x => ⟪M x, x⟫
  let f : E → ℝ := fun x => ⟪u, x⟫
  let q : E → ℝ := fun x => Q x - ∫ y, Q y ∂μ
  have hC : ∀ j k, C j k = C k j := by
    intro j k
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hMxy (x y : E) :
      ⟪M x, y⟫ = ∑ j, ∑ k, C j k * ⟪b k, x⟫ * ⟪b j, y⟫ := by
    simp [M, sum_inner, real_inner_smul_left, mul_assoc]
  have hM : IsSelfAdjoint M := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    intro x y
    change ⟪M x, y⟫ = ⟪x, M y⟫
    conv_rhs => rw [real_inner_comm]
    rw [hMxy, hMxy, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hC k j]
    ring
  have hMij (i j) : ⟪M (b i), b j⟫ = C j i := by
    rw [hMxy]
    simp [b.inner_eq_ite]
  have hvar : ∫ x, q x ^ 2 ∂μ ≤ 8 * S := by
    simpa only [q, Q, hMij, hC, S, b] using hL M hM
  have hf : MemLp f 2 μ := hlin u
  have hQ : MemLp Q 2 μ := by
    have heq : Q = fun x => ∑ j, ∑ k, C j k * (⟪b k, x⟫ * ⟪b j, x⟫) := by
      funext x
      simp only [Q, hMxy, mul_assoc]
    rw [heq]
    exact memLp_finsetSum _ fun j _ =>
      memLp_finsetSum _ fun k _ =>
        (hquad (b k) (b j)).const_mul (C j k)
  have hq : MemLp q 2 μ := hQ.sub (memLp_const _)
  have hcross : ∫ x, f x * q x ∂μ = S := by
    have hprod : ∀ j k, Integrable (fun x => ⟪u, x⟫ * (⟪b k, x⟫ * ⟪b j, x⟫)) μ :=
      fun j k => hf.integrable_mul (hquad (b k) (b j))
    have hprodC : ∀ j k, Integrable (fun x => C j k * (⟪u, x⟫ * (⟪b k, x⟫ * ⟪b j, x⟫))) μ :=
      fun j k => (hprod j k).const_mul _
    have hsum : Integrable (fun x => f x * Q x) μ := hf.integrable_mul hQ
    simp only [q, mul_sub]
    rw [integral_sub hsum ((hf.integrable (by norm_num)).mul_const (∫ y, Q y ∂μ)),
      integral_mul_const]
    simp only [f, hc, zero_mul, sub_zero]
    simp_rw [Q, hMxy, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        have heq : (fun x => ⟪u, x⟫ * (C j k * ⟪b k, x⟫ * ⟪b j, x⟫)) =
            fun x => C j k * (⟪u, x⟫ * ⟪b j, x⟫ * ⟪b k, x⟫) := by
          funext x; ring
        rw [heq, integral_const_mul]
        exact (pow_two (C j k)).symm
      · intro k _
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodC j k
    · intro j _
      apply integrable_finsetSum
      intro k _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodC j k
  have hf2 : Integrable (fun x => f x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hq2 : Integrable (fun x => q x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hq.aestronglyMeasurable).1 hq
  have hsq : 0 ≤ (∫ x, q x ^ 2 ∂μ) - 16 * S + 64 * ‖u‖ ^ 2 := by
    have hn := integral_nonneg (μ := μ) (f := fun x => (q x - 8 * f x) ^ 2)
      (fun x => sq_nonneg _)
    have heq : (fun x => (q x - 8 * f x) ^ 2) =
        fun x => q x ^ 2 - 16 * (f x * q x) + 64 * f x ^ 2 := by
      funext x; ring
    rw [heq, integral_add (f := fun x => q x ^ 2 - 16 * (f x * q x))
      (g := fun x => 64 * f x ^ 2)
      (hq2.sub ((hf.integrable_mul hq).const_mul 16))
      (hf2.const_mul 64),
      integral_sub (f := fun x => q x ^ 2) (g := fun x => 16 * (f x * q x))
      hq2 ((hf.integrable_mul hq).const_mul 16),
      integral_const_mul, integral_const_mul, hcross] at hn
    have he : ∫ x, f x ^ 2 ∂μ = ‖u‖ ^ 2 := by
      simpa only [f, pow_two, real_inner_self_eq_norm_sq] using hiso u u
    rwa [he] at hn
  change S ≤ 8 * ‖u‖ ^ 2
  linarith

include hexp in
/-- **BKL Lemma 4.2, conditional on the Letwin bound**: for a centered isotropic probability law
with all exponential moments satisfying `LetwinQuadraticBound`, `R^μ_3 ≤ 8 Id`, that is
`∑_{j,k} κ_3(u, e_j, e_k)² ≤ 8 |u|²` for every `u`. -/
theorem sum_sq_cumulant_three_le_of_letwin (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : LetwinQuadraticBound μ) (u : E) :
    ∑ j, ∑ k, cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by
  have hκ (v w : E) :
      cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
    have ht := taylorTensor_two_inner_eq_of_centered μ hexp hc u v w
    rw [taylorTensor_inner_eq_cumulant μ hexp u 2 ![v, w]] at ht
    norm_num at ht
    linarith
  simp_rw [hκ]
  exact sum_sq_thirdMoment_le_of_letwin μ (third_memLp_inner μ hexp)
    (third_memLp_inner_mul μ hexp) hc hiso hL u
end ThirdCumulant


section CumulantEstimates

omit [CompleteSpace E]

/--
**Linear step of BKL Proposition 7.1** (p. 30): under the cumulant bound `R^μ_{d+1} ≤ b Id` in
coordinates, `Σ_J κ_{d+1}(u, e_J)² ≤ b |u|²`, the Taylor tensor of `ℓ = ⟪v, ·⟫` satisfies
`|T_d ℓ|² ≤ b |v|² / (d!)²` in the Hilbert–Schmidt norm, by `T_d ℓ = κ_{d+1}(v, ·, …, ·) / d!`. -/
theorem norm_coordTensor_taylorTensor_inner_sq_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {d : ℕ} {b : ℝ}
    (hR :
      ∀ u : E,
        ∑ J : Fin d → Fin (Module.finrank ℝ E),
            cumulant μ (d + 1) (Fin.cons u fun k => stdOrthonormalBasis ℝ E (J k)) ^ 2 ≤
          b * ‖u‖ ^ 2)
    (v : E) :
    ‖Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ E)
            (taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^
        2 ≤
      b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
  have hcoord :
    ∀ J : Fin d → Fin (Module.finrank ℝ E),
      (Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ E)
              (taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp
          J =
        (d.factorial : ℝ)⁻¹ *
          cumulant μ (d + 1) (Fin.cons v (fun k => stdOrthonormalBasis ℝ E (J k))) := by
    intro J
    simp [Analysis.Tensor.coordTensor_apply, taylorTensor_inner_eq_cumulant, hexp]
  rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ J : Fin d → Fin (Module.finrank ℝ E),
          ‖(Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ E)
                    (taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp
                J‖ ^
            2 =
        ((d.factorial : ℝ)⁻¹) ^ 2 *
          ∑ J : Fin d → Fin (Module.finrank ℝ E),
            cumulant μ (d + 1) (Fin.cons v (fun k => stdOrthonormalBasis ℝ E (J k))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [hcoord J, norm_mul]
      simp [Real.norm_eq_abs, sq_abs, mul_pow]
    _ ≤ ((d.factorial : ℝ)⁻¹) ^ 2 * (b * ‖v‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hR v) (sq_nonneg _)
    _ = b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      simp [div_eq_mul_inv, inv_pow]
      ring


/-- **Linear-function step in an arbitrary orthonormal basis** (BKL p. 30): the special case
`norm_coordTensor_taylorTensor_inner_sq_le` with `stdOrthonormalBasis ℝ E` replaced by any
orthonormal
basis `bE`. -/
theorem norm_coordTensor_taylorTensor_inner_sq_le_of_basis (μ : Measure E)
    [IsProbabilityMeasure μ] (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {m : ℕ} (bE : OrthonormalBasis (Fin m) ℝ E) {d : ℕ} {b : ℝ}
    (hR :
      ∀ u : E,
        ∑ J : Fin d → Fin m, cumulant μ (d + 1) (Fin.cons u fun k => bE (J k)) ^ 2 ≤
          b * ‖u‖ ^ 2)
    (v : E) :
    ‖Analysis.Tensor.coordTensor bE (taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
  have hcoord :
    ∀ J : Fin d → Fin m,
      (Analysis.Tensor.coordTensor (bE) (taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp J =
        (d.factorial : ℝ)⁻¹ * cumulant μ (d + 1) (Fin.cons v (fun k => bE (J k))) := by
    intro J
    simp [Analysis.Tensor.coordTensor_apply, taylorTensor_inner_eq_cumulant, hexp]
  rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ J : Fin d → Fin m,
          ‖(Analysis.Tensor.coordTensor (bE) (taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp J‖ ^ 2 =
        ((d.factorial : ℝ)⁻¹) ^ 2 *
          ∑ J : Fin d → Fin m, cumulant μ (d + 1) (Fin.cons v (fun k => bE (J k))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [hcoord J, norm_mul]
      simp [Real.norm_eq_abs, sq_abs, mul_pow]
    _ ≤ ((d.factorial : ℝ)⁻¹) ^ 2 * (b * ‖v‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hR v) (sq_nonneg _)
    _ = b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      simp [div_eq_mul_inv, inv_pow]
      ring

open scoped ContDiff in
/-- **Local smoothness of `Λ_μ`** (BKL p. 29, "finite and smooth in a neighborhood of the origin"):
one positive norm-exponential moment `∫ e^{r‖x‖} dμ < ∞` makes `Λ_μ` `C^∞` on the open ball of
radius `r`. The local integral identities are in `Tilt/Local.lean`. -/
theorem contDiffOn_logLaplace_ball (μ : Measure E) [NeZero μ] {r : ℝ}
    (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiffOn ℝ ∞ (logLaplace μ) (Metric.ball 0 r) := by
  let _ := hr
  have hgi : ∀ t < r,
      Integrable (fun x : E => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
    intro t ht
    simpa only [norm_one, mul_one] using
      Probability.integrable_exp_mul_norm_of_le hexp ht.le
  have hZ : ContDiffOn ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ)
      (Metric.ball 0 r) := by
    simpa only [smul_eq_mul, mul_one] using
      weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable hgi
  apply hZ.log
  intro z hz
  have hz' : ‖z‖ < r := by simpa using hz
  have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
    refine (hgi ‖z‖ hz').mono' ?_ ?_
    · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
    · filter_upwards [] with x
      simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
  exact (integral_exp_pos hzint).ne'

end CumulantEstimates

/-- Iterated derivatives of a composition with a continuous linear equivalence. -/
private theorem equiv_iteratedFDeriv_univ {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : G ≃L[ℝ] E) (f : E → F) (x : G) (i : ℕ) :
    iteratedFDeriv ℝ i (f ∘ g) x =
      (iteratedFDeriv ℝ i f (g x)).compContinuousLinearMap
        (fun _ => (g : G →L[ℝ] E)) := by
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using
    g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
      (Set.mem_univ (g x)) i

section InnerProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cumulants along a linear isometry**: `κ^{φ_*ν}_k(φ u₁, …, φ u_k) = κ^ν_k(u₁, …, u_k)` for
every measure `ν` on a real inner-product space, since `Λ_{φ_*ν} = Λ_ν ∘ φ⁻¹` pointwise. -/
theorem cumulant_map_linearIsometryEquiv [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (φ : E ≃ₗᵢ[ℝ] F) (ν : Measure E) (k : ℕ) (u : Fin k → E) :
    cumulant (ν.map φ) k (fun i => φ (u i)) = cumulant ν k u := by
    have hlog :
        logLaplace (ν.map φ) = logLaplace ν ∘ (φ.symm : F → E) := by
      funext z
      simp only [logLaplace, Function.comp_apply]
      let hcont : Continuous (fun y : F => Real.exp ⟪z, y⟫) :=
        Real.continuous_exp.comp (continuous_const.inner continuous_id)
      have hz :
          AEStronglyMeasurable (fun y : F => Real.exp ⟪z, y⟫) (ν.map φ) :=
        hcont.aestronglyMeasurable
      have hmap :
          (∫ y : F, Real.exp ⟪z, y⟫ ∂(ν.map φ)) =
            ∫ x : E, Real.exp ⟪z, φ x⟫ ∂ν := by
        rw [integral_map φ.continuous.measurable.aemeasurable hz]
      have hinner :
          (∫ x : E, Real.exp ⟪z, φ x⟫ ∂ν) =
            ∫ x : E, Real.exp ⟪φ.symm z, x⟫ ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hx : ⟪z, φ x⟫ = ⟪φ.symm z, x⟫ := by
          simpa using (φ.symm.inner_map_map z (φ x)).symm
        rw [hx]
      rw [hmap, hinner]
    change
      (iteratedFDeriv ℝ k (logLaplace (ν.map φ)) 0)
          (fun i => φ (u i)) =
        (iteratedFDeriv ℝ k (logLaplace ν) 0) u
    rw [hlog]
    have hderiv :
        iteratedFDeriv ℝ k (logLaplace ν ∘ (φ.symm : F → E)) 0 =
          (iteratedFDeriv ℝ k (logLaplace ν) 0).compContinuousLinearMap
            (fun _ => (φ.symm.toContinuousLinearEquiv : F →L[ℝ] E)) := by
      simpa using
        (equiv_iteratedFDeriv_univ
          (g := φ.symm.toContinuousLinearEquiv) (f := logLaplace ν)
          (x := (0 : F)) (i := k))
    rw [hderiv]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

private lemma affine_iteratedFDeriv_linear_eq_zero
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] ℝ) {k : ℕ} (hk : 2 ≤ k) (x : G) :
    iteratedFDeriv ℝ k L x = 0 := by
  have hone :
      iteratedFDeriv ℝ 1 L =
        fun _ : G => iteratedFDeriv ℝ 1 L (0 : G) := by
    funext y
    ext v
    simp only [iteratedFDeriv_one_apply, ContinuousLinearMap.fderiv]
  have hz : ∀ n : ℕ, 2 ≤ n → ∀ y : G, iteratedFDeriv ℝ n L y = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro y
        ext v
        change iteratedFDeriv ℝ (1 + 1) L y v = 0
        rw [iteratedFDeriv_succ_apply_left, hone]
        simp
    | succ n _hn ih =>
        have hfun : iteratedFDeriv ℝ n L = fun _ : G => 0 := funext ih
        intro y
        ext v
        change iteratedFDeriv ℝ (n + 1) L y v = 0
        rw [iteratedFDeriv_succ_apply_left, hfun]
        simp
  exact hz k hk x

/-- **Cumulants along an affine map** (BKL (77)): for `k ≥ 2`, the cumulants of the push-forward of
`μ` under `x ↦ T (x - a)` are those of `μ` evaluated on the adjoint directions,
`κ^{(T(· - a))_*μ}_k(u₁, …, u_k) = κ^μ_k(T† u₁, …, T† u_k)`. -/
theorem cumulant_map_affine [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (a : E) (μ : Measure E) [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {k : ℕ} (hk : 2 ≤ k) (u : Fin k → F) :
    cumulant (μ.map (fun x => T (x - a))) k u =
      cumulant μ k (fun i => ContinuousLinearMap.adjoint (T : E →L[ℝ] F) (u i)) := by
  let A : F →L[ℝ] E := ContinuousLinearMap.adjoint (T : E →L[ℝ] F)
  let L : F →L[ℝ] ℝ := (innerSL ℝ a).comp A
  have hL (z : F) : L z = ⟪A z, a⟫ := by
    change ⟪a, A z⟫ = ⟪A z, a⟫
    exact (real_inner_comm a (A z)).symm
  have hadjoint (z : F) (x : E) : ⟪z, T x⟫ = ⟪A z, x⟫ := by
    change ⟪z, (T : E →L[ℝ] F) x⟫ =
      ⟪ContinuousLinearMap.adjoint (T : E →L[ℝ] F) z, x⟫
    simp only [ContinuousLinearMap.adjoint_inner_left]
  have hmeas : Measurable (fun x : E => T (x - a)) :=
    (T.continuous.comp (continuous_id.sub continuous_const)).measurable
  have hlog :
      logLaplace (μ.map (fun x => T (x - a))) =
        (logLaplace μ ∘ A) - (L : F → ℝ) := by
    funext z
    have hint : Integrable (fun x : E => Real.exp ⟪A z, x⟫) μ := by
      refine (hexp ‖A z‖).mono'
        ((continuous_const.inner continuous_id).rexp.aestronglyMeasurable) ?_
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (real_inner_le_norm (A z) x)
    have hpos : 0 < ∫ x : E, Real.exp ⟪A z, x⟫ ∂μ :=
      integral_exp_pos hint
    have hfactor :
        (fun x : E => Real.exp ⟪z, T (x - a)⟫) =
          fun x => Real.exp (-L z) * Real.exp ⟪A z, x⟫ := by
      funext x
      rw [hadjoint, inner_sub_right, ← hL z, sub_eq_add_neg, Real.exp_add]
      exact mul_comm _ _
    have hzm :
        AEStronglyMeasurable (fun y : F => Real.exp ⟪z, y⟫)
          (μ.map (fun x => T (x - a))) :=
      (continuous_const.inner continuous_id).rexp.aestronglyMeasurable
    change Real.log (∫ y : F, Real.exp ⟪z, y⟫
      ∂(μ.map (fun x => T (x - a)))) = logLaplace μ (A z) - L z
    rw [integral_map hmeas.aemeasurable hzm, hfactor, integral_const_mul,
      Real.log_mul (Real.exp_ne_zero _) hpos.ne', Real.log_exp]
    change -L z + logLaplace μ (A z) = logLaplace μ (A z) - L z
    ring
  have hΛ : ContDiff ℝ ∞ (logLaplace μ) := contDiff_logLaplace μ hexp
  have hΛk : ContDiff ℝ k (logLaplace μ) :=
    hΛ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (logLaplace μ ∘ A) := hΛ.comp A.contDiff
  have hgk : ContDiff ℝ k (logLaplace μ ∘ A) := hΛk.comp A.contDiff
  have hl : ContDiff ℝ ∞ (L : F → ℝ) := L.contDiff
  have hlk : ContDiff ℝ k (L : F → ℝ) := L.contDiff
  have hsub :
      iteratedFDeriv ℝ k ((logLaplace μ ∘ A) - (L : F → ℝ)) (0 : F) =
        iteratedFDeriv ℝ k (logLaplace μ ∘ A) 0 -
          iteratedFDeriv ℝ k L 0 := by
    have hs :
        iteratedFDeriv ℝ k ((logLaplace μ ∘ A) - (L : F → ℝ)) =
          iteratedFDeriv ℝ k (logLaplace μ ∘ A) -
            iteratedFDeriv ℝ k L := by
      apply iteratedFDeriv_sub
      all_goals assumption
    exact congrFun hs (0 : F)
  have hchain :
      iteratedFDeriv ℝ k (logLaplace μ ∘ A) (0 : F) =
        (iteratedFDeriv ℝ k (logLaplace μ) (A 0)).compContinuousLinearMap
          (fun _ => A) := by
    apply ContinuousLinearMap.iteratedFDeriv_comp_right
    all_goals
      first
      | exact hΛ
      | exact WithTop.coe_le_coe.mpr le_top
  change (iteratedFDeriv ℝ k
      (logLaplace (μ.map (fun x => T (x - a)))) 0) u =
    (iteratedFDeriv ℝ k (logLaplace μ) 0) (fun i => A (u i))
  rw [hlog, hsub, affine_iteratedFDeriv_linear_eq_zero L hk, sub_zero, hchain]
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]

end InnerProduct

section MomentLimit

open ProbabilityTheory Filter Topology

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma quadratic_basis_expansion
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (M : E →L[ℝ] E) (x : E) :
    ⟪M x, x⟫ =
      ∑ i, ∑ j, ⟪M (b i), b j⟫ * (⟪b i, x⟫ * ⟪b j, x⟫) := by
  classical
  calc
    ⟪M x, x⟫ =
        ⟪M (∑ i, ⟪b i, x⟫ • b i), ∑ j, ⟪b j, x⟫ • b j⟫ := by
      rw [b.sum_repr']
    _ = ∑ i, ∑ j, ⟪M (b i), b j⟫ * (⟪b i, x⟫ * ⟪b j, x⟫) := by
      rw [map_sum, sum_inner]
      simp only [map_smul, real_inner_smul_left, inner_sum, inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma quadratic_coordinate_memLp
    [MeasurableSpace E] {ρ : Measure E} (hρ : MemLp id 4 ρ) (u v : E) :
    MemLp (fun x => ⟪u, x⟫ * ⟪v, x⟫) 2 ρ := by
  have ht : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    constructor
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_add]
    norm_num
  have hu : MemLp (fun x => (⟪u, x⟫ : ℝ)) 4 ρ := hρ.const_inner u
  have hv : MemLp (fun x => (⟪v, x⟫ : ℝ)) 4 ρ := hρ.const_inner v
  exact hu.mul hv (hpqr := ht)

private lemma tendsto_integral_finite_linear_combination
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : ℕ → Measure α) (ν : Measure α)
    (c : ι → ℝ) (f : ι → α → ℝ)
    (hμ : ∀ k i, Integrable (f i) (μ k))
    (hν : ∀ i, Integrable (f i) ν)
    (ht : ∀ i, Tendsto (fun k => ∫ x, f i x ∂μ k) atTop
      (𝓝 (∫ x, f i x ∂ν))) :
    Tendsto (fun k => ∫ x, ∑ i, c i * f i x ∂μ k) atTop
      (𝓝 (∫ x, ∑ i, c i * f i x ∂ν)) := by
  classical
  have heq :
      (fun k => ∫ x, ∑ i, c i * f i x ∂μ k) =
        (fun k => ∑ i, c i * ∫ x, f i x ∂μ k) := by
    funext k
    rw [integral_finsetSum _ (fun i _ => (hμ k i).const_mul (c i))]
    simp only [integral_const_mul]
  rw [heq, integral_finsetSum _ (fun i _ => (hν i).const_mul (c i))]
  simp only [integral_const_mul]
  exact tendsto_finsetSum _ (fun i _ => (ht i).const_mul (c i))

private lemma square_finite_linear_combination
    {α ι : Type*} [Fintype ι] (c : ι → ℝ) (f : ι → α → ℝ) :
    (fun x => (∑ i, c i * f i x) ^ 2) =
      (fun x => ∑ p : ι × ι, (c p.1 * c p.2) * (f p.1 x * f p.2 x)) := by
  classical
  funext x
  rw [pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Letwin's quadratic bound passes to limits in the moments of degree ≤ 4** (Letwin
arXiv:2607.24164v1, Lemma A.1, last sentence: "both sides of (1.2) pass to the limit"): if
probability laws `μ k` with finite fourth moments satisfy `LetwinQuadraticBound` and all mixed
moments `∫ ∏ᵢ ⟪vᵢ, x⟫` of degree `d ≤ 4` converge to those of a law `ν` with finite fourth
moment, then `ν` satisfies `LetwinQuadraticBound`. -/
theorem letwinQuadraticBound_of_tendsto_moments [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] (μ : ℕ → Measure E) (ν : Measure E)
    [∀ k, IsProbabilityMeasure (μ k)] [IsProbabilityMeasure ν] (hμ : ∀ k, MemLp id 4 (μ k))
    (hν : MemLp id 4 ν)
    (hmom :
      ∀ d : ℕ,
        d ≤ 4 →
          ∀ v : Fin d → E,
            Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(μ k)) atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂ν)))
    (hL : ∀ k, LetwinQuadraticBound (μ k)) : LetwinQuadraticBound ν := by
  classical
  intro M hM
  let b := stdOrthonormalBasis ℝ E
  let I := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
  let c : I → ℝ := fun p => ⟪M (b p.1), b p.2⟫
  let f : I → E → ℝ := fun p x => ⟪b p.1, x⟫ * ⟪b p.2, x⟫
  let Q : E → ℝ := fun x => ⟪M x, x⟫
  have hQ : Q = fun x => ∑ p : I, c p * f p x := by
    funext x
    dsimp only [Q, c, f]
    rw [Fintype.sum_prod_type]
    exact quadratic_basis_expansion b M x
  have hQsq :
    (fun x => Q x ^ 2) = (fun x => ∑ p : I × I, (c p.1 * c p.2) * (f p.1 x * f p.2 x)) := by
    rw [hQ]
    exact square_finite_linear_combination c f
  have hf (ρ : Measure E) (hρ : MemLp id 4 ρ) (p : I) : MemLp (f p) 2 ρ :=
    quadratic_coordinate_memLp hρ (b p.1) (b p.2)
  have hQQ (ρ : Measure E) (hρ : MemLp id 4 ρ) : MemLp Q 2 ρ := by
    rw [hQ]
    exact memLp_finsetSum _ (fun p _ => (hf ρ hρ p).const_mul (c p))
  have ht2 (p : I) : Tendsto (fun k => ∫ x, f p x ∂μ k) atTop (𝓝 (∫ x, f p x ∂ν)) := by
    simpa [f, Fin.prod_univ_two] using hmom 2 (by norm_num) ![b p.1, b p.2]
  have ht4 (p : I × I) :
    Tendsto (fun k => ∫ x, f p.1 x * f p.2 x ∂μ k) atTop (𝓝 (∫ x, f p.1 x * f p.2 x ∂ν)) := by
    simpa [f, Fin.prod_univ_four, mul_assoc] using
      hmom 4 (by norm_num) ![b p.1.1, b p.1.2, b p.2.1, b p.2.2]
  have hfirst : Tendsto (fun k => ∫ x, Q x ∂μ k) atTop (𝓝 (∫ x, Q x ∂ν)) := by
    rw [hQ]
    exact
      tendsto_integral_finite_linear_combination μ ν c f
        (fun k p => (hf (μ k) (hμ k) p).integrable (by norm_num))
        (fun p => (hf ν hν p).integrable (by norm_num)) ht2
  have hsecond : Tendsto (fun k => ∫ x, Q x ^ 2 ∂μ k) atTop (𝓝 (∫ x, Q x ^ 2 ∂ν)) := by
    rw [hQsq]
    exact
      tendsto_integral_finite_linear_combination μ ν (fun p : I × I => c p.1 * c p.2)
        (fun p : I × I => fun x => f p.1 x * f p.2 x)
        (fun k p => (hf (μ k) (hμ k) p.1).integrable_mul (hf (μ k) (hμ k) p.2))
        (fun p => (hf ν hν p.1).integrable_mul (hf ν hν p.2)) ht4
  have hv (ρ : Measure E) [IsProbabilityMeasure ρ] (hρ : MemLp id 4 ρ) :
    (∫ x, (Q x - ∫ y, Q y ∂ρ) ^ 2 ∂ρ) = (∫ x, Q x ^ 2 ∂ρ) - (∫ x, Q x ∂ρ) ^ 2 := by
    exact
      (ProbabilityTheory.variance_eq_integral (hQQ ρ hρ).aemeasurable).symm.trans
        (ProbabilityTheory.variance_eq_sub (hQQ ρ hρ))
  have hcenter :
    Tendsto (fun k => ∫ x, (Q x - ∫ y, Q y ∂μ k) ^ 2 ∂μ k) atTop
      (𝓝 (∫ x, (Q x - ∫ y, Q y ∂ν) ^ 2 ∂ν)) := by
    have heq :
      (fun k => ∫ x, (Q x - ∫ y, Q y ∂μ k) ^ 2 ∂μ k) =
        (fun k => (∫ x, Q x ^ 2 ∂μ k) - (∫ x, Q x ∂μ k) ^ 2) :=
      funext fun k => hv (μ k) (hμ k)
    rw [heq, hv ν hν]
    exact hsecond.sub (hfirst.pow 2)
  exact le_of_tendsto' hcenter (fun k => hL k M hM)

end InnerProduct

end MomentLimit

end FunctionalInequalities.Analysis.BakryEmery
