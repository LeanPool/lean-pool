/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.BasisChange
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Positivity
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.GradientJet
public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.Symmetry
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Third cumulants from one exponential moment

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Lemma 4.2, in its source scope: log-concavity guarantees
some positive exponential radius (Borell) but not, in general, every exponential moment, so the
third-cumulant
identity and the Hilbert–Schmidt contraction bound are derived here from a single radius `r > 0`
with `∫ e^{r‖x‖} dμ < ∞`: `κ₃(u,v,w) = ∫⟪u,x⟫⟪v,x⟫⟪w,x⟫` for centered `μ`, polynomial `L²`
membership, and `∑_{jk} κ₃(u,e_j,e_k)² ≤ 8‖u‖²` under isotropy and the Letwin quadratic bound
(contraction argument as in `Cumulant`, whose all-radii version keeps its own provenance); the
second
cumulant of any such law is the centered second moment, i.e. the covariance pairing. A law with
compact support has every exponential moment. The log-concave adapter and the Eldan base case are
in `KLS/BKL/LocalThirdCumulant.lean`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section SecondCumulants

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private theorem second_apply {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v w : E) :
    iteratedFDeriv ℝ 2 f x ![v, w] = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [(hf.differentiableAt_iteratedFDeriv (m := 1) (by norm_num)).iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Fin.tail, Matrix.cons_val_zero, Matrix.cons_val_succ]

/- Second derivative of a product at a point where one factor vanishes and the other has value one
and
zero derivative (localized version of the argument in `Cumulant`). -/
private theorem second_mul {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (v w : E) (hf0 : f x = 0) (hg0 : g x = 1)
    (hg1 : fderiv ℝ g x = 0) :
    iteratedFDeriv ℝ 2 (fun y => f y * g y) x ![v, w] =
      iteratedFDeriv ℝ 2 f x ![v, w] := by
  have hdf := hf.fderiv_right (m := ∞) (by simp)
  have hdg := hg.fderiv_right (m := ∞) (by simp)
  have hfw : DifferentiableAt ℝ (fun y => fderiv ℝ f y w) x :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.contDiffAt.comp x hdf).differentiableAt (by simp)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ g y w) x :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.contDiffAt.comp x hdg).differentiableAt (by simp)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =ᶠ[𝓝 x]
      (fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w) := by
    have hfe := (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by norm_num)
    have hge := (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by norm_num)
    filter_upwards [hfe, hge] with y hyf hyg
    rw [fderiv_fun_mul (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))]
    simp
  rw [second_apply (hf.mul hg), second_apply hf, heq.fderiv_eq]
  rw [fderiv_fun_add (f := fun y => f y * fderiv ℝ g y w)
    (g := fun y => g y * fderiv ℝ f y w)
    ((hf.differentiableAt (by simp)).mul hgw)
    ((hg.differentiableAt (by simp)).mul hfw)]
  rw [fderiv_fun_mul (hf.differentiableAt (by simp)) hgw,
    fderiv_fun_mul (hg.differentiableAt (by simp)) hfw]
  simp [hf0, hg0, hg1]

end SecondCumulants

theorem norm_exp_weights {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
  intro t ht
  simp only [norm_one, mul_one]
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _))

theorem inner_exp_weights {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u : E) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖⟪u, x⟫‖) μ := by
  intro t ht
  have h := (weightedExpD_integrable_lt (g := fun _ : E => (1 : ℝ))
    measurable_const.aestronglyMeasurable (norm_exp_weights hexp)) t ht
  refine (h.const_mul ‖u‖).mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [weightedExpD, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
    norm_one, mul_one]
  calc
    Real.exp (t * ‖x‖) * ‖⟪u, x⟫‖ ≤ Real.exp (t * ‖x‖) * (‖u‖ * ‖x‖) := by
      gcongr
      exact norm_inner_le_norm u x
    _ = ‖u‖ * (Real.exp (t * ‖x‖) * ‖x‖) := by ring

/--
**Third cumulant of a centered law with one exponential moment**: if `∫ e^{r‖x‖} dμ < ∞` for some
`r > 0` and `μ` is centered, then `κ₃(u, v, w) = ∫ ⟪u,x⟫⟪v,x⟫⟪w,x⟫ dμ` (no global exponential
moments). -/
theorem cumulant_three_eq_integral_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
    cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
  let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • ⟪w, x⟫ ∂μ
  let F : E → ℝ := fun z => fderiv ℝ (logLaplace μ) z w
  have hz : ‖(0 : E)‖ < r := by simpa
  have hL : ContDiffAt ℝ ∞ (logLaplace μ) 0 :=
    (contDiffOn_logLaplace_ball μ hr hexp).contDiffAt (Metric.ball_mem_nhds 0 hr)
  have hF : ContDiffAt ℝ ∞ F 0 :=
    (ContinuousLinearMap.apply ℝ ℝ w).contDiff.contDiffAt.comp 0
      (hL.fderiv_right (m := ∞) (by simp))
  have hZ : ContDiffAt ℝ ∞ Z 0 :=
    (weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable
          (norm_exp_weights hexp)).contDiffAt
      (Metric.ball_mem_nhds 0 hr)
  have hZ0 : Z 0 = 1 := by simp [Z]
  have hF0 : F 0 = 0 := by
    dsimp [F]
    rw [← tiltAverage_inner_eq_fderiv_logLaplace_of_lt μ hexp hz w]
    simpa [tiltAverage, expTilt] using hc w
  have hZ1 : fderiv ℝ Z 0 = 0 := by
    ext a
    have h :=
      iteratedFDeriv_weightedExp_integral_of_lt μ (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (norm_exp_weights hexp) 1 (0 : E) hz ![a]
    have h' : fderiv ℝ Z 0 a = ∫ x, ⟪a, x⟫ ∂μ := by
      simpa [Z, iteratedFDeriv_one_apply, real_inner_comm] using h
    exact h'.trans (hc a)
  have hNZ : N =ᶠ[𝓝 0] (fun z => F z * Z z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with z hzmem
    have hz' : ‖z‖ < r := by simpa using hzmem
    have hi :=
      integrable_exp_inner_smul_of_lt μ (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (norm_exp_weights hexp) hz'
    have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 :=
      (integral_exp_pos (by simpa only [smul_eq_mul, mul_one] using hi)).ne'
    dsimp [N, F, Z]
    rw [← tiltAverage_inner_eq_fderiv_logLaplace_of_lt μ hexp hz' w]
    rw [tiltAverage, expTilt, integral_tilted]
    simp only [smul_eq_mul, mul_one, div_eq_mul_inv]
    rw [show
        (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * ⟪w, x⟫) =
          (fun x => (Real.exp ⟪z, x⟫ * ⟪w, x⟫) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹)
        by funext x; ring]
    rw [integral_mul_const]
    field_simp
  have hsecond := second_mul hF hZ u v hF0 hZ0 hZ1
  have hm :=
    iteratedFDeriv_weightedExp_integral_of_lt μ (g := fun x => ⟪w, x⟫)
      (by fun_prop : Continuous (fun x : E => ⟪w, x⟫)).aestronglyMeasurable
      (inner_exp_weights hexp w) 2 (0 : E) hz ![u, v]
  have hm' : iteratedFDeriv ℝ 2 N 0 ![u, v] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
    simpa [N, Fin.prod_univ_two, smul_eq_mul, real_inner_comm, mul_comm, mul_left_comm,
      mul_assoc] using hm
  have hNF : iteratedFDeriv ℝ 2 N 0 ![u, v] = iteratedFDeriv ℝ 2 F 0 ![u, v] := by
    rw [(hNZ.iteratedFDeriv ℝ 2).self_of_nhds]
    exact hsecond
  have hcomm :
    iteratedFDeriv ℝ 2 F 0 ![u, v] = iteratedFDeriv ℝ 2 (fderiv ℝ (logLaplace μ)) 0 ![u, v] w := by
    have H :=
      (ContinuousLinearMap.apply ℝ ℝ w).iteratedFDeriv_comp_left
        (hL.fderiv_right (m := ∞) (by simp)) (i := 2) (by norm_cast)
    exact congrArg (fun T => T ![u, v]) H
  unfold cumulant
  rw [iteratedFDeriv_succ_apply_right]
  have hinit : Fin.init ![u, v, w] = ![u, v] := by
    ext i
    fin_cases i <;> rfl
  rw [hinit]
  change iteratedFDeriv ℝ 2 (fderiv ℝ (logLaplace μ)) 0 ![u, v] w = _
  rw [← hcomm, ← hNF, hm']

section PolynomialMoments

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
private theorem norm_pow_integrable (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ}
    (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
    Integrable (fun x => ‖x‖ ^ k) μ := by
  have hneg : Integrable (fun x => Real.exp (-r * ‖x‖)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) (norm_nonneg _))
  have h := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul hr.ne' hexp hneg k
  simpa only [abs_norm] using h

/--
A continuous function with a polynomial bound is in `L²(μ)` when `μ` has one exponential moment. -/
theorem memLp_of_polynomial_bound_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → ℝ}
    (hg : Continuous g) {C : ℝ} {k : ℕ} (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) : MemLp g 2 μ := by
  apply (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
  have hi :=
    ((integrable_const (1 : ℝ)).add (norm_pow_integrable μ hr hexp (k * 2))).const_mul
      (C ^ 2 * 2 ^ (k * 2 - 1))
  refine hi.mono' (hg.pow 2).aestronglyMeasurable ?_
  filter_upwards [] with x
  calc
    ‖g x ^ 2‖ = ‖g x‖ ^ 2 := norm_pow _ _
    _ ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
    _ = C ^ 2 * (1 + ‖x‖) ^ (k * 2) := by rw [mul_pow, ← pow_mul]
    _ ≤ C ^ 2 * (2 ^ (k * 2 - 1) * (1 + ‖x‖ ^ (k * 2))) := by
      gcongr
      simpa only [one_pow] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg x) (k * 2)
    _ = (C ^ 2 * 2 ^ (k * 2 - 1)) * (1 + ‖x‖ ^ (k * 2)) := by ring

end PolynomialMoments

section ProjectionMoments

omit [FiniteDimensional ℝ E]
private theorem memLp_inner_of_local (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) :
    MemLp (fun x => ⟪v, x⟫) 2 μ := by
  apply memLp_of_polynomial_bound_of_integrable_exp μ hr hexp (by fun_prop) (C := ‖v‖) (k := 1)
  intro x
  simpa only [pow_one] using
    (norm_inner_le_norm v x).trans
      (mul_le_mul_of_nonneg_left (by linarith : ‖x‖ ≤ 1 + ‖x‖) (norm_nonneg v))

private theorem memLp_inner_mul_of_local (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v w : E) :
    MemLp (fun x => ⟪v, x⟫ * ⟪w, x⟫) 2 μ := by
  apply memLp_of_polynomial_bound_of_integrable_exp μ hr hexp (by fun_prop)
    (C := ‖v‖ * ‖w‖) (k := 2)
  intro x
  calc
    ‖⟪v, x⟫ * ⟪w, x⟫‖ ≤ (‖v‖ * ‖x‖) * (‖w‖ * ‖x‖) := by
      rw [norm_mul]
      exact mul_le_mul (norm_inner_le_norm v x) (norm_inner_le_norm w x)
        (norm_nonneg _) (by positivity)
    _ = (‖v‖ * ‖w‖) * ‖x‖ ^ 2 := by ring
    _ ≤ (‖v‖ * ‖w‖) * (1 + ‖x‖) ^ 2 := by gcongr; linarith

end ProjectionMoments

/--
**BKL Lemma 4.2, local-moment form**: for a centered isotropic law with one exponential moment and
the Letwin quadratic bound, `∑_{jk} κ₃(u, e_j, e_k)² ≤ 8‖u‖²` (the contraction argument of
`Cumulant`,
with all `L²` facts from the single radius). -/
theorem sum_sq_cumulant_three_le_of_letwin_of_integrable_exp (μ : Measure E)
    [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : LetwinQuadraticBound μ) (u : E) :
    ∑ j, ∑ k, cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by
  have hκ (v w : E) : cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ :=
    cumulant_three_eq_integral_of_integrable_exp μ hr hexp hc u v w
  simp_rw [hκ]
  exact
    sum_sq_thirdMoment_le_of_letwin μ (memLp_inner_of_local μ hr hexp)
      (memLp_inner_mul_of_local μ hr hexp) hc hiso hL u
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem sum_pair_eq_sum_tensor {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    (∑ j, ∑ k, T ![b j, b k] ^ 2) =
      ∑ J : Fin 2 → Fin m, Analysis.Tensor.coordTensor b T J ^ 2 := by
  classical
    calc
    (∑ j, ∑ k, T ![b j, b k] ^ 2) = ∑ q : Fin m × Fin m, T ![b q.1, b q.2] ^ 2 :=
      (Fintype.sum_prod_type (fun q : Fin m × Fin m => T ![b q.1, b q.2] ^ 2)).symm
    _ =
        ∑ q : Fin m × Fin m,
          Analysis.Tensor.coordTensor b T ((finTwoArrowEquiv (Fin m)).symm q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Analysis.Tensor.coordTensor_apply, finTwoArrowEquiv_symm_apply]
      have heq : (fun i => b (![q.1, q.2] i)) = ![b q.1, b q.2] := by
        ext i
        fin_cases i <;> rfl
      rw [heq]
    _ = _ :=
      (finTwoArrowEquiv (Fin m)).symm.sum_comp (fun J => Analysis.Tensor.coordTensor b T J ^ 2)

/-- The same bound in any orthonormal basis (Hilbert–Schmidt norm is basis independent). -/
theorem sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis (μ : Measure E)
    [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : LetwinQuadraticBound μ) {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ E) (u : E) :
    ∑ j, ∑ k, cumulant μ 3 ![u, b j, b k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  have hcons (a b : E) : Fin.cons u ![a, b] = ![u, a, b] := by
    ext i
    fin_cases i <;> rfl
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ := (cumulant μ 3).curryLeft u
  have hb :
    (∑ j, ∑ k, cumulant μ 3 ![u, b j, b k] ^ 2) =
      ∑ J : Fin 2 → Fin m, Analysis.Tensor.coordTensor b T J ^ 2 := by
    simpa only [T, ContinuousMultilinearMap.curryLeft_apply, hcons] using
      sum_pair_eq_sum_tensor b T
  have hs :
    (∑ j, ∑ k, cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2) =
      ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ E) T J ^ 2 := by
    simpa only [T, ContinuousMultilinearMap.curryLeft_apply, hcons] using
      sum_pair_eq_sum_tensor (stdOrthonormalBasis ℝ E) T
  rw [hb, Analysis.Tensor.sum_coordTensor_sq_eq b (stdOrthonormalBasis ℝ E) T, ← hs]
  exact sum_sq_cumulant_three_le_of_letwin_of_integrable_exp μ hr hexp hc hiso hL u

section SecondCumulant

/--
**Second cumulant from one exponential moment**: for any probability law with `∫ e^{r‖x‖} dμ < ∞`
for
some `r > 0` (no centering), `κ₂(u, v) = ∫⟪u,x⟫⟪v,x⟫ dμ − (∫⟪u,x⟫ dμ)(∫⟪v,x⟫ dμ)`. -/
theorem cumulant_two_eq_centered_moment_of_integrable_exp (μ : Measure E)
    [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u v : E) :
    cumulant μ 2 ![u, v] = (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ) - (∫ x, ⟪u, x⟫ ∂μ) * (∫ x, ⟪v, x⟫ ∂μ) := by
  let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • ⟪v, x⟫ ∂μ
  let F : E → ℝ := fun z => fderiv ℝ (logLaplace μ) z v
  have hz : ‖(0 : E)‖ < r := by simpa
  have hL : ContDiffAt ℝ ∞ (logLaplace μ) 0 :=
    (contDiffOn_logLaplace_ball μ hr hexp).contDiffAt (Metric.ball_mem_nhds 0 hr)
  have hF : ContDiffAt ℝ ∞ F 0 :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.comp 0
      (hL.fderiv_right (m := ∞) (by simp))
  have hZ : ContDiffAt ℝ ∞ Z 0 :=
    (weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable
          (norm_exp_weights hexp)).contDiffAt
      (Metric.ball_mem_nhds 0 hr)
  have hZ0 : Z 0 = 1 := by simp [Z]
  have hF0 : F 0 = ∫ x, ⟪v, x⟫ ∂μ := by
    dsimp [F]
    rw [← tiltAverage_inner_eq_fderiv_logLaplace_of_lt μ hexp hz v]
    simp [tiltAverage, expTilt]
  have hZ1 : fderiv ℝ Z 0 u = ∫ x, ⟪u, x⟫ ∂μ := by
    have h :=
      iteratedFDeriv_weightedExp_integral_of_lt μ (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (norm_exp_weights hexp) 1 (0 : E) hz ![u]
    simpa [Z, iteratedFDeriv_one_apply, real_inner_comm] using h
  have hN1 : fderiv ℝ N 0 u = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ := by
    have h :=
      iteratedFDeriv_weightedExp_integral_of_lt μ (g := fun x => ⟪v, x⟫)
        (by fun_prop : Continuous (fun x : E => ⟪v, x⟫)).aestronglyMeasurable
        (inner_exp_weights hexp v) 1 (0 : E) hz ![u]
    simpa [N, iteratedFDeriv_one_apply, smul_eq_mul, real_inner_comm] using h
  have hNZ : N =ᶠ[𝓝 0] (fun z => F z * Z z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with z hzmem
    have hz' : ‖z‖ < r := by simpa using hzmem
    have hi :=
      integrable_exp_inner_smul_of_lt μ (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (norm_exp_weights hexp) hz'
    have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 :=
      (integral_exp_pos (by simpa only [smul_eq_mul, mul_one] using hi)).ne'
    dsimp [N, F, Z]
    rw [← tiltAverage_inner_eq_fderiv_logLaplace_of_lt μ hexp hz' v]
    rw [tiltAverage, expTilt, integral_tilted]
    simp only [smul_eq_mul, mul_one, div_eq_mul_inv]
    rw [show
        (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * ⟪v, x⟫) =
          (fun x => (Real.exp ⟪z, x⟫ * ⟪v, x⟫) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹)
        by funext x; ring]
    rw [integral_mul_const]
    field_simp
  have hD := congrArg (fun L : E →L[ℝ] ℝ => L u) hNZ.fderiv_eq
  rw [fderiv_fun_mul (hF.differentiableAt (by simp)) (hZ.differentiableAt (by simp))] at hD
  simp only [add_apply, smul_apply, smul_eq_mul] at hD
  rw [hF0, hZ1, hZ0, one_mul, hN1] at hD
  change iteratedFDeriv ℝ 2 (logLaplace μ) 0 ![u, v] = _
  rw [second_apply hL]
  change fderiv ℝ F 0 u = _
  nlinarith

/-- One exponential moment gives `id ∈ L²(μ)`. -/
theorem memLp_id_two_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    MemLp id 2 μ := by
  have hn : MemLp (fun x : E => ‖x‖) 2 μ := by
    apply memLp_of_polynomial_bound_of_integrable_exp μ hr hexp continuous_norm (C := 1) (k := 1)
    intro x
    simp only [norm_norm, pow_one, one_mul]
    linarith
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn

/-- The second cumulant is the covariance pairing `⟪Cov(μ) u, v⟫`. -/
theorem cumulant_two_eq_covariance_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u v : E) :
    cumulant μ 2 ![u, v] = ⟪Covariance.operator μ u, v⟫ := by
  have h2 := memLp_id_two_of_integrable_exp μ hr hexp
  have hX : MemLp (fun x => ⟪u, x⟫) 2 μ := by
    simpa only [id_eq] using h2.const_inner (𝕜 := ℝ) u
  have hY : MemLp (fun x => ⟪v, x⟫) 2 μ := by
    simpa only [id_eq] using h2.const_inner (𝕜 := ℝ) v
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_apply_eq_cov h2,
    ProbabilityTheory.covariance_eq_sub hX hY]
  exact cumulant_two_eq_centered_moment_of_integrable_exp μ hr hexp u v

end SecondCumulant

section CompactSupport

/-! The compact-support moment lemmas are stated for a finite-dimensional normed space (no inner
product). -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- A law with compact support has every exponential moment. -/
theorem compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)

theorem compact_support_memLp_poly (μ : Measure F) [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {g : F → ℝ} (hg : Continuous g) {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) : MemLp g 2 μ :=
  memLp_of_polynomial_bound_of_integrable_exp μ (by norm_num : (0 : ℝ) < 1)
    (compact_support_integrable_exp μ hc 1) hg hb

theorem compact_support_integrable_norm_pow (μ : Measure F) [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) (k : ℕ) : Integrable (fun x => ‖x‖ ^ k) μ := by
  have hLp : MemLp (fun x => ‖x‖ ^ k) 2 μ := by
    apply compact_support_memLp_poly μ hc (by fun_prop) (C := 1) (k := k)
    intro x
    simp only [norm_pow, norm_norm, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
  exact hLp.integrable (by norm_num)

end CompactSupport

section GradientJets

/-! BKL arXiv:2610.05474v1, p. 20, the sentence before (74): for `Λ = logLaplace μ` of a compactly
supported law
and `v(z) = ∇Λ(z) − ∇Λ(0)`, `v(0) = 0`, `Dv(0) = A` (the covariance) and, for every `r ≥ 1`,
`Dʳv(0)[h] = cumulantVector μ (List.ofFn h)`, i.e. `⟪Dʳv(0)[h], w⟫ = κ_{r+1}(h, w)` (generic
supports in
`Analysis/IteratedDerivative/GradientJet.lean`).
-/

/--
The Riesz vector of the last slot of the scalar cumulant of order `hs.length + 1`, the first slots
being the
list `hs` (inherited order): `⟪cumulantVector μ hs, w⟫ = κ_{|hs|+1}(hs, w)`. -/
noncomputable def cumulantVector (μ : Measure E) (hs : List E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    ((cumulant μ (hs.length + 1)).curryRight (fun i => hs.get i))

omit [BorelSpace E] in
/-- Literal scalar-cumulant meaning of `cumulantVector`. -/
theorem cumulantVector_inner (μ : Measure E) (hs : List E) (w : E) :
    ⟪cumulantVector μ hs, w⟫ =
      cumulant μ (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by
  rw [cumulantVector, InnerProductSpace.toDual_symm_apply,
    ContinuousMultilinearMap.curryRight_apply]

/--
**CGF gradient at zero is the mean**: for a compactly supported probability law, `∇Λ(0) = ∫ x dμ`.
-/
theorem gradient_logLaplace_zero_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    gradient (logLaplace (μ : Measure E)) 0 = ∫ x, x ∂(μ : Measure E) := by
  have hexp : ∀ r : ℝ, Integrable (fun x : E => Real.exp (r * ‖x‖)) (μ : Measure E) :=
    compact_support_integrable_exp _ hc
  have hid : Integrable (id : E → E) (μ : Measure E) := by
    refine (hexp 1).mono' measurable_id.aestronglyMeasurable ?_
    filter_upwards [] with x
    have h : ‖x‖ ≤ Real.exp ‖x‖ := by
      calc
        ‖x‖ ≤ ‖x‖ + 1 := by linarith [norm_nonneg x]
        _ ≤ Real.exp ‖x‖ := Real.add_one_le_exp ‖x‖
    simpa using h
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  rw [fderiv_logLaplace_zero_apply (μ := (μ : Measure E)) (hexp := hexp) v]
  rw [real_inner_comm v (∫ x, x ∂(μ : Measure E))]
  simpa using integral_inner hid v

/--
**`Dv(0) = A`**: the derivative at zero of the centred CGF gradient is the covariance operator. -/
theorem fderiv_centeredGradient_logLaplace_zero_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    fderiv ℝ
        (fun z : E =>
          gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)
        0 =
      Covariance.operator (μ : Measure E) := by
  let Λ : E → ℝ := logLaplace (μ : Measure E)
  have hΛ : ContDiff ℝ ∞ Λ := by
    dsimp [Λ]
    exact contDiff_logLaplace _ (compact_support_integrable_exp _ hc)
  have hΛ' : ContDiff ℝ 1 (fderiv ℝ Λ) := by
    apply hΛ.fderiv_right
    exact WithTop.coe_le_coe.mpr le_top
  have hfd : DifferentiableAt ℝ (fderiv ℝ Λ) 0 :=
    (hΛ'.differentiable (by norm_num)).differentiableAt
  let L : (E →L[ℝ] ℝ) →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
  have hgrad : gradient Λ = fun x => L (fderiv ℝ Λ x) := by
    funext x
    rfl
  have hg : HasFDerivAt (fun x => L (fderiv ℝ Λ x)) (L.comp (fderiv ℝ (fderiv ℝ Λ) 0)) 0 := by
    convert L.hasFDerivAt.comp 0 hfd.hasFDerivAt using 1
    simp [Function.comp_def]
  change
    fderiv ℝ (fun z : E => gradient Λ z - gradient Λ 0) 0 = Covariance.operator (μ : Measure E)
  rw [fderiv_sub_const, hgrad, hg.fderiv]
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro w
  change
    ⟪(InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ (fderiv ℝ Λ) 0) u), w⟫ =
      ⟪Covariance.operator (μ : Measure E) u, w⟫
  rw [InnerProductSpace.toDual_symm_apply]
  have hiter : ((fderiv ℝ (fderiv ℝ Λ) 0) u) w = iteratedFDeriv ℝ 2 Λ 0 ![u, w] := by
    simpa using (iteratedFDeriv_two_apply (𝕜 := ℝ) (f := Λ) (z := 0) (m := ![u, w])).symm
  rw [hiter]
  change cumulant (μ : Measure E) 2 ![u, w] = ⟪Covariance.operator (μ : Measure E) u, w⟫
  exact
    cumulant_two_eq_covariance_of_integrable_exp (μ := (μ : Measure E)) (hr := one_pos)
      (compact_support_integrable_exp _ hc 1) u w

/-- **Jets of the centred CGF gradient are the cumulant Riesz vectors**: for `r ≥ 1`,
`Dʳ(∇Λ − ∇Λ(0))(0)[h] = cumulantVector μ (List.ofFn h)`, i.e. `⟪Dʳv(0)[h], w⟫ = κ_{r+1}(h, w)`. -/
theorem iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (r : ℕ) (hr : 1 ≤ r) (h : Fin r → E) :
    iteratedFDeriv ℝ r (fun z : E =>
      gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0) 0 h =
      cumulantVector (μ : Measure E) (List.ofFn h) := by
    have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
    let Λ : E → ℝ := logLaplace (μ : Measure E)
    have hΛ : ContDiff ℝ ∞ Λ := by
      dsimp [Λ]
      exact contDiff_logLaplace _ (compact_support_integrable_exp _ hc)
    have hg : ContDiff ℝ ∞ (gradient Λ) := by
      change ContDiff ℝ ∞
        ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ Λ)
      exact
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
          (hΛ.fderiv_right (by simp))
    change
      iteratedFDeriv ℝ r
          (fun z : E => gradient Λ z - gradient Λ 0) 0 h =
        cumulantVector (μ : Measure E) (List.ofFn h)
    rw [iteratedFDeriv_sub_const_of_pos hg (gradient Λ 0) hr 0]
    apply ext_inner_right ℝ
    intro w
    rw [inner_iteratedFDeriv_gradient_apply hΛ r 0 h w,
      cumulantVector_inner]
    have haux :
        ∀ (n : ℕ) (hn : n = r) (g : Fin n → E),
          (∀ i, g i = h (Fin.cast hn i)) →
            cumulant (μ : Measure E) (n + 1) (Fin.snoc g w) =
              iteratedFDeriv ℝ (r + 1) Λ 0 (Fin.snoc h w) := by
      intro n hn g hg'
      subst n
      have hgeq : g = h := by
        funext i
        simpa using hg' i
      unfold cumulant
      dsimp [Λ]
      rw [hgeq]
    symm
    exact
      haux (List.ofFn h).length List.length_ofFn
        (fun i => (List.ofFn h).get i)
        (fun i => by
          simpa using (List.get_ofFn h i))

end GradientJets

section SingletonAllocation

/--
**Singleton allocation of (74)** (BKL arXiv:2610.05474v1, p. 21): for a compactly supported law
whose covariance
`A` is a unit, `⟪κ₂(w,·), A⁻¹ κ_{|hs|+1}(hs,·)⟫ = κ_{|hs|+1}(hs, w)`, the order-`(|hs|+1)` cumulant
with `w` in the
last slot. -/
theorem inner_cumulantVector_single_ringInverse_cumulantVector (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hA : IsUnit (Covariance.operator (μ : Measure E)))
    (hs : List E) (w : E) :
    ⟪cumulantVector (μ : Measure E) [w],
        Ring.inverse (Covariance.operator (μ : Measure E))
          (cumulantVector (μ : Measure E) hs)⟫ =
      cumulant (μ : Measure E) (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by
  have hA2 : cumulantVector (μ : Measure E) [w] = Covariance.operator (μ : Measure E) w := by
    apply ext_inner_right ℝ
    intro u
    rw [cumulantVector_inner]
    have hv : Fin.snoc (fun i => [w].get i) u = ![w, u] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change cumulant (μ : Measure E) 2 (![w, u]) = ⟪Covariance.operator (μ : Measure E) w, u⟫
    rw [cumulant_two_eq_covariance_of_integrable_exp (μ := μ) (hr := one_pos)
        (compact_support_integrable_exp _ hc 1) w u]
  have hsa : IsSelfAdjoint (Covariance.operator (μ : Measure E)) :=
    Covariance.operator_isSelfAdjoint (μ : Measure E)
  have hsymm (x y : E) :
    ⟪Covariance.operator (μ : Measure E) x, y⟫ = ⟪x, Covariance.operator (μ : Measure E) y⟫ := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) x y
  have hunit (u : E) :
    Covariance.operator (μ : Measure E) (Ring.inverse (Covariance.operator (μ : Measure E)) u) =
      u := by
    have h :=
      congrArg (fun T : E →L[ℝ] E => T u)
        (Ring.mul_inverse_cancel (Covariance.operator (μ : Measure E)) hA)
    simpa using h
  calc
    ⟪cumulantVector (μ : Measure E) [w],
          Ring.inverse (Covariance.operator (μ : Measure E))
            (cumulantVector (μ : Measure E) hs)⟫ =
        ⟪Covariance.operator (μ : Measure E) w,
          Ring.inverse (Covariance.operator (μ : Measure E))
            (cumulantVector (μ : Measure E) hs)⟫ := by
      rw [hA2]
    _ =
        ⟪w,
          Covariance.operator (μ : Measure E)
            (Ring.inverse (Covariance.operator (μ : Measure E))
              (cumulantVector (μ : Measure E) hs))⟫ := by
      exact
        hsymm w
          (Ring.inverse (Covariance.operator (μ : Measure E))
            (cumulantVector (μ : Measure E) hs))
    _ = ⟪w, cumulantVector (μ : Measure E) hs⟫ := by rw [hunit]
    _ = ⟪cumulantVector (μ : Measure E) hs, w⟫ := by rw [real_inner_comm]
    _ = cumulant (μ : Measure E) (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by
      rw [cumulantVector_inner]

end SingletonAllocation

section CumulantSymmetry

/--
The cumulant tensors of a compactly supported law are symmetric: `κ_m(h ∘ σ) = κ_m(h)` for every
permutation `σ`. -/
theorem cumulant_comp_perm_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : Fin m → E) :
    cumulant (μ : Measure E) m (h ∘ σ) = cumulant (μ : Measure E) m h := by
  have hΛ : ContDiff ℝ ∞ (logLaplace (μ : Measure E)) :=
    contDiff_logLaplace _ (compact_support_integrable_exp _ hc)
  simp only [cumulant]
  exact iteratedFDeriv_perm hΛ m h σ 0

end CumulantSymmetry

end FunctionalInequalities.Analysis.BakryEmery
