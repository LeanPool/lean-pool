/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.CompactQuadratic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Local
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Generator of the BKL posterior expectation (deterministic core of (68))

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67)–(68), compact-prior stage: the posterior
expectation `(c, Q) ↦ ∫ f dμ_{c,Q}` of a measurable `f` bounded on the support is `C^∞` in `c`, its
`c`-gradient is `Cov(f, ⟪h,x⟫)`, its `c`-Hessian is a covariance expression, its `Q`-derivative in a
direction `M` is `−½ Cov(f, ⟪Mx,x⟫)`, and for every symmetric `M` the generator combination
`D_c[M a] + ∂_Q[M] + ½ tr_M D²_c` vanishes. Instantiating `M = Cov(μ_{c,Q})⁻¹` is the deterministic
content of the zero drift in (68); no stochastic process, Itô formula or martingale is constructed.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Probability.Posterior

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The expectation `∫ f dμ_{c,Q}` of `f` under the posterior with parameters `(c, Q)`. -/
def posteriorExpectation (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) (f : E → ℝ) : ℝ :=
  ∫ x, f x ∂((μ : Measure E).tilted (quadraticExponent c Q))

/--
Under a compact prior, `e^{s‖x‖} ‖e^{E_{0,Q}} f‖` is integrable for every `s` (bounded `f` on the
support). -/
theorem integrable_exp_norm_mul_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (_hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) (s : ℝ) :
    Integrable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (quadraticExponent 0 Q x) * f x‖)
      (μ : Measure E) := by
  have hφ : Continuous (quadraticExponent (0 : E) Q) := by unfold quadraticExponent; fun_prop
  obtain ⟨P, _hP, hp⟩ := exists_bound_on_support_of_compact μ hc hφ
  obtain ⟨R, _hR, hR⟩ :=
    exists_bound_on_support_of_compact μ hc (continuous_norm : Continuous (fun x : E => ‖x‖))
  have hmeas :
    Measurable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (quadraticExponent 0 Q x) * f x‖) :=
    ((Real.continuous_exp.comp (continuous_norm.const_mul s)).measurable).mul
      (((Real.continuous_exp.comp hφ).measurable.mul hf).norm)
  apply integrable_of_bound_on_support μ hmeas (Real.exp (|s| * R + P) * C)
  intro x hx
  have hnorm : ‖x‖ ≤ R := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using hR x hx
  have hleft : s * ‖x‖ ≤ |s| * R :=
    (mul_le_mul_of_nonneg_right (le_abs_self s) (norm_nonneg x)).trans
      (mul_le_mul_of_nonneg_left hnorm (abs_nonneg s))
  have hright : quadraticExponent 0 Q x ≤ P :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hp x hx)
  change
    ‖Real.exp (s * ‖x‖) * ‖Real.exp (quadraticExponent 0 Q x) * f x‖‖ ≤
      Real.exp (|s| * R + P) * C
  rw [norm_mul, norm_norm, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
  exact
    mul_le_mul (Real.exp_le_exp.mpr (add_le_add hleft hright)) (hfb x hx) (norm_nonneg _)
      (Real.exp_nonneg _)

/--
The unnormalized integral `c ↦ ∫ e^{E_{c,Q}} f dμ` is `C^∞` under a compact prior (weighted-integral
smoothness inside every exponential radius). -/
theorem contDiff_weighted_integral_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞
      (fun c : E => ∫ x, Real.exp (quadraticExponent c Q x) * f x ∂(μ : Measure E)) := by
  let g : E → ℝ := fun x => Real.exp (quadraticExponent 0 Q x) * f x
  have hp : Continuous (quadraticExponent (0 : E) Q) := by unfold quadraticExponent; fun_prop
  have hg : AEStronglyMeasurable g (μ : Measure E) :=
    (Real.continuous_exp.comp hp).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hi (s : ℝ) : Integrable (fun x => Real.exp (s * ‖x‖) * ‖g x‖) (μ : Measure E) :=
    integrable_exp_norm_mul_of_compact μ hc hf hC hfb Q s
  have hs : ContDiff ℝ ∞ (fun c : E => ∫ x, Real.exp ⟪c, x⟫ • g x ∂(μ : Measure E)) := by
    rw [contDiff_iff_contDiffAt]
    intro c
    have hon :=
      weighted_integral_contDiffOn (μ : Measure E) hg (r := ‖c‖ + 1) (fun s _hs => hi s)
    apply hon.contDiffAt
    exact
      Metric.isOpen_ball.mem_nhds
        (by simpa only [Metric.mem_ball, dist_zero_right] using (lt_add_one ‖c‖))
  have heq :
    (fun c : E => ∫ x, Real.exp ⟪c, x⟫ • g x ∂(μ : Measure E)) = fun c =>
      ∫ x, Real.exp (quadraticExponent c Q x) * f x ∂(μ : Measure E) := by
    funext c
    congr 1
    funext x
    dsimp [g]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [quadraticExponent, inner_zero_left, zero_sub]
    ring
  rw [heq] at hs
  exact hs

/-- The posterior expectation is `C^∞` in `c` at every fixed `Q`, including `Q = 0`. -/
theorem contDiff_posteriorExpectation_c (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞ (fun c => posteriorExpectation μ c Q f) := by
  have hN := contDiff_weighted_integral_quadraticExponent_of_compact μ hc hf hC hfb Q
  have hZ :=
    contDiff_weighted_integral_quadraticExponent_of_compact μ hc (f := fun _ => (1 : ℝ))
      measurable_const (C := 1) (by norm_num) (by intro x hx; simp) Q
  simp only [mul_one] at hZ
  have hpos (c : E) : (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E)) ≠ 0 := by
    apply (integral_exp_pos (integrable_exp_of_compact μ hc ?_)).ne'
    unfold quadraticExponent
    fun_prop
  have heq :
    (fun c => posteriorExpectation μ c Q f) = fun c =>
      (∫ x, Real.exp (quadraticExponent c Q x) * f x ∂(μ : Measure E)) /
        ∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E) := by
    funext c
    exact integral_tilted_eq_div μ _ _
  rw [heq]
  exact hN.div hZ hpos

/-- The `c`-gradient of the posterior expectation is the covariance with the linear score. -/
theorem fderiv_posteriorExpectation_c_apply (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h : E) :
    fderiv ℝ (fun y => posteriorExpectation μ y Q f) c h =
      covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  have hsm := contDiff_posteriorExpectation_c μ hc hf hC hfb Q
  have hsm2 : ContDiff ℝ 2 (fun y => posteriorExpectation μ y Q f) :=
    hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hD := (hsm2.differentiable (by norm_num) c).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_line c h 0) (by simp)
  have hN := expectation_hasDerivAt_quadraticExponent_of_compact μ hc c h Q 0 hf hC hfb
  have hg : quadraticExponent h (0 : E →L[ℝ] E) = fun x => ⟪h, x⟫ := by
    funext x
    simp [quadraticExponent]
  have hN' : HasDerivAt (fun t : ℝ => posteriorExpectation μ (c + t • h) Q f)
      (covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q))) 0 := by
    simpa only [posteriorExpectation, smul_zero, add_zero, hg] using hN
  exact hD.unique hN'

/--
The `c`-Hessian of the posterior expectation: `Cov(f, ⟪h,x⟫⟪k,x⟫) − (∫⟪h,x⟫) Cov(f,⟪k,x⟫) − (∫⟪k,x⟫)
Cov(f,⟪h,x⟫)`. -/
theorem bilinearIteratedFDerivTwo_posteriorExpectation_c (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q : E →L[ℝ] E)
    (h k : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c h k =
      covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
          (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
            covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        (∫ x, ⟪k, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
          covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  have hsm := contDiff_posteriorExpectation_c μ hc hf hC hfb Q
  have hsm2 : ContDiff ℝ 2 (fun y => posteriorExpectation μ y Q f) :=
    hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hsm2]
  have hD :=
    (differentiable_fderiv_apply hsm2 k c).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_line c h 0) (by simp)
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  have hh : Continuous (fun x : E => ⟪h, x⟫) := by fun_prop
  have hk : Continuous (fun x : E => ⟪k, x⟫) := by fun_prop
  have hN := covariance_hasDerivAt_of_compact μ hc hφ hh hk hf hC hfb
  have hphase (t : ℝ) :
    quadraticExponent (c + t • h) Q = fun x => quadraticExponent c Q x + t * ⟪h, x⟫ := by
    funext x
    simp only [quadraticExponent, inner_add_left, real_inner_smul_left]
    ring
  have hfun :
    (fun y => fderiv ℝ (fun z => posteriorExpectation μ z Q f) y k) = fun y =>
      covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent y Q)) := by
    funext y
    exact fderiv_posteriorExpectation_c_apply μ hc hf hC hfb y Q k
  have hD' := hD
  simp only [Function.comp_def, hfun, hphase] at hD'
  simpa only [hfun] using hD'.unique hN


end Smooth

section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


/-- The mean `a = ∫ x dμ_{c,Q}` of the posterior. -/
def posteriorMean (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E) : E :=
  ∫ x, x ∂((μ : Measure E).tilted (quadraticExponent c Q))

/-- `∫ ⟪h, x⟫ dμ_{c,Q} = ⟪h, a⟫` (finite second moment from compact support). -/
theorem integral_inner_eq_inner_posteriorMean (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) =
      ⟪h, posteriorMean μ c Q⟫ := by
  obtain ⟨R, _hR, hmom⟩ := exists_uniform_norm_moments_tilted_quadraticExponent_of_compact μ hc
  let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  have h2 : MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr (hmom c Q 2).1
  have hi := h2.integrable one_le_two
  change
    (∫ x, (innerSL ℝ h) (id x) ∂((μ : Measure E).tilted (quadraticExponent c Q))) =
      (innerSL ℝ h) (∫ x, id x ∂((μ : Measure E).tilted (quadraticExponent c Q)))
  exact (innerSL ℝ h).integral_comp_comm hi

/-- The `c`-Hessian written with the posterior mean. -/
theorem bilinearIteratedFDerivTwo_posteriorExpectation_c_mean (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q : E →L[ℝ] E)
    (h k : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c h k =
      covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
          ⟪h, posteriorMean μ c Q⟫ *
            covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        ⟪k, posteriorMean μ c Q⟫ *
          covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  rw [bilinearIteratedFDerivTwo_posteriorExpectation_c μ hc hf hC hfb,
    integral_inner_eq_inner_posteriorMean μ hc c Q h,
    integral_inner_eq_inner_posteriorMean μ hc c Q k]


variable {ι : Type*} [Fintype ι]

/--
**Trace of the `c`-Hessian against a symmetric `M`**: `Σ_i D²_c(f)[M e_i, e_i] = Cov(f, ⟪Mx,x⟫) − 2
Cov(f, ⟪M a, x⟫)`
in any orthonormal basis. -/
theorem sum_bilinearIteratedFDerivTwo_posteriorExpectation_c (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q M : E →L[ℝ] E)
    (b : OrthonormalBasis ι ℝ E) (hM : ∀ u v : E, ⟪M u, v⟫ = ⟪u, M v⟫) :
    (∑ i,
        bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (b i)) (b i)) =
      covariance f (fun x => ⟪M x, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        2 *
          covariance f (fun x => ⟪M (posteriorMean μ c Q), x⟫)
            ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  let ν : Measure E := (μ : Measure E).tilted (quadraticExponent c Q)
  let a : E := posteriorMean μ c Q
  let : IsProbabilityMeasure ν :=
    isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  have hF2 : MemLp f 2 ν := memLp_two_tilted_of_compact μ hc hφ hf hfb
  have hL2 (g : E → ℝ) (hg : Continuous g) : MemLp g 2 ν :=
    memLp_two_tilted_quadraticExponent_of_compact μ hc c Q hg
  have hs1 :
    (∑ i, covariance f (fun x : E => ⟪M (b i), x⟫ * ⟪b i, x⟫) ν) =
      covariance f (fun x => ⟪M x, x⟫) ν := by
    rw [← covariance_fun_sum_right (fun i => hL2 _ (by fun_prop)) hF2]
    congr 1
    funext x
    calc
      ∑ i, ⟪M (b i), x⟫ * ⟪b i, x⟫ = ∑ i, ⟪M (⟪b i, x⟫ • b i), x⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_smul, real_inner_smul_left]
        ring
      _ = ⟪M (∑ i, ⟪b i, x⟫ • b i), x⟫ := by rw [map_sum, sum_inner]
      _ = ⟪M x, x⟫ := by rw [b.sum_repr' x]
  have hs2 :
    (∑ i, ⟪M (b i), a⟫ * covariance f (fun x : E => ⟪b i, x⟫) ν) =
      covariance f (fun x => ⟪M a, x⟫) ν := by
    simp_rw [← covariance_const_mul_right]
    rw [← covariance_fun_sum_right (fun i => hL2 _ (by fun_prop)) hF2]
    congr 1
    funext x
    calc
      (∑ i, ⟪M (b i), a⟫ * ⟪b i, x⟫) = ∑ i, ⟪M a, b i⟫ * ⟪b i, x⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hM (b i) a, real_inner_comm (b i) (M a)]
      _ = ⟪M a, x⟫ := b.sum_inner_mul_inner (M a) x
  have hs3 :
    (∑ i, ⟪b i, a⟫ * covariance f (fun x : E => ⟪M (b i), x⟫) ν) =
      covariance f (fun x => ⟪M a, x⟫) ν := by
    simp_rw [← covariance_const_mul_right]
    rw [← covariance_fun_sum_right (fun i => hL2 _ (by fun_prop)) hF2]
    congr 1
    funext x
    calc
      ∑ i, ⟪b i, a⟫ * ⟪M (b i), x⟫ = ∑ i, ⟪M (⟪b i, a⟫ • b i), x⟫ := by
        simp only [map_smul, real_inner_smul_left]
      _ = ⟪M (∑ i, ⟪b i, a⟫ • b i), x⟫ := by rw [map_sum, sum_inner]
      _ = ⟪M a, x⟫ := by rw [b.sum_repr' a]
  simp_rw [bilinearIteratedFDerivTwo_posteriorExpectation_c_mean μ hc hf hC hfb]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  change
    (∑ i, covariance f (fun x : E => ⟪M (b i), x⟫ * ⟪b i, x⟫) ν) -
          (∑ i, ⟪M (b i), a⟫ * covariance f (fun x : E => ⟪b i, x⟫) ν) -
        (∑ i, ⟪b i, a⟫ * covariance f (fun x : E => ⟪M (b i), x⟫) ν) =
      _
  rw [hs1, hs2, hs3]
  ring

omit [CompleteSpace E] in
/-- The `Q`-derivative of the posterior expectation in direction `M` is `−½ Cov(f, ⟪Mx,x⟫)`. -/
theorem posteriorExpectation_hasDerivAt_Q (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q M : E →L[ℝ] E) :
    HasDerivAt (fun t : ℝ => posteriorExpectation μ c (Q + t • M) f)
      (-(1 / 2 : ℝ) *
        covariance f (fun x => ⟪M x, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)))
      0 := by
  have hd := expectation_hasDerivAt_quadraticExponent_of_compact μ hc c 0 Q M hf hC hfb
  have hscore : quadraticExponent (0 : E) M = fun x => -(1 / 2 : ℝ) * ⟪M x, x⟫ := by
    funext x
    simp only [quadraticExponent, inner_zero_left]
    ring
  simpa only [posteriorExpectation, smul_zero, add_zero, hscore,
    covariance_const_mul_right] using hd

/--
**Generator cancellation (deterministic core of BKL (68))**: for every symmetric `M`, the three
terms
`D_c(f)[M a] + ∂_Q(f)[M] + ½ Σ_i D²_c(f)[M e_i, e_i]` vanish. With `M = Cov(μ_{c,Q})⁻¹` this is the
statement that the drift of `∫ f dμ_t` along (67) is zero; the stochastic equation itself is not
constructed here. -/
theorem posteriorExpectation_generator_cancellation (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q M : E →L[ℝ] E)
    (b : OrthonormalBasis ι ℝ E) (hM : ∀ u v : E, ⟪M u, v⟫ = ⟪u, M v⟫) :
    fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (M (posteriorMean μ c Q)) +
          deriv (fun t : ℝ => posteriorExpectation μ c (Q + t • M) f) 0 +
        (1 / 2 : ℝ) *
          (∑ i,
            bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (b i))
              (b i)) =
      0 := by
  rw [fderiv_posteriorExpectation_c_apply μ hc hf hC hfb,
    (posteriorExpectation_hasDerivAt_Q μ hc hf hC hfb c Q M).deriv,
    sum_bilinearIteratedFDerivTwo_posteriorExpectation_c μ hc hf hC hfb c Q M b hM]
  ring

end Mean

end FunctionalInequalities.Probability.Posterior
