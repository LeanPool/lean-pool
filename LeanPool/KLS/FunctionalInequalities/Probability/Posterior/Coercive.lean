/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.Exponent
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Probability.Moments.Covariance

/-!
# The BKL posterior under a coercive quadratic parameter

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67): when `⟪Q x, x⟫ ≥ a‖x‖²` with `a > 0`, the
quadratic damping of the exponent `⟪c, x⟫ − ½⟪Q x, x⟫` dominates every polynomially weighted
exponential
on a parameter neighbourhood, so for an arbitrary probability prior (no moment assumption) the
posterior
is a probability law, polynomially growing statistics are in `L²`, and the posterior expectation has
the
covariance derivative along any signed parameter line `(c + t h, Q + t H)`. The source initial stage
`Q = 0` is not coercive in positive dimension (in dimension zero coercivity holds vacuously) and is
handled by the compact-prior modules. No stochastic process, Itô formula
or (68)–(71) is constructed.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Posterior

section Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
**Uniform domination on a parameter neighbourhood**: if `⟪Q x, x⟫ ≥ a‖x‖²` with `a > 0`, then for
`|t| < δ = a/(2(1+‖H‖))` the weights `e^{E_{c+th,Q+tH}(x)} (1+‖x‖)^k` are bounded uniformly in `x`
(any signed directions `h, H`). -/
theorem exists_uniform_polynomial_bound (c h : E) (Q H : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫) (k : ℕ) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ M : ℝ,
          0 < M ∧
            ∀ t : ℝ,
              |t| < δ →
                ∀ x : E,
                  Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * (1 + ‖x‖) ^ k ≤ M := by
  let δ : ℝ := a / (2 * (1 + ‖H‖))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let D : ℝ := ‖c‖ + δ * ‖h‖ + k
  refine ⟨δ, hδ, Real.exp (D ^ 2 / a), Real.exp_pos _, ?_⟩
  intro t ht x
  have hd : δ * (1 + ‖H‖) = a / 2 := by
    dsimp [δ]
    field_simp
  have htH : |t| * ‖H‖ ≤ a / 2 := by
    have h1 : |t| * ‖H‖ ≤ δ * ‖H‖ := mul_le_mul_of_nonneg_right ht.le (norm_nonneg H)
    nlinarith [mul_nonneg hδ.le (norm_nonneg H)]
  have hH : |⟪H x, x⟫| ≤ ‖H‖ * ‖x‖ ^ 2 := by
    calc
      |⟪H x, x⟫| ≤ ‖H x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (H.le_opNorm x) (norm_nonneg x)
      _ = ‖H‖ * ‖x‖ ^ 2 := by ring
  have hpert : |t * ⟪H x, x⟫| ≤ (a / 2) * ‖x‖ ^ 2 := by
    rw [abs_mul]
    calc
      |t| * |⟪H x, x⟫| ≤ |t| * (‖H‖ * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hH (abs_nonneg t)
      _ = (|t| * ‖H‖) * ‖x‖ ^ 2 := by ring
      _ ≤ (a / 2) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right htH (sq_nonneg _)
  have hquad : (a / 2) * ‖x‖ ^ 2 ≤ ⟪(Q + t • H) x, x⟫ := by
    simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left]
    nlinarith [hQ x, neg_abs_le (t * ⟪H x, x⟫)]
  have hlinear : ⟪c + t • h, x⟫ ≤ (‖c‖ + δ * ‖h‖) * ‖x‖ := by
    calc
      ⟪c + t • h, x⟫ ≤ ‖c + t • h‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (‖c‖ + |t| * ‖h‖) * ‖x‖ := by
        gcongr
        simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le c (t • h)
      _ ≤ (‖c‖ + δ * ‖h‖) * ‖x‖ := by gcongr
  have hpot :
    quadraticExponent (c + t • h) (Q + t • H) x + k * ‖x‖ ≤ D * ‖x‖ - (a / 4) * ‖x‖ ^ 2 := by
    dsimp [quadraticExponent, D]
    nlinarith
  have hmax : D * ‖x‖ - (a / 4) * ‖x‖ ^ 2 ≤ D ^ 2 / a := by
    apply (mul_le_mul_iff_right₀ ha).mp
    have heq : a * (D ^ 2 / a) = D ^ 2 := by field_simp
    rw [heq]
    nlinarith [sq_nonneg (a * ‖x‖ - 2 * D)]
  have hpow : (1 + ‖x‖) ^ k ≤ Real.exp (k * ‖x‖) := by
    rw [Real.exp_nat_mul]
    gcongr
    simpa only [add_comm] using Real.add_one_le_exp ‖x‖
  calc
    Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * (1 + ‖x‖) ^ k ≤
        Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * Real.exp (k * ‖x‖) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp (quadraticExponent (c + t • h) (Q + t • H) x + k * ‖x‖) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (D ^ 2 / a) := Real.exp_le_exp.mpr (hpot.trans hmax)

end Pointwise

section Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Under coercivity the normalizer `e^{E_{c,Q}}` is integrable for every probability prior. -/
theorem integrable_exp_quadraticExponent (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E)
    {a : ℝ} (ha : 0 < a) (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫) :
    Integrable (fun x => Real.exp (quadraticExponent c Q x)) (μ : Measure E) := by
  obtain ⟨δ, hδ, M, _hM, hbound⟩ := exists_uniform_polynomial_bound c 0 Q 0 ha hQ 0
  have hc : Continuous (fun x => Real.exp (quadraticExponent c Q x)) := by
    unfold quadraticExponent; fun_prop
  refine (integrable_const M).mono' hc.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa only [zero_smul, add_zero, pow_zero, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using hbound 0 (by simpa using hδ) x

/--
Under coercivity the posterior `μ.tilted E_{c,Q}` is a probability law for every probability prior.
-/
theorem isProbabilityMeasure_tilted_quadraticExponent_of_coercive (μ : ProbabilityMeasure E)
    (c : E) (Q : E →L[ℝ] E) {a : ℝ} (ha : 0 < a) (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫) :
    IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) :=
  isProbabilityMeasure_tilted (integrable_exp_quadraticExponent μ c Q ha hQ)

/--
Under coercivity `e^{E_{c,Q}} f` is integrable for every measurable `f` of polynomial growth; no
moment
of the prior is needed. -/
theorem integrable_exp_quadraticExponent_mul (μ : ProbabilityMeasure E) (c : E) (Q : E →L[ℝ] E)
    {a : ℝ} (ha : 0 < a) (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable (fun x => Real.exp (quadraticExponent c Q x) * f x) (μ : Measure E) := by
  obtain ⟨δ, hδ, M, _hM, hb⟩ := exists_uniform_polynomial_bound c 0 Q 0 ha hQ k
  have hc : Continuous (fun x => Real.exp (quadraticExponent c Q x)) := by
    unfold quadraticExponent; fun_prop
  refine
    (integrable_const (C * M)).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hw : Real.exp (quadraticExponent c Q x) * (1 + ‖x‖) ^ k ≤ M := by
    simpa only [zero_smul, add_zero] using hb 0 (by simpa using hδ) x
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (quadraticExponent c Q x) * ‖f x‖ ≤
        Real.exp (quadraticExponent c Q x) * (C * (1 + ‖x‖) ^ k) :=
      mul_le_mul_of_nonneg_left (hbound x) (Real.exp_nonneg _)
    _ = C * (Real.exp (quadraticExponent c Q x) * (1 + ‖x‖) ^ k) := by ring
    _ ≤ C * M := mul_le_mul_of_nonneg_left hw hC

/-- Measurable statistics of polynomial growth are integrable for the coercive posterior. -/
theorem integrable_tilted_quadraticExponent_of_polynomial (μ : ProbabilityMeasure E) (c : E)
    (Q : E →L[ℝ] E) {a : ℝ} (ha : 0 < a) (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫) {f : E → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable f ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  apply (integrable_tilted_iff (integrable_exp_quadraticExponent μ c Q ha hQ) f).mpr
  simpa only [smul_eq_mul] using integrable_exp_quadraticExponent_mul μ c Q ha hQ hf hC k hbound

/-- Measurable statistics of polynomial growth are in `L²` of the coercive posterior. -/
theorem memLp_two_tilted_quadraticExponent_of_polynomial (μ : ProbabilityMeasure E) (c : E)
    (Q : E →L[ℝ] E) {a : ℝ} (ha : 0 < a) (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫) {f : E → ℝ}
    (hf : Measurable f) {C : ℝ} (_hC : 0 ≤ C) (k : ℕ) (hb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply
    integrable_tilted_quadraticExponent_of_polynomial μ c Q ha hQ (hf.pow_const 2) (sq_nonneg C)
      (k * 2)
  intro x
  calc
    ‖f x ^ 2‖ = ‖f x‖ ^ 2 := norm_pow _ _
    _ ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := by gcongr; exact hb x
    _ = C ^ 2 * (1 + ‖x‖) ^ (k * 2) := by rw [mul_pow, pow_mul]

/--
Differentiation of the unnormalized posterior integral along a parameter line (coercive case). -/
theorem hasDerivAt_weighted_integral_quadraticExponent (μ : ProbabilityMeasure E) (c h : E)
    (Q H : E →L[ℝ] E) {a : ℝ} (ha : 0 < a) (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫) {f : E → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hfbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    HasDerivAt
      (fun t : ℝ =>
        ∫ x, Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * f x ∂(μ : Measure E))
      (∫ x, Real.exp (quadraticExponent c Q x) * quadraticExponent h H x * f x ∂(μ : Measure E))
      0 := by
  obtain ⟨δ, hδ, M, _hM, hb⟩ := exists_uniform_polynomial_bound c h Q H ha hQ (k + 2)
  let G : ℝ := ‖h‖ + ‖H‖ / 2
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let F : ℝ → E → ℝ := fun t x => Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * f x
  let F' : ℝ → E → ℝ := fun t x =>
    Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * quadraticExponent h H x * f x
  have he (t : ℝ) :
    Continuous (fun x => Real.exp (quadraticExponent (c + t • h) (Q + t • H) x)) := by
    unfold quadraticExponent
    fun_prop
  have hg : Continuous (fun x => quadraticExponent h H x) := by
    unfold quadraticExponent;
    fun_prop
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) (μ : Measure E) :=
    Eventually.of_forall fun t => (he t).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hi : Integrable (F 0) (μ : Measure E) := by
    simpa only [F, zero_smul, add_zero] using
      integrable_exp_quadraticExponent_mul μ c Q ha hQ hf hC k hfbound
  have hmeas' : AEStronglyMeasurable (F' 0) (μ : Measure E) :=
    ((he 0).aestronglyMeasurable.mul hg.aestronglyMeasurable).mul hf.aestronglyMeasurable
  have hdomb : ∀ᵐ x ∂(μ : Measure E), ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖F' t x‖ ≤ C * G * M := by
    filter_upwards [] with x t ht
    have ht' : |t| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    calc
      ‖F' t x‖ =
          Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * ‖quadraticExponent h H x‖ *
            ‖f x‖ := by
        simp only [F', norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤
          Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * (G * (1 + ‖x‖) ^ 2) *
            (C * (1 + ‖x‖) ^ k) := by
        gcongr
        · exact norm_quadraticExponent_le h H x
        · exact hfbound x
      _ =
          C * G *
            (Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * (1 + ‖x‖) ^ (k + 2)) := by
        rw [pow_add]
        ring
      _ ≤ C * G * M := mul_le_mul_of_nonneg_left (hb t ht' x) (mul_nonneg hC hG)
  have hdiff :
    ∀ᵐ x ∂(μ : Measure E), ∀ t ∈ Metric.ball (0 : ℝ) δ, HasDerivAt (F · x) (F' t x) t := by
    filter_upwards [] with x t _ht
    convert!
        ((((hasDerivAt_id t).mul_const (quadraticExponent h H x)).const_add
              (quadraticExponent c Q x)).exp.mul_const
          (f x)) using
        1 <;>
      simp only [F, F', quadraticExponent_add_smul, one_mul, id_eq]
  have hd :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0 : ℝ) hδ) hmeas hi
      hmeas' hdomb (integrable_const (C * G * M)) hdiff
  simpa only [F, F', zero_smul, add_zero] using hd.2

/--
**Parameter response of the coercive posterior**: for any probability prior, `⟪Q x, x⟫ ≥ a‖x‖²` with
`a > 0`, and measurable `f` of polynomial growth, `t ↦ ∫ f d(μ.tilted E_{c+th,Q+tH})` has derivative
`Cov_{μ.tilted E_{c,Q}}(f, E_{h,H})` at `t = 0`. The case `Q = 0` is not covered here; see
`CompactQuadratic.lean`. -/
theorem expectation_hasDerivAt_quadraticExponent_of_coercive (μ : ProbabilityMeasure E)
    (c h : E) (Q H : E →L[ℝ] E) {a : ℝ} (ha : 0 < a) (hQ : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hfb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    HasDerivAt
      (fun t : ℝ =>
        ∫ x, f x ∂((μ : Measure E).tilted (quadraticExponent (c + t • h) (Q + t • H))))
      (covariance f (quadraticExponent h H) ((μ : Measure E).tilted (quadraticExponent c Q)))
      0 := by
  have hN := hasDerivAt_weighted_integral_quadraticExponent μ c h Q H ha hQ hf hC k hfb
  have hZ :=
    hasDerivAt_weighted_integral_quadraticExponent μ c h Q H ha hQ (f := fun _ => (1 : ℝ))
      measurable_const (C := 1) (by norm_num) 0 (by intro x; simp)
  simp only [mul_one] at hZ
  have hZi := integrable_exp_quadraticExponent μ c Q ha hQ
  have hZne : (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E)) ≠ 0 :=
    (integral_exp_pos hZi).ne'
  let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    isProbabilityMeasure_tilted_quadraticExponent_of_coercive μ c Q ha hQ
  have hF2 := memLp_two_tilted_quadraticExponent_of_polynomial μ c Q ha hQ hf hC k hfb
  have hg : Continuous (quadraticExponent h H) := by unfold quadraticExponent; fun_prop
  have hG2 :=
    memLp_two_tilted_quadraticExponent_of_polynomial μ c Q ha hQ hg.measurable (C :=
      ‖h‖ + ‖H‖ / 2) (by positivity) 2 (norm_quadraticExponent_le h H)
  have hcov :
    covariance f (quadraticExponent h H) ((μ : Measure E).tilted (quadraticExponent c Q)) =
      ((∫ x,
              Real.exp (quadraticExponent c Q x) * quadraticExponent h H x *
                f x ∂(μ : Measure E)) *
            (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E)) -
          (∫ x, Real.exp (quadraticExponent c Q x) * f x ∂(μ : Measure E)) *
            (∫ x,
              Real.exp (quadraticExponent c Q x) * quadraticExponent h H x ∂(μ : Measure E))) /
        (∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure E)) ^ 2 := by
    rw [covariance_eq_sub hF2 hG2, integral_tilted_eq_div, integral_tilted_eq_div,
      integral_tilted_eq_div]
    simp only [Pi.mul_apply]
    have heq :
      (fun x => Real.exp (quadraticExponent c Q x) * (f x * quadraticExponent h H x)) = fun x =>
        Real.exp (quadraticExponent c Q x) * quadraticExponent h H x * f x := by
      funext x; ring
    rw [heq]
    field_simp
  have hd := hN.div hZ (by simpa only [zero_smul, add_zero] using hZne)
  have hfunc :
    (fun t : ℝ =>
        ∫ x, f x ∂((μ : Measure E).tilted (quadraticExponent (c + t • h) (Q + t • H)))) =
      fun t =>
      (∫ x, Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) * f x ∂(μ : Measure E)) /
        ∫ x, Real.exp (quadraticExponent (c + t • h) (Q + t • H) x) ∂(μ : Measure E) := by
    funext t
    exact integral_tilted_eq_div μ _ _
  rw [hfunc, hcov]
  convert! hd using 1
  simp only [zero_smul, add_zero]

end Probability

end FunctionalInequalities.Probability.Posterior
