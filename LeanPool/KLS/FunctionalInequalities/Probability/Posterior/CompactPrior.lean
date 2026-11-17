/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.Exponent
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Probability.Moments.Covariance

/-!
# Tilts of a compactly supported prior

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, the compact-prior stage before (67): for a
probability
law with compact support, every continuous exponent gives an integrable tilt (a probability law),
bounded
measurable statistics are in `L²` of the tilt, tilted expectations are bounded by the support bound,
and
the expectation `t ↦ ∫ f d(μ.tilted (φ + t g))` has derivative `Cov_{μ.tilted φ}(f, g)` at `t = 0`.
No coercivity is needed, so zero parameters are covered.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Posterior

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]

omit [BorelSpace Ω] in
/-- A measurable function bounded on the support is integrable. -/
theorem integrable_of_bound_on_support (μ : ProbabilityMeasure Ω) {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ)
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) : Integrable f (μ : Measure Ω) := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [(μ : Measure Ω).support_mem_ae] with x hx
  exact hb x hx

omit [BorelSpace Ω] [SecondCountableTopology Ω] in
/-- A continuous function is bounded on a compact support. -/
theorem exists_bound_on_support_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ : Ω → ℝ} (hφ : Continuous φ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ x ∈ (μ : Measure Ω).support, ‖φ x‖ ≤ P := by
  obtain ⟨P, hP⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨max P 0, le_max_right _ _, fun x hx => (hP x hx).trans (le_max_left _ _)⟩

/-- `e^{φ} f` is integrable for continuous `φ` and `f` bounded on a compact support. -/
theorem integrable_exp_mul_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ f : Ω → ℝ} (hφ : Continuous φ)
    (hf : Measurable f) {C : ℝ} (_hC : 0 ≤ C) (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    Integrable (fun x => Real.exp (φ x) * f x) (μ : Measure Ω) := by
  obtain ⟨P, _hP, hp⟩ := exists_bound_on_support_of_compact μ hc hφ
  apply
    integrable_of_bound_on_support μ ((Real.continuous_exp.comp hφ).measurable.mul hf)
      (Real.exp P * C)
  intro x hx
  change ‖Real.exp (φ x) * f x‖ ≤ Real.exp P * C
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul ?_ (hb x hx) (norm_nonneg _) (Real.exp_nonneg P)
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (φ x)).trans (by simpa only [Real.norm_eq_abs] using hp x hx)

/-- `e^{φ}` is integrable for continuous `φ` on a compact support. -/
theorem integrable_exp_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ : Ω → ℝ} (hφ : Continuous φ) :
    Integrable (fun x => Real.exp (φ x)) (μ : Measure Ω) := by
  simpa only [mul_one] using
    integrable_exp_mul_of_compact μ hc hφ (f := fun _ => (1 : ℝ)) measurable_const (C := 1)
      (by norm_num) (by intro x hx; simp)

/-- The tilt by a continuous exponent of a compactly supported law is a probability law. -/
theorem isProbabilityMeasure_tilted_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ : Ω → ℝ} (hφ : Continuous φ) :
    IsProbabilityMeasure ((μ : Measure Ω).tilted φ) :=
  isProbabilityMeasure_tilted (integrable_exp_of_compact μ hc hφ)

/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ f : Ω → ℝ} (hφ : Continuous φ)
    (hf : Measurable f) {C : ℝ} (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd

/-- Differentiation of the unnormalized tilted integral under a compact prior. -/
theorem hasDerivAt_weighted_integral_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ} (hφ : Continuous φ)
    (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (φ x + t * g x) * f x ∂(μ : Measure Ω))
      (∫ x, Real.exp (φ x) * g x * f x ∂(μ : Measure Ω)) 0 := by
  obtain ⟨P, _hP, hp⟩ := exists_bound_on_support_of_compact μ hc hφ
  obtain ⟨G, hG, hgB⟩ := exists_bound_on_support_of_compact μ hc hg
  let F : ℝ → Ω → ℝ := fun t x => Real.exp (φ x + t * g x) * f x
  let F' : ℝ → Ω → ℝ := fun t x => Real.exp (φ x + t * g x) * g x * f x
  have he (t : ℝ) : Continuous (fun x => Real.exp (φ x + t * g x)) :=
    Real.continuous_exp.comp (hφ.add (hg.const_mul t))
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) (μ : Measure Ω) :=
    Eventually.of_forall fun t => (he t).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hi : Integrable (F 0) (μ : Measure Ω) := by
    simpa only [F, zero_mul, add_zero] using integrable_exp_mul_of_compact μ hc hφ hf hC hfb
  have hm' : AEStronglyMeasurable (F' 0) (μ : Measure Ω) :=
    ((he 0).aestronglyMeasurable.mul hg.aestronglyMeasurable).mul hf.aestronglyMeasurable
  have hbound :
    ∀ᵐ x ∂(μ : Measure Ω), ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t x‖ ≤ Real.exp (P + G) * G * C := by
    filter_upwards [(μ : Measure Ω).support_mem_ae] with x hx t ht
    have ht' : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have htg : t * g x ≤ G := by
      calc
        t * g x ≤ |t * g x| := le_abs_self _
        _ = |t| * |g x| := abs_mul _ _
        _ ≤ |t| * G :=
          mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hgB x hx)
            (abs_nonneg _)
        _ ≤ G := by nlinarith
    have hφx : φ x ≤ P := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hp x hx)
    have hex : Real.exp (φ x + t * g x) ≤ Real.exp (P + G) := Real.exp_le_exp.mpr (by linarith)
    change |Real.exp (φ x + t * g x) * g x * f x| ≤ Real.exp (P + G) * G * C
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply
      mul_le_mul ?_ (by simpa only [Real.norm_eq_abs] using hfb x hx) (abs_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) hG)
    exact
      mul_le_mul hex (by simpa only [Real.norm_eq_abs] using hgB x hx) (abs_nonneg _)
        (Real.exp_nonneg _)
  have hdiff :
    ∀ᵐ x ∂(μ : Measure Ω), ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (F · x) (F' t x) t := by
    filter_upwards [] with x t _ht
    convert! ((((hasDerivAt_id t).mul_const (g x)).const_add (φ x)).exp.mul_const (f x)) using 1
    simp only [F', one_mul, id_eq]
  have hd :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)) hmeas hi hm' hbound
      (integrable_const (Real.exp (P + G) * G * C)) hdiff
  simpa only [F, F', zero_mul, add_zero] using hd.2

/--
**First variation of a tilted expectation under a compact prior**: for continuous `φ, g` and a
measurable `f` bounded on the support, `t ↦ ∫ f d(μ.tilted (φ + t g))` has derivative
`Cov_{μ.tilted φ}(f, g)` at `t = 0`. Zero parameters are allowed. -/
theorem expectation_hasDerivAt_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ} (hφ : Continuous φ)
    (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f g ((μ : Measure Ω).tilted φ)) 0 := by
  have hN := hasDerivAt_weighted_integral_of_compact μ hc hφ hg hf hC hfb
  have hZ :=
    hasDerivAt_weighted_integral_of_compact μ hc hφ hg (f := fun _ => (1 : ℝ)) measurable_const
      (C := 1) (by norm_num) (by intro x hx; simp)
  simp only [mul_one] at hZ
  have hZi := integrable_exp_of_compact μ hc hφ
  have hZne : (∫ x, Real.exp (φ x) ∂(μ : Measure Ω)) ≠ 0 := (integral_exp_pos hZi).ne'
  let : IsProbabilityMeasure ((μ : Measure Ω).tilted φ) :=
    isProbabilityMeasure_tilted_of_compact μ hc hφ
  have hF2 := memLp_two_tilted_of_compact μ hc hφ hf hfb
  obtain ⟨G, _hG, hgb⟩ := exists_bound_on_support_of_compact μ hc hg
  have hG2 := memLp_two_tilted_of_compact μ hc hφ hg.measurable hgb
  have hcov :
    covariance f g ((μ : Measure Ω).tilted φ) =
      ((∫ x, Real.exp (φ x) * g x * f x ∂(μ : Measure Ω)) *
            (∫ x, Real.exp (φ x) ∂(μ : Measure Ω)) -
          (∫ x, Real.exp (φ x) * f x ∂(μ : Measure Ω)) *
            (∫ x, Real.exp (φ x) * g x ∂(μ : Measure Ω))) /
        (∫ x, Real.exp (φ x) ∂(μ : Measure Ω)) ^ 2 := by
    rw [covariance_eq_sub hF2 hG2, integral_tilted_eq_div, integral_tilted_eq_div,
      integral_tilted_eq_div]
    simp only [Pi.mul_apply]
    have heq : (fun x => Real.exp (φ x) * (f x * g x)) = fun x => Real.exp (φ x) * g x * f x := by
      funext x; ring
    rw [heq]
    field_simp
  have hd := hN.div hZ (by simpa only [zero_mul, add_zero] using hZne)
  have hfunc :
    (fun t : ℝ => ∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) = fun t =>
      (∫ x, Real.exp (φ x + t * g x) * f x ∂(μ : Measure Ω)) /
        ∫ x, Real.exp (φ x + t * g x) ∂(μ : Measure Ω) := by
    funext t
    exact integral_tilted_eq_div μ _ _
  rw [hfunc, hcov]
  convert! hd using 1
  simp only [zero_mul, add_zero]

/--
A tilted expectation of a statistic bounded on the support is bounded by the same constant. -/
theorem norm_integral_tilted_le_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ f : Ω → ℝ} (hφ : Continuous φ)
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂((μ : Measure Ω).tilted φ)‖ ≤ C := by
  let : IsProbabilityMeasure ((μ : Measure Ω).tilted φ) :=
    isProbabilityMeasure_tilted_of_compact μ hc hφ
  have hi : Integrable f ((μ : Measure Ω).tilted φ) := by
    apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) f).mpr
    simpa only [smul_eq_mul] using integrable_exp_mul_of_compact μ hc hφ hf hC hb
  have hbound : ∀ᵐ x ∂((μ : Measure Ω).tilted φ), ‖f x‖ ≤ C := by
    apply (tilted_absolutelyContinuous (μ : Measure Ω) φ).ae_le
    filter_upwards [(μ : Measure Ω).support_mem_ae] with x hx
    exact hb x hx
  calc
    ‖∫ x, f x ∂((μ : Measure Ω).tilted φ)‖ ≤ ∫ x, ‖f x‖ ∂((μ : Measure Ω).tilted φ) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, C ∂((μ : Measure Ω).tilted φ) :=
      integral_mono_ae hi.norm (integrable_const C) hbound
    _ = C := by simp

omit [BorelSpace Ω] [SecondCountableTopology Ω] in
private theorem bound_mul {μ : ProbabilityMeasure Ω} {f k : Ω → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C)
    (hk : ∀ x ∈ (μ : Measure Ω).support, ‖k x‖ ≤ D) :
    ∀ x ∈ (μ : Measure Ω).support, ‖f x * k x‖ ≤ C * D := by
  intro x hx
  rw [norm_mul]
  exact mul_le_mul (hf x hx) (hk x hx) (norm_nonneg _) hC

/--
**Derivative of a tilted covariance under a compact prior**: for continuous `φ, g, k` and measurable
`f`
bounded on the support, `t ↦ Cov_{μ.tilted(φ + t g)}(f, k)` has derivative
`Cov(f, g k) − (∫ g) Cov(f, k) − (∫ k) Cov(f, g)` (all under `μ.tilted φ`) at `t = 0`. -/
theorem covariance_hasDerivAt_of_compact (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g k f : Ω → ℝ} (hφ : Continuous φ)
    (hg : Continuous g) (hk : Continuous k) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => covariance f k ((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f (fun x => g x * k x) ((μ : Measure Ω).tilted φ) -
          (∫ x, g x ∂((μ : Measure Ω).tilted φ)) * covariance f k ((μ : Measure Ω).tilted φ) -
        (∫ x, k x ∂((μ : Measure Ω).tilted φ)) * covariance f g ((μ : Measure Ω).tilted φ))
      0 := by
  obtain ⟨D, hD, hkb⟩ := exists_bound_on_support_of_compact μ hc hk
  obtain ⟨G, hG, hgb⟩ := exists_bound_on_support_of_compact μ hc hg
  have hfk := bound_mul hC hfb hkb
  have hgk := bound_mul hG hgb hkb
  have hN :=
    expectation_hasDerivAt_of_compact μ hc hφ hg (hf.mul hk.measurable) (mul_nonneg hC hD) hfk
  have hF := expectation_hasDerivAt_of_compact μ hc hφ hg hf hC hfb
  have hK := expectation_hasDerivAt_of_compact μ hc hφ hg hk.measurable hD hkb
  have hfun :
    (fun t : ℝ => covariance f k ((μ : Measure Ω).tilted (fun x => φ x + t * g x))) = fun t =>
      (∫ x, f x * k x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) -
        (∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) *
          (∫ x, k x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) := by
    funext t
    have hp : Continuous (fun x => φ x + t * g x) := hφ.add (hg.const_mul t)
    let : IsProbabilityMeasure ((μ : Measure Ω).tilted (fun x => φ x + t * g x)) :=
      isProbabilityMeasure_tilted_of_compact μ hc hp
    rw [covariance_eq_sub (memLp_two_tilted_of_compact μ hc hp hf hfb)
        (memLp_two_tilted_of_compact μ hc hp hk.measurable hkb)]
    rfl
  let ν : Measure Ω := (μ : Measure Ω).tilted φ
  let : IsProbabilityMeasure ν := isProbabilityMeasure_tilted_of_compact μ hc hφ
  have hF2 : MemLp f 2 ν := memLp_two_tilted_of_compact μ hc hφ hf hfb
  have hK2 : MemLp k 2 ν := memLp_two_tilted_of_compact μ hc hφ hk.measurable hkb
  have hG2 : MemLp g 2 ν := memLp_two_tilted_of_compact μ hc hφ hg.measurable hgb
  have hFK2 : MemLp (fun x => f x * k x) 2 ν :=
    memLp_two_tilted_of_compact μ hc hφ (hf.mul hk.measurable) hfk
  have hGK2 : MemLp (fun x => g x * k x) 2 ν :=
    memLp_two_tilted_of_compact μ hc hφ (hg.mul hk).measurable hgk
  have hrate :
    covariance (fun x => f x * k x) g ν -
        (covariance f g ν * ∫ x, k x ∂ν + (∫ x, f x ∂ν) * covariance k g ν) =
      covariance f (fun x => g x * k x) ν - (∫ x, g x ∂ν) * covariance f k ν -
        (∫ x, k x ∂ν) * covariance f g ν := by
    rw [covariance_eq_sub hFK2 hG2, covariance_eq_sub hF2 hG2, covariance_eq_sub hK2 hG2,
      covariance_eq_sub hF2 hGK2, covariance_eq_sub hF2 hK2]
    simp only [Pi.mul_apply]
    have hfgk : (fun x => f x * k x * g x) = fun x => f x * (g x * k x) := by funext x; ring
    have hkg : (fun x => k x * g x) = fun x => g x * k x := by funext x; ring
    rw [hfgk, hkg]
    ring
  rw [hfun]
  have hd := hN.sub (hF.mul hK)
  simp only [zero_mul, add_zero] at hd
  change
    covariance (f * k) g ((μ : Measure Ω).tilted φ) -
        (covariance f g ((μ : Measure Ω).tilted φ) * (∫ x, k x ∂((μ : Measure Ω).tilted φ)) +
          (∫ x, f x ∂((μ : Measure Ω).tilted φ)) * covariance k g ((μ : Measure Ω).tilted φ)) =
      _ at hrate
  rw [hrate] at hd
  convert! hd using 1

end FunctionalInequalities.Probability.Posterior
