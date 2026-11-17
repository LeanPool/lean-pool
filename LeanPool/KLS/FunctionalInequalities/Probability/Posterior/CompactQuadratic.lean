/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.CompactPrior
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.Coercive

/-!
# The BKL posterior of a compactly supported prior

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67) in the compact stage: for a compactly supported
prior every parameter pair `(c, Q)`, including the initial pair `c = Q = 0`, gives a probability
posterior, continuous statistics are in `L²`, the expectation has the covariance derivative along
signed
parameter lines, and all norm moments are bounded uniformly in the parameters by a support radius.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Posterior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/--
**Parameter response of the posterior of a compactly supported prior**: for every `(c, Q)`
(including
`c = Q = 0`) and measurable `f` bounded on the support, `t ↦ ∫ f d(μ.tilted E_{c+th,Q+tH})` has
derivative
`Cov_{μ.tilted E_{c,Q}}(f, E_{h,H})` at `t = 0`. -/
theorem expectation_hasDerivAt_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c h : E) (Q H : E →L[ℝ] E) {f : E → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
    HasDerivAt
      (fun t : ℝ =>
        ∫ x, f x ∂((μ : Measure E).tilted (quadraticExponent (c + t • h) (Q + t • H))))
      (covariance f (quadraticExponent h H) ((μ : Measure E).tilted (quadraticExponent c Q)))
      0 := by
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  have hg : Continuous (quadraticExponent h H) := by unfold quadraticExponent; fun_prop
  have hphase (t : ℝ) :
    quadraticExponent (c + t • h) (Q + t • H) = fun x =>
      quadraticExponent c Q x + t * quadraticExponent h H x := by
    funext x
    exact quadraticExponent_add_smul c h Q H t x
  simpa only [hphase] using expectation_hasDerivAt_of_compact μ hc hφ hg hf hC hb

/-- Every posterior of a compactly supported prior is a probability law. -/
theorem isProbabilityMeasure_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  apply isProbabilityMeasure_tilted_of_compact μ hc
  unfold quadraticExponent
  fun_prop

/-- Continuous statistics are in `L²` of every posterior of a compactly supported prior. -/
theorem memLp_two_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E)
    {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  exact memLp_two_tilted_of_compact μ hc hφ hf.measurable hb

/--
**Uniform posterior moments**: a support radius `R` bounds `∫ ‖x‖^p` under every posterior `(c, Q)`
by `R^p` (the bounded-moment input for (69)–(70); the stochastic equations themselves are not
constructed). -/
theorem exists_uniform_norm_moments_tilted_quadraticExponent_of_compact
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) :
    ∃ R : ℝ,
      0 ≤ R ∧
        ∀ (c : E) (Q : E →L[ℝ] E) (p : ℕ),
          Integrable (fun x => ‖x‖ ^ p) ((μ : Measure E).tilted (quadraticExponent c Q)) ∧
            (∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (quadraticExponent c Q))) ≤ R ^ p := by
  obtain ⟨R, hR, hbound⟩ :=
    exists_bound_on_support_of_compact μ hc (continuous_norm : Continuous (fun x : E => ‖x‖))
  have hnorm : ∀ x ∈ (μ : Measure E).support, ‖x‖ ≤ R := by
    intro x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using hbound x hx
  refine ⟨R, hR, ?_⟩
  intro c Q p
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  have hf : Continuous (fun x : E => ‖x‖ ^ p) := continuous_norm.pow p
  have hfb : ∀ x ∈ (μ : Measure E).support, ‖‖x‖ ^ p‖ ≤ R ^ p := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) p)]
    exact pow_le_pow_left₀ (norm_nonneg x) (hnorm x hx) p
  have hi2 := memLp_two_tilted_quadraticExponent_of_compact μ hc c Q hf
  let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  refine ⟨hi2.integrable one_le_two, ?_⟩
  have hle :
    (∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (quadraticExponent c Q))) ≤
      ‖∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (quadraticExponent c Q))‖ :=
    le_abs_self _
  exact
    hle.trans (norm_integral_tilted_le_of_compact μ hc hφ hf.measurable (pow_nonneg hR p) hfb)

end FunctionalInequalities.Probability.Posterior
