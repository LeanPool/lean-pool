/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.SmoothBall

/-!
# LipschitzApproximation: Measurable

Measurability of gradients, almost-everywhere differentiability and dominated Lp convergence for
approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Measurable

variable [MeasurableSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Dominated convergence for the `L^p` seminorm, `0 < p < ∞`. -/
theorem tendsto_eLpNorm_zero_of_dominated {V : Type*} [NormedAddCommGroup V]
    (μ : Measure E) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    {F : ℕ → E → V} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    {bound : E → ℝ} (hbound : MemLp bound p μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p μ) atTop (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have heq : ∀ n, eLpNorm (F n) p μ = eLpNorm' (F n) p.toReal μ := fun n =>
    eLpNorm_eq_eLpNorm' hp0 hp (hF n)
  simp_rw [heq, eLpNorm']
  have h : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖bound x‖ₑ ^ p.toReal)
      (fun n => ((hF n).enorm.pow_const _)) (fun n => ?_) ?_ ?_
    · filter_upwards [hle n] with x hx
      have : ‖F n x‖ₑ ≤ ‖bound x‖ₑ := by
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
          coe_nnnorm, coe_nnnorm]
        exact hx.trans (le_abs_self _)
      exact ENNReal.rpow_le_rpow this hq.le
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hbound.eLpNorm_lt_top).ne
    · filter_upwards [hlim] with x hx
      have h0 : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : V)).comp hx
        simp only [Function.comp_def, enorm_zero] at this
        exact this
      have := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp h0
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hq] using this
  simp only [lintegral_zero] at h
  have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp h
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hq),
    ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p.toReal)] using this

section GradientMeasurability

variable [BorelSpace E] [CompleteSpace E]

theorem measurable_gradient (f : E → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

variable [SecondCountableTopology E]

theorem aestronglyMeasurable_gradient (f : E → ℝ) (μ : Measure E) :
    AEStronglyMeasurable (gradient f) μ :=
  (measurable_gradient f).aestronglyMeasurable

end GradientMeasurability

variable [BorelSpace E] [FiniteDimensional ℝ E]
/-- Rademacher's theorem for locally Lipschitz real functions. -/
theorem ae_differentiableAt_of_locallyLipschitz {f : E → ℝ} (hf : LocallyLipschitz f)
    (m : Measure E) [m.IsAddHaarMeasure] : ∀ᵐ x ∂m, DifferentiableAt ℝ f x := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂m, x ∈ Metric.ball (0 : E) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨K, hK⟩ :=
      lipschitzOnWith_of_locallyLipschitz_of_isCompact hf (isCompact_closedBall (0 : E) n)
    obtain ⟨g, hg, hfg⟩ := hK.extend_real
    filter_upwards [hg.ae_differentiableAt (μ := m)] with x hx hxn
    have : f =ᶠ[𝓝 x] g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxn] with y hy
      exact hfg (Metric.ball_subset_closedBall hy)
    exact hx.congr_of_eventuallyEq this
  filter_upwards [ae_all_iff.mpr h] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (by simpa using hn)

/-- The radii `1 / (j + 1)` used for the approximating sequences. -/
def radius (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

theorem tendsto_radius : Tendsto radius atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

end Measurable


end FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
