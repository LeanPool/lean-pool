/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Process.Kernel.OnePointExhaustionTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.UniformExhaustionBudget
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventTail

/-!
# ExhaustionTailInput

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stream-field variable exhaustion-tail input

The amplified pointwise analytic tail is transported to the exhaustion metric
and packaged with the shift-dependent uniform profile.  Above the cubic-log
cutoff this is the localized stream-field estimate; below it the normalized
potential-mass bound supplies the unit estimate.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open DivergenceFormProcess.Form
open HCPolySupport
open MarkovProcess MarkovProcess.Semigroup
open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem streamExhaustionAmp_ge {x : Vec d} {r : ℝ} :
    r ≤ streamExhaustionAmp x r := by
  unfold streamExhaustionAmp
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [NeZero d] in
private theorem measurable_complBallIndicator (x : Vec d) (r : ℝ) :
    Measurable fun z ↦ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet.compl

omit [NeZero d] in
private theorem complBallIndicator_nonneg (x : Vec d) (r : ℝ) (z : Vec d) :
    0 ≤ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem abs_complBallIndicator_le_one (x : Vec d) (r : ℝ) (z : Vec d) :
    |(Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z| ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem ofReal_complBallIndicator (x : Vec d) (r : ℝ) :
    (fun z ↦ ENNReal.ofReal
      ((Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z)) =
      (Metric.ball x r)ᶜ.indicator (1 : Vec d → ℝ≥0∞) := by
  funext z
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> norm_num

theorem stream_liveTail_le_uniform
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : (streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ)) (x : Vec d) (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) x
          (Metric.ball x (streamExhaustionAmp x r))ᶜ ≤
      ENNReal.ofReal
        (streamUniformExhaustionProfile M omega (mu : ℝ)
          (Real.sqrt (mu : ℝ) * r)) := by
  by_cases hcut : streamUniformExhaustionCutoff M omega (mu : ℝ) <
      Real.sqrt (mu : ℝ) * r
  · let ar := streamExhaustionAmp x r
    let f : Vec d → ℝ :=
      fun z ↦ (Metric.ball x ar)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z
    have har : 0 < ar := streamExhaustionAmp_pos hr
    have hf : Measurable f := measurable_complBallIndicator x ar
    have hf0 : ∀ z, 0 ≤ f z := complBallIndicator_nonneg x ar
    have hf1 : ∀ z, |f z| ≤ 1 := abs_complBallIndicator_le_one x ar
    have hzero : ∀ z ∈ euclideanBall x ar, f z = 0 := by
      intro z hz
      dsimp only [f]
      rw [Set.indicator_of_notMem]
      exact fun hzcompl ↦ hzcompl
        (HCPolySupport.euclideanBall_subset_metricBall har hz)
    have hsqrt : 0 ≤ Real.sqrt (mu : ℝ) := Real.sqrt_nonneg _
    have hscale : Real.sqrt (mu : ℝ) * r ≤ Real.sqrt (mu : ℝ) * ar :=
      mul_le_mul_of_nonneg_left streamExhaustionAmp_ge hsqrt
    have hone : 1 < Real.sqrt (mu : ℝ) * ar :=
      lt_of_le_of_lt (one_le_streamUniformExhaustionCutoff M omega (mu : ℝ))
        (hcut.trans_le hscale)
    have htail := mul_toReal_streamAnalyticMinimalResolvent_le_profile
      M omega mu hmu hf hf0 hf1 har hone hzero
    have hdom := streamLocalizedTailProfile_amp_le_uniform
      M omega hmu x hr hcut
    have hreal := htail.trans hdom
    have hfinite := (streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent_ne_top
      mu hf hf0 (by norm_num : (0 : ℝ) ≤ 1) hf1 x
    have hset : R.kernelSemigroup.kernelResolvent (mu : ℝ)
        ((Metric.ball x ar)ᶜ.indicator 1) x =
        R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x ar)ᶜ := by
      rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ)
        (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl) x,
        lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]
    change ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x ar)ᶜ ≤ _
    rw [← hset, ← ofReal_complBallIndicator x ar, hid mu hf hf0 hf1 x]
    rw [← ENNReal.ofReal_toReal hfinite,
      ← ENNReal.ofReal_mul mu.property.le]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hbelow : Real.sqrt (mu : ℝ) * r ≤
        streamUniformExhaustionCutoff M omega (mu : ℝ) := le_of_not_gt hcut
    calc
      ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.resolventPotential (mu : ℝ) x
            (Metric.ball x (streamExhaustionAmp x r))ᶜ ≤ 1 :=
        R.kernelSemigroup.ofReal_mul_resolventPotential_le_one mu.property x _
      _ ≤ ENNReal.ofReal
          (streamUniformExhaustionProfile M omega (mu : ℝ)
            (Real.sqrt (mu : ℝ) * r)) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
          (one_le_streamUniformExhaustionProfile_of_le_cutoff M omega hbelow)

/-- The stream-field profile and reciprocal-norm exhaustion provide the
shift-dependent one-point resolvent-tail input with time exponent `3/2`. -/
def streamVariableExhaustionTailInput
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : (streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R)
    (hcons : R.kernelSemigroup.IsConservative) :
    WholeSpaceVariableExhaustionResolventTailInput R where
  rho := streamExhaustionRho
  continuous_rho := continuous_streamExhaustionRho
  rho_pos := streamExhaustionRho_pos
  lipschitz_rho := lipschitzWith_streamExhaustionRho
  isCompact_superlevel := fun _epsilon hepsilon ↦
    isCompact_streamExhaustionRho_superlevel hepsilon
  rho_le_one := streamExhaustionRho_le_one
  phi := streamUniformExhaustionProfile M omega
  phi_nonneg := streamUniformExhaustionProfile_nonneg M omega
  hasTail := fun mu hmu ↦
    Algsuperdiff.Process.PositiveC0ContractiveResolvent.hasResolventTail_onePoint_of_amplified R
      hcons streamExhaustionRho
      continuous_streamExhaustionRho streamExhaustionRho_pos
      lipschitzWith_streamExhaustionRho
      (fun _epsilon hepsilon ↦ isCompact_streamExhaustionRho_superlevel hepsilon)
      streamExhaustionAmp
      (fun _x _r _z hdist hlevel ↦
        streamExhaustionAmp_le_dist hdist hlevel)
      (stream_liveTail_le_uniform M omega R hid mu hmu)
  cutoff := streamUniformExhaustionCutoff M omega
  cutoff_nonneg := streamUniformExhaustionCutoff_nonneg M omega
  budget := streamUniformExhaustionBudget M omega
  budget_nonneg := streamUniformExhaustionBudget_nonneg M omega
  integral_le := fun mu hmu ↦
    lintegral_streamUniformExhaustionProfile_mul_cube_le M omega hmu
  timeExponent := 3 / 2
  one_lt_timeExponent := by norm_num
  timeExponent_le_two := by norm_num
  cutoffGrowth := streamUniformExhaustionGrowth M omega (3 / 2)
  cutoffGrowth_nonneg := streamUniformExhaustionGrowth_nonneg M omega
    (by norm_num) (by norm_num)
  cutoff_pow_le := fun mu hmu ↦
    streamUniformExhaustionCutoff_pow_le M omega (by norm_num) (by norm_num) hmu

end

end Algsuperdiff.Section5.Field
