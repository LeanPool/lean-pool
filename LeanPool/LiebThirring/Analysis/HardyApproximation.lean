/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Analysis.HardySchwartz
import Mathlib.Analysis.Normed.Lp.SmoothApprox
/-!
# Approximation in the squared-radius weighted norm

Squared-radius weighted volume is finite on compact sets.

The squared-norm integral is the square of the extended L² seminorm.
-/
public section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology SchwartzMap FourierTransform
namespace LiebThirring

/-- Squared-radius weighted volume is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_norm_sq_volume :
    IsFiniteMeasureOnCompacts ((volume : Measure Position).withDensity
      (fun x => ENNReal.ofReal (‖x‖ ^ 2))) := by
  constructor
  intro K hK
  rw [withDensity_apply _ hK.measurableSet]
  have hi := (continuous_norm.pow 2).continuousOn.integrableOn_compact
    (μ := (volume : Measure Position)) hK
  change IntegrableOn (fun x : Position => ‖x‖ ^ 2) K volume at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖x‖))]
  exact ENNReal.ofReal_lt_top

variable {E : Type*} [NormedAddCommGroup E]

/-- The squared-norm integral is the square of the extended L² seminorm. -/
theorem lintegral_norm_sq_eq_eLpNorm_sq {μ : Measure Position} {f : Position → E}
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) = eLpNorm f 2 μ ^ 2 := by
  change (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) = eLpNorm f 2 μ ^ 2
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf).symm

/-- A finite squared-norm integral gives membership in L². -/
theorem memLp_two_of_lintegral_norm_sq_lt_top {μ : Measure Position} {f : Position → E}
    (hf : AEStronglyMeasurable f μ) (h : (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    MemLp f 2 μ := by
  rw [lintegral_norm_sq_eq_eLpNorm_sq hf] at h
  exact (ENNReal.pow_lt_top_iff.mp h).resolve_right (by decide)

/-- Vanishing L² approximation errors give convergence of the associated Lp elements. -/
theorem tendsto_toLp_of_eLpNorm_sub_le {μ : Measure Position} {v : Position → E}
    (hv : MemLp v 2 μ) {f : ℕ → Position → E} (hf : ∀ n, MemLp (f n) 2 μ)
    (h : ∀ n, eLpNorm (v - f n) 2 μ ≤ ENNReal.ofReal ((n + 1 : ℝ)⁻¹)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hv.toLp v)) := by
  apply tendsto_iff_edist_tendsto_0.mpr
  have hz : Tendsto (fun n : ℕ => ENNReal.ofReal ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal
      (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz (fun n => bot_le)
  intro n
  dsimp only
  rw [Lp.edist_toLp_toLp, eLpNorm_sub_comm]
  exact h n

variable [NormedSpace ℝ E]

/-- Schwartz approximation with both L² convergence and convergence of the radial quadratic
integral. -/
theorem exists_schwartz_weighted_approximation (v : Lp E 2 (volume : Measure Position))
    (hv : (∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2) < ⊤) :
    ∃ f : ℕ → 𝓢(Position, E),
      Tendsto (fun n => (f n).toLp 2 volume) atTop (𝓝 v) ∧
      Tendsto (fun n => ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖f n x‖₊ : ℝ≥0∞) ^ 2)
        atTop (𝓝 (∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2)) := by
  let ν := (volume : Measure Position).withDensity (fun x => ENNReal.ofReal (‖x‖ ^ 2))
  let μ := (volume : Measure Position) + ν
  have hν : IsFiniteMeasureOnCompacts ν := isFiniteMeasureOnCompacts_norm_sq_volume
  let : IsFiniteMeasureOnCompacts ν := hν
  have hμ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK =>
    (by
      change volume K + ν K < ⊤
      exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩)⟩
  let : IsFiniteMeasureOnCompacts μ := hμ
  have hm : Measurable (fun x : Position => ENNReal.ofReal (‖x‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp (continuous_norm.pow 2).measurable
  have haν : AEStronglyMeasurable (fun x => v x) ν :=
    (Lp.aestronglyMeasurable v).mono_ac (withDensity_absolutelyContinuous _ _)
  have haμ : AEStronglyMeasurable (fun x => v x) μ :=
    (Lp.aestronglyMeasurable v).add_measure haν
  have he (g : Position → E) (hg : AEStronglyMeasurable g volume) :
      (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂ν) =
        ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖g x‖₊ : ℝ≥0∞) ^ 2 := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hm.aemeasurable
      (hg.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)]
    apply lintegral_congr
    intro x
    dsimp only [Pi.mul_apply]
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  have hvν : MemLp (fun x => v x) 2 ν :=
    memLp_two_of_lintegral_norm_sq_lt_top haν (by rw [he _ (Lp.aestronglyMeasurable v)]; exact hv)
  have hvμ : MemLp (fun x => v x) 2 μ := by
    apply memLp_two_of_lintegral_norm_sq_lt_top haμ
    rw [lintegral_add_measure, he _ (Lp.aestronglyMeasurable v)]
    apply ENNReal.add_lt_top.mpr
    exact ⟨by rw [lintegral_norm_sq_eq_eLpNorm_sq (Lp.aestronglyMeasurable v)]; finiteness, hv⟩
  have hh (n : ℕ) := hvμ.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by positivity : 0 < (n + 1 : ℝ)⁻¹)
  choose g hgK hgC hg using hh
  let f : ℕ → 𝓢(Position, E) := fun n => (hgK n).toSchwartzMap (hgC n)
  have hfν (n : ℕ) : MemLp (f n) 2 ν := (hgC n).continuous.memLp_of_hasCompactSupport (hgK n)
  have hf₀ (n : ℕ) : MemLp (f n) 2 volume := (f n).memLp 2 volume
  have h₀ := tendsto_toLp_of_eLpNorm_sub_le (Lp.memLp v) hf₀ (fun n =>
    (eLpNorm_mono_measure (f := (fun x => v x) - (f n : Position → E)) (p := 2)
      (show (volume : Measure Position) ≤ μ from Measure.le_add_right le_rfl)).trans (hg n))
  have h₁ := tendsto_toLp_of_eLpNorm_sub_le hvν hfν (fun n =>
    (eLpNorm_mono_measure (f := (fun x => v x) - (f n : Position → E)) (p := 2) (show ν ≤ μ from
      Measure.le_add_left le_rfl)).trans (hg n))
  refine ⟨f, ?_, ?_⟩
  · have hi : (Lp.memLp v).toLp (fun x => v x) = v := by
      apply Lp.ext
      exact (Lp.memLp v).coeFn_toLp
    simpa only [SchwartzMap.toLp, hi] using h₀
  · have hh := (ENNReal.continuous_pow 2).tendsto _ |>.comp (continuous_enorm.tendsto _ |>.comp h₁)
    have hn (n : ℕ) : ‖(hfν n).toLp (f n)‖ₑ ^ 2 =
        ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖f n x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [Lp.enorm_toLp, ← lintegral_norm_sq_eq_eLpNorm_sq (hfν n).aestronglyMeasurable,
        he _ (f n).continuous.aestronglyMeasurable]
    have hv' : ‖hvν.toLp (fun x => v x)‖ₑ ^ 2 =
        ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [Lp.enorm_toLp, ← lintegral_norm_sq_eq_eLpNorm_sq haν, he _ (Lp.aestronglyMeasurable v)]
    simpa only [Function.comp_def, hn, hv'] using hh

end LiebThirring
end
