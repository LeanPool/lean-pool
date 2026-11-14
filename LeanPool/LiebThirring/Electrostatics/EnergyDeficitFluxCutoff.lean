/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Smooth expanding cutoffs and the radial derivative defect

The fixed smooth cutoff, one on the unit ball and zero outside radius two.

Expanding smooth cutoff centred at the nucleus.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace LiebThirring

/-- The fixed smooth cutoff, one on the unit ball and zero outside radius two. -/
def exteriorFluxBump : ContDiffBump (0 : Position) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- Expanding smooth cutoff centred at the nucleus. -/
noncomputable def exteriorFluxCutoff (c : Position) (T : ℝ) (x : Position) : ℝ :=
  exteriorFluxBump (T⁻¹ • (x - c))

/-- The fixed radial derivative defect whose scaled form appears in the cutoff error. -/
noncomputable def exteriorFluxDefect (x : Position) : ℝ :=
  fderiv ℝ (exteriorFluxBump : Position → ℝ) x x

/-- The cutoff is smooth for every scale. -/
theorem contDiff_exteriorFluxCutoff (c : Position) (T : ℝ) :
    ContDiff ℝ ∞ (exteriorFluxCutoff c T) :=
by
  apply exteriorFluxBump.contDiff.comp
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : Position => T⁻¹)).smul
    (contDiff_id.sub contDiff_const)

/-- The radial derivative defect is continuous. -/
theorem continuous_exteriorFluxDefect : Continuous exteriorFluxDefect :=
  (exteriorFluxBump.contDiff.continuous_fderiv (by simp : (∞ : ℕ∞ω) ≠ 0)).clm_apply continuous_id

/-- Compact support of the radial derivative defect. -/
theorem hasCompactSupport_exteriorFluxDefect : HasCompactSupport exteriorFluxDefect := by
  apply (exteriorFluxBump.hasCompactSupport.fderiv ℝ).mono'
  intro x hx
  apply subset_closure
  apply Function.mem_support.mpr
  intro h
  exact hx (by simp only [exteriorFluxDefect, h, zero_apply])

/-- A global bound on the fixed radial derivative defect. -/
theorem exteriorFluxDefect_bounded : ∃ C : ℝ, ∀ x, ‖exteriorFluxDefect x‖ ≤ C :=
  hasCompactSupport_exteriorFluxDefect.exists_bound_of_continuous continuous_exteriorFluxDefect

/-- The defect at the origin vanishes. -/
@[simp] theorem exteriorFluxDefect_zero : exteriorFluxDefect 0 = 0 := by
  simp only [exteriorFluxDefect, map_zero]

/-- Expanding cutoffs tend to one pointwise. -/
theorem tendsto_exteriorFluxCutoff (c x : Position) :
    Tendsto (fun T : ℝ => exteriorFluxCutoff c T x) atTop (𝓝 1) := by
  have hs : Tendsto (fun T : ℝ => T⁻¹ • (x - c)) atTop (𝓝 (0 : Position)) := by
    simpa only [zero_smul] using (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝
      0)).smul_const (x - c)
  have hone : exteriorFluxBump (0 : Position) = 1 :=
    exteriorFluxBump.one_of_mem_closedBall (by simp [exteriorFluxBump])
  simpa only [exteriorFluxCutoff, hone, Function.comp_def] using
    exteriorFluxBump.continuous.continuousAt.tendsto.comp hs

/-- The scaled radial derivative defect tends to zero pointwise. -/
theorem tendsto_exteriorFluxDefect (c x : Position) :
    Tendsto (fun T : ℝ => exteriorFluxDefect (T⁻¹ • (x - c))) atTop (𝓝 0) := by
  have hs : Tendsto (fun T : ℝ => T⁻¹ • (x - c)) atTop (𝓝 (0 : Position)) := by
    simpa only [zero_smul] using (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝
      0)).smul_const (x - c)
  simpa only [exteriorFluxDefect_zero, Function.comp_def] using
    continuous_exteriorFluxDefect.continuousAt.tendsto.comp hs

/-- Dominated convergence for a cutoff against any integrable real density. -/
theorem tendsto_integral_exteriorFluxCutoff (μ : Measure Position) (c : Position)
    (f : Position → ℝ) (hf : Integrable f μ) :
    Tendsto (fun T : ℝ => ∫ x, exteriorFluxCutoff c T x * f x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · exact Eventually.of_forall (fun T =>
      ((contDiff_exteriorFluxCutoff c T).continuous.measurable.aestronglyMeasurable).mul
        hf.aestronglyMeasurable)
  · exact Eventually.of_forall (fun T => Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ exteriorFluxCutoff c T x from exteriorFluxBump.nonneg)]
      exact mul_le_of_le_one_left (norm_nonneg _) exteriorFluxBump.le_one))
  · exact hf.norm
  · exact Eventually.of_forall (fun x => by
      simpa only [one_mul] using (tendsto_exteriorFluxCutoff c x).mul_const (f x))

/-- The scaled radial cutoff derivative error vanishes under an integrable majorant. -/
theorem tendsto_integral_exteriorFluxDefect (μ : Measure Position) (c : Position)
    (f : Position → ℝ) (hf : Integrable f μ) :
    Tendsto (fun T : ℝ => ∫ x, exteriorFluxDefect (T⁻¹ • (x - c)) * f x ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exteriorFluxDefect_bounded
  have hm (T : ℝ) : Continuous (fun x : Position => exteriorFluxDefect (T⁻¹ • (x - c))) :=
    continuous_exteriorFluxDefect.comp
      ((continuous_const : Continuous (fun _ : Position => T⁻¹)).smul
        (continuous_id.sub continuous_const))
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun T x => exteriorFluxDefect (T⁻¹ • (x - c)) * f x)
    (f := fun _ : Position => (0 : ℝ)) (fun x => C * ‖f x‖)
    (Eventually.of_forall (fun T => hm T |>.measurable.aestronglyMeasurable.mul
      hf.aestronglyMeasurable))
    (Eventually.of_forall (fun T => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))))
    (hf.norm.const_mul C)
    (Eventually.of_forall (fun x => by
      simpa only [zero_mul] using (tendsto_exteriorFluxDefect c x).mul_const (f x)))
  simpa only [integral_zero] using hh

end LiebThirring

end
