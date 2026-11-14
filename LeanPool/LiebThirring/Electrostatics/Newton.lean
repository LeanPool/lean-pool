/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Basic
public import LeanPool.LiebThirring.Electrostatics.SphereAngular
import LeanPool.LiebThirring.Electrostatics.NewtonIntegral
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Newton's shell potential theorem

Newton’s shell formula holds at every observation point, including points on the shell. The
proof uses normalized sphere measure and its height distribution.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LiebThirring

/-- The value at the shell center, including the infinite value at radius zero. -/
theorem coulombPotential_shell_center (a : Position) {r : ℝ} (hr : 0 ≤ r) :
    coulombPotential (shell a r) a = (ENNReal.ofReal r)⁻¹ := by
  unfold coulombPotential
  calc
    _ = ∫⁻ _y, (ENNReal.ofReal r)⁻¹ ∂shell a r := by
      apply lintegral_congr_ae
      filter_upwards [ae_shell_norm a hr] with y hy
      simp only [coulombKernel, norm_sub_rev a y, hy]
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The squared-distance reduction in the direction from the shell center to `x`. -/
theorem coulombKernel_shell_direction (a x : Position) {r : ℝ} (hr : 0 ≤ r)
    (hz : 0 < ‖x - a‖) (ω : sphere (0 : Position) 1) :
    coulombKernel x (a + r • (ω : Position)) =
      (ENNReal.ofReal (Real.sqrt (‖x - a‖ ^ 2 + r ^ 2 -
        2 * ‖x - a‖ * r * inner ℝ (ω : Position) (‖x - a‖⁻¹ • (x - a)))))⁻¹ := by
  have hω : ‖(ω : Position)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hi : inner ℝ (x - a) (ω : Position) = ‖x - a‖ *
      inner ℝ (ω : Position) (‖x - a‖⁻¹ • (x - a)) := by
    rw [inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hz.ne', one_mul, real_inner_comm]
  have hsub : x - (a + r • (ω : Position)) = (x - a) - r • (ω : Position) := by abel
  have hs : ‖x - (a + r • (ω : Position))‖ ^ 2 = ‖x - a‖ ^ 2 + r ^ 2 -
      2 * ‖x - a‖ * r * inner ℝ (ω : Position) (‖x - a‖⁻¹ • (x - a)) := by
    rw [hsub, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hω,
      mul_one, inner_smul_right, hi]
    ring
  rw [coulombKernel, ← hs, Real.sqrt_sq (norm_nonneg _)]

/-- The shell potential is the Archimedes angular average, including zero observation radius. -/
theorem coulombPotential_shell_angular (a : Position) {r : ℝ} (hr : 0 < r) (x : Position) :
    coulombPotential (shell a r) x = (ENNReal.ofReal 2)⁻¹ *
      ∫⁻ t in Icc (-1 : ℝ) 1,
        (ENNReal.ofReal (Real.sqrt (‖x - a‖ ^ 2 + r ^ 2 - 2 * ‖x - a‖ * r * t)))⁻¹ := by
  by_cases hxa : x = a
  · subst x
    rw [coulombPotential_shell_center a hr.le]
    simp only [sub_self, norm_zero]
    simpa only [max_eq_right hr.le] using
      (newton_angular_integral (u := 0) (by norm_num) hr).symm
  · have hz : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
    let e : Position := ‖x - a‖⁻¹ • (x - a)
    have he : ‖e‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz), inv_mul_cancel₀ hz.ne']
    let f : ℝ → ℝ≥0∞ := fun t =>
      (ENNReal.ofReal (Real.sqrt (‖x - a‖ ^ 2 + r ^ 2 - 2 * ‖x - a‖ * r * t)))⁻¹
    have hf : Measurable f := by
      exact (ENNReal.measurable_ofReal.comp
        ((continuous_const.sub (continuous_const.mul continuous_id)).sqrt.measurable)).inv
    have hk : Measurable (coulombKernel x) :=
      (ENNReal.measurable_ofReal.comp
        (continuous_norm.comp (continuous_const.sub continuous_id)).measurable).inv
    have hm : Measurable (fun ω : sphere (0 : Position) 1 => inner ℝ (ω : Position) e) :=
      (continuous_subtype_val.inner continuous_const).measurable
    unfold coulombPotential shell
    rw [lintegral_map hk (measurable_shellMap a r)]
    calc
      _ = ∫⁻ ω : sphere (0 : Position) 1, f (inner ℝ (ω : Position) e) ∂unitSphereMeasure := by
        apply lintegral_congr
        intro ω
        exact coulombKernel_shell_direction a x hr.le hz ω
      _ = ∫⁻ t, f t ∂unitSphereMeasure.map
          (fun ω : sphere (0 : Position) 1 => inner ℝ (ω : Position) e) :=
        (lintegral_map hf hm).symm
      _ = _ := by
        rw [unitSphereMeasure_inner_uniform e he, lintegral_smul_measure]
        rfl

/-- Newton's formula for every point, including the center and the singular sphere. -/
theorem coulombPotential_shell (a : Position) {r : ℝ} (hr : 0 < r) (x : Position) :
    coulombPotential (shell a r) x = (ENNReal.ofReal (max ‖x - a‖ r))⁻¹ := by
  rw [coulombPotential_shell_angular a hr x]
  exact newton_angular_integral (norm_nonneg _) hr
end LiebThirring

end
