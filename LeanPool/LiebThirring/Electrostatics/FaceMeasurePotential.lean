/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import LeanPool.LiebThirring.Electrostatics.Basic
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Generic potential estimates from uniform local Coulomb control

The extended Coulomb kernel is measurable as a function of its second argument.

Outside the unit ball the kernel is at most one.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LiebThirring

/-- The extended Coulomb kernel is measurable as a function of its second argument. -/
theorem measurable_coulombKernel_right (x : Position) : Measurable (coulombKernel x) :=
  ((measurable_const.sub measurable_id).norm.ennreal_ofReal).inv

/-- Outside the unit ball the kernel is at most one. -/
theorem coulombKernel_le_one_of_not_mem_ball (x y : Position)
    (hy : y ∉ Metric.ball x 1) : coulombKernel x y ≤ 1 := by
  have hd : 1 ≤ ‖x - y‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
  change (ENNReal.ofReal ‖x - y‖)⁻¹ ≤ 1
  rw [← inv_one]
  exact ENNReal.inv_le_inv.mpr (by simpa using ENNReal.ofReal_le_ofReal hd)

/-- Uniform local control at radius one gives a global bound. -/
theorem coulombPotential_le_of_local_bound (μ : Measure Position) (C : ℝ)
    (hlocal : ∀ x : Position, ∀ ε : ℝ, 0 < ε →
      ∫⁻ y in Metric.ball x ε, coulombKernel x y ∂μ ≤ ENNReal.ofReal (C * ε))
    (x : Position) : coulombPotential μ x ≤ ENNReal.ofReal C + μ univ := by
  change (∫⁻ y, coulombKernel x y ∂μ) ≤ _
  rw [← lintegral_add_compl _ measurableSet_ball]
  focus apply add_le_add
  · simpa only [mul_one] using hlocal x 1 zero_lt_one
  · calc
      ∫⁻ y in (Metric.ball x 1)ᶜ, coulombKernel x y ∂μ ≤
          ∫⁻ y in (Metric.ball x 1)ᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
        exact coulombKernel_le_one_of_not_mem_ball x y hy
      _ = μ (Metric.ball x 1)ᶜ := by simp only [lintegral_const, Measure.restrict_apply_univ,
        one_mul]
      _ ≤ μ univ := measure_mono (subset_univ _)

/-- A finite measure with uniform local control has an everywhere finite potential. -/
theorem coulombPotential_lt_top_of_local_bound (μ : Measure Position) [IsFiniteMeasure μ]
    (C : ℝ) (hlocal : ∀ x : Position, ∀ ε : ℝ, 0 < ε →
      ∫⁻ y in Metric.ball x ε, coulombKernel x y ∂μ ≤ ENNReal.ofReal (C * ε))
    (x : Position) : coulombPotential μ x < ⊤ :=
  (coulombPotential_le_of_local_bound μ C hlocal x).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, measure_lt_top μ univ⟩)

/-- The self-energy is finite under the same uniform local estimate. -/
theorem coulombEnergy_lt_top_of_local_bound (μ : Measure Position) [IsFiniteMeasure μ]
    (C : ℝ) (hlocal : ∀ x : Position, ∀ ε : ℝ, 0 < ε →
      ∫⁻ y in Metric.ball x ε, coulombKernel x y ∂μ ≤ ENNReal.ofReal (C * ε)) :
    coulombEnergy μ μ < ⊤ := by
  change (∫⁻ x, coulombPotential μ x ∂μ) < ⊤
  calc
    ∫⁻ x, coulombPotential μ x ∂μ ≤
        ∫⁻ _ : Position, (ENNReal.ofReal C + μ univ) ∂μ :=
      lintegral_mono (coulombPotential_le_of_local_bound μ C hlocal)
    _ = (ENNReal.ofReal C + μ univ) * μ univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top
      (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, measure_lt_top μ univ⟩)
      (measure_lt_top μ univ)

/-- Continuous capped Coulomb kernel, with a positive cap radius. -/
noncomputable def cappedCoulombKernel (r : ℝ) (x y : Position) : ℝ≥0∞ :=
  (ENNReal.ofReal (max r ‖x - y‖))⁻¹

/-- Potential of the capped kernel. -/
noncomputable def cappedCoulombPotential (μ : Measure Position) (r : ℝ) (x : Position) : ℝ≥0∞ :=
  ∫⁻ y, cappedCoulombKernel r x y ∂μ

theorem continuous_cappedCoulombKernel_left (r : ℝ) (y : Position) :
    Continuous (fun x : Position => cappedCoulombKernel r x y) :=
  (ENNReal.continuous_ofReal.comp (continuous_const.max
    (continuous_id.sub continuous_const).norm)).fun_inv

theorem measurable_cappedCoulombKernel_right (r : ℝ) (x : Position) :
    Measurable (cappedCoulombKernel r x) :=
  ((measurable_const.max (measurable_const.sub measurable_id).norm).ennreal_ofReal).inv

theorem cappedCoulombKernel_le (r : ℝ) (x y : Position) :
    cappedCoulombKernel r x y ≤ coulombKernel x y :=
  ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (le_max_right _ _))

theorem cappedCoulombKernel_le_cap (r : ℝ) (x y : Position) :
    cappedCoulombKernel r x y ≤ (ENNReal.ofReal r)⁻¹ :=
  ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem cappedCoulombPotential_le (μ : Measure Position) (r : ℝ) (x : Position) :
    cappedCoulombPotential μ r x ≤ coulombPotential μ x :=
  lintegral_mono (cappedCoulombKernel_le r x)

/-- A positive cap radius gives a continuous potential for every finite measure. -/
theorem continuous_cappedCoulombPotential (μ : Measure Position) [IsFiniteMeasure μ]
    (r : ℝ) (hr : 0 < r) : Continuous (cappedCoulombPotential μ r) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Tendsto (fun z => ∫⁻ y, cappedCoulombKernel r z y ∂μ) (𝓝 x)
    (𝓝 (∫⁻ y, cappedCoulombKernel r x y ∂μ))
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun _ : Position => (ENNReal.ofReal r)⁻¹)
  · exact Eventually.of_forall (measurable_cappedCoulombKernel_right r)
  · exact Eventually.of_forall (fun z => Eventually.of_forall (cappedCoulombKernel_le_cap r z))
  · rw [lintegral_const]
    exact (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hr))
      (measure_lt_top μ univ)).ne
  · exact Eventually.of_forall (fun y => (continuous_cappedCoulombKernel_left r y).continuousAt)

theorem cappedCoulombPotential_lt_top (μ : Measure Position) [IsFiniteMeasure μ]
    (r : ℝ) (hr : 0 < r) (x : Position) : cappedCoulombPotential μ r x < ⊤ := by
  calc
    cappedCoulombPotential μ r x ≤ ∫⁻ _ : Position, (ENNReal.ofReal r)⁻¹ ∂μ :=
      lintegral_mono (cappedCoulombKernel_le_cap r x)
    _ = (ENNReal.ofReal r)⁻¹ * μ univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hr))
      (measure_lt_top μ univ)

/-- The potential differs from its capped approximation only in the local ball. -/
theorem coulombPotential_le_capped_add_of_local_bound (μ : Measure Position) (C r : ℝ)
    (hr : 0 < r) (hlocal : ∀ x : Position, ∀ ε : ℝ, 0 < ε →
      ∫⁻ y in Metric.ball x ε, coulombKernel x y ∂μ ≤ ENNReal.ofReal (C * ε))
    (x : Position) :
    coulombPotential μ x ≤ cappedCoulombPotential μ r x + ENNReal.ofReal (C * r) := by
  classical
  have hk : ∀ y : Position, coulombKernel x y ≤ cappedCoulombKernel r x y +
      (Metric.ball x r).indicator (coulombKernel x) y := by
    intro y
    by_cases hy : y ∈ Metric.ball x r
    · rw [Set.indicator_of_mem hy]
      exact le_add_left le_rfl
    · have hd : r ≤ ‖x - y‖ := by
        simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
      rw [Set.indicator_of_notMem hy, add_zero]
      simp only [cappedCoulombKernel, max_eq_right hd, coulombKernel, le_refl]
  calc
    coulombPotential μ x ≤ ∫⁻ y, cappedCoulombKernel r x y +
        (Metric.ball x r).indicator (coulombKernel x) y ∂μ := lintegral_mono hk
    _ = cappedCoulombPotential μ r x + ∫⁻ y in Metric.ball x r, coulombKernel x y ∂μ := by
      rw [lintegral_add_left (measurable_cappedCoulombKernel_right r x),
        lintegral_indicator measurableSet_ball]
      rfl
    _ ≤ _ := add_le_add le_rfl (hlocal x r hr)

/-- The real-valued capped potential is continuous. -/
theorem continuous_toReal_cappedCoulombPotential (μ : Measure Position) [IsFiniteMeasure μ]
    (r : ℝ) (hr : 0 < r) : Continuous (fun x => (cappedCoulombPotential μ r x).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (ENNReal.continuousAt_toReal (cappedCoulombPotential_lt_top μ r hr x).ne).comp
    (continuous_cappedCoulombPotential μ r hr).continuousAt

/-- Quantitative uniform approximation in the finite real-valued potential. -/
theorem dist_toReal_coulombPotential_capped_le (μ : Measure Position) [IsFiniteMeasure μ]
    (C r : ℝ) (hC : 0 ≤ C) (hr : 0 < r)
    (hlocal : ∀ x : Position, ∀ ε : ℝ, 0 < ε →
      ∫⁻ y in Metric.ball x ε, coulombKernel x y ∂μ ≤ ENNReal.ofReal (C * ε))
    (x : Position) :
    dist (coulombPotential μ x).toReal (cappedCoulombPotential μ r x).toReal ≤ C * r := by
  have hp := coulombPotential_lt_top_of_local_bound μ C hlocal x
  have hq := cappedCoulombPotential_lt_top μ r hr x
  have hle : (cappedCoulombPotential μ r x).toReal ≤ (coulombPotential μ x).toReal :=
    ENNReal.toReal_mono hp.ne (cappedCoulombPotential_le μ r x)
  have hu := ENNReal.toReal_mono
    (ENNReal.add_lt_top.mpr ⟨hq, ENNReal.ofReal_lt_top⟩).ne
    (coulombPotential_le_capped_add_of_local_bound μ C r hr hlocal x)
  rw [ENNReal.toReal_add hq.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg hC hr.le)] at hu
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
  linarith only [hu]

/-- Uniform local control gives continuity of the finite real-valued potential. -/
theorem continuous_toReal_coulombPotential_of_local_bound (μ : Measure Position)
    [IsFiniteMeasure μ] (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ x : Position, ∀ ε : ℝ, 0 < ε →
      ∫⁻ y in Metric.ball x ε, coulombKernel x y ∂μ ≤ ENNReal.ofReal (C * ε)) :
    Continuous (fun x => (coulombPotential μ x).toReal) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  let r := ε / (2 * (C + 1))
  have hr : 0 < r := div_pos hε (mul_pos (by norm_num) (by linarith only [hC]))
  have hsmall : C * r < ε := by
    dsimp only [r]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (mul_pos (by norm_num) (by linarith only [hC]))).mpr
    nlinarith only [hC, hε]
  refine ⟨fun x => (cappedCoulombPotential μ r x).toReal,
    continuous_toReal_cappedCoulombPotential μ r hr, ?_⟩
  intro x
  apply hsub
  exact (dist_toReal_coulombPotential_capped_le μ C r hC hr hlocal x).trans_lt hsmall

end LiebThirring

end
