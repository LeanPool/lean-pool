/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasurePotential
import all LeanPool.LiebThirring.Electrostatics.Basic
public import LeanPool.LiebThirring.Electrostatics.PlaneLocal

/-!
# Decay of Coulomb potentials of planar densities

Away from a radius `r > 0`, the Coulomb kernel is bounded by `1/r`.

The far Coulomb contribution of any positive measure is controlled by its mass.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LiebThirring

/-- Away from a radius `r > 0`, the Coulomb kernel is bounded by `1/r`. -/
lemma coulombKernel_le_of_le_norm_sub (x y : Position) {r : ℝ}
    (hr : 0 < r) (hxy : r ≤ ‖x - y‖) :
    coulombKernel x y ≤ ENNReal.ofReal (1 / r) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos hr]
  exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal hxy)

/-- The far Coulomb contribution of any positive measure is controlled by its mass. -/
theorem lintegral_coulombKernel_compl_ball_le (μ : Measure Position) (x : Position)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in (Metric.ball x r)ᶜ, coulombKernel x y ∂μ) ≤
      ENNReal.ofReal (1 / r) * μ univ := by
  calc
    _ ≤ ∫⁻ _y in (Metric.ball x r)ᶜ, ENNReal.ofReal (1 / r) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with y hy
      apply coulombKernel_le_of_le_norm_sub x y hr
      simpa only [mem_compl_iff, Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev] using hy
    _ ≤ _ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact mul_le_mul_right (measure_mono (subset_univ _)) _

/-- planar integration controls any planar density bounded on the indicated ball. -/
theorem lintegral_coulombKernel_ball_withDensity_le (n b x : Position)
    (hn : ‖n‖ = 1) (F : PlaneFrame (affinePlane n b))
    (f : Position → ℝ≥0∞) (hf : Measurable f) (B : ℝ) {r : ℝ} (hr : 0 < r)
    (hfB : ∀ᵐ y ∂(planeMeasure F).restrict (Metric.ball x r), f y ≤ ENNReal.ofReal B) :
    (∫⁻ y in Metric.ball x r, coulombKernel x y ∂(planeMeasure F).withDensity f) ≤
      ENNReal.ofReal B * ENNReal.ofReal (2 * Real.pi * r) := by
  rw [restrict_withDensity Metric.isOpen_ball.measurableSet,
    lintegral_withDensity_eq_lintegral_mul _ hf (measurable_coulombKernel_right x)]
  calc
    _ ≤ ∫⁻ y in Metric.ball x r, ENNReal.ofReal B * coulombKernel x y ∂planeMeasure F := by
      apply lintegral_mono_ae
      filter_upwards [hfB] with y hy
      exact mul_le_mul_left hy _
    _ = ENNReal.ofReal B * ∫⁻ y in Metric.ball x r, coulombKernel x y ∂planeMeasure F :=
      lintegral_const_mul _ (measurable_coulombKernel_right x)
    _ ≤ _ := mul_le_mul_right
      (lintegral_coulombKernel_ball_planeMeasure_le n b x hn F hr) _

/-- Uniform potential bound for a bounded planar density of bounded mass. -/
theorem coulombPotential_withDensity_planeMeasure_le (n b : Position)
    (hn : ‖n‖ = 1) (F : PlaneFrame (affinePlane n b))
    (f : Position → ℝ≥0∞) (hf : Measurable f) (B m : ℝ)
    (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hfB : ∀ᵐ y ∂planeMeasure F, f y ≤ ENNReal.ofReal B)
    (hmass : (planeMeasure F).withDensity f univ ≤ ENNReal.ofReal m) (x : Position) :
    coulombPotential ((planeMeasure F).withDensity f) x ≤
      ENNReal.ofReal (2 * Real.pi * B + m) := by
  unfold coulombPotential
  rw [← lintegral_add_compl _ (Metric.isOpen_ball.measurableSet : MeasurableSet (Metric.ball x 1))]
  calc
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * Real.pi * 1) +
        ENNReal.ofReal (1 / (1 : ℝ)) * (planeMeasure F).withDensity f univ :=
      add_le_add
        (lintegral_coulombKernel_ball_withDensity_le n b x hn F f hf B
          zero_lt_one (ae_restrict_of_ae hfB))
        (lintegral_coulombKernel_compl_ball_le _ x zero_lt_one)
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * Real.pi) + ENNReal.ofReal m := by
      simpa only [mul_one, div_one, ENNReal.ofReal_one, one_mul] using
        add_le_add (le_refl (ENNReal.ofReal B * ENNReal.ofReal (2 * Real.pi))) hmass
    _ = _ := by
      rw [← ENNReal.ofReal_mul hB, mul_comm B, ENNReal.ofReal_add (by positivity) hm]

/-- Scalar cubic decay bound outside half the observation radius. -/
lemma cubic_decay_le_half_radius (A R t : ℝ) (hA : 0 ≤ A) (hR : 0 < R)
    (ht : 0 ≤ t) (hRt : R / 2 ≤ t) :
    A / (1 + t) ^ 3 ≤ 8 * A / R ^ 3 := by
  have hden : 0 < 1 + t := add_pos_of_pos_of_nonneg zero_lt_one ht
  have hbase : R ≤ 2 * (1 + t) := by linarith only [hRt]
  have hcube : R ^ 3 ≤ 8 * (1 + t) ^ 3 := by
    calc
      R ^ 3 ≤ (2 * (1 + t)) ^ 3 := pow_le_pow_left₀ hR.le hbase 3
      _ = _ := by ring
  rw [div_le_div_iff₀ (pow_pos hden 3) (pow_pos hR 3)]
  calc
    A * R ^ 3 ≤ A * (8 * (1 + t) ^ 3) := mul_le_mul_of_nonneg_left hcube hA
    _ = _ := by ring

/-- Points in the observation ball of half-radius lie outside half the origin-radius. -/
lemma half_norm_le_of_mem_ball (x y : Position)
    (hy : y ∈ Metric.ball x (‖x‖ / 2)) : ‖x‖ / 2 ≤ ‖y‖ := by
  have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hdist : ‖x - y‖ < ‖x‖ / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  linarith only [htri, hdist]

/-- Large-radius potential estimate from cubic density decay and bounded mass. -/
theorem coulombPotential_withDensity_planeMeasure_le_of_norm_pos (n b : Position)
    (hn : ‖n‖ = 1) (F : PlaneFrame (affinePlane n b))
    (f : Position → ℝ≥0∞) (hf : Measurable f) (A m : ℝ)
    (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hfA : ∀ᵐ y ∂planeMeasure F, f y ≤ ENNReal.ofReal (A / (1 + ‖y‖) ^ 3))
    (hmass : (planeMeasure F).withDensity f univ ≤ ENNReal.ofReal m)
    (x : Position) (hx : 0 < ‖x‖) :
    coulombPotential ((planeMeasure F).withDensity f) x ≤
      ENNReal.ofReal (2 * m / ‖x‖ + 8 * Real.pi * A / ‖x‖ ^ 2) := by
  have hr : 0 < ‖x‖ / 2 := half_pos hx
  have hfsmall : ∀ᵐ y ∂(planeMeasure F).restrict (Metric.ball x (‖x‖ / 2)),
      f y ≤ ENNReal.ofReal (8 * A / ‖x‖ ^ 3) := by
    filter_upwards [ae_restrict_of_ae hfA,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hfy hy
    exact hfy.trans (ENNReal.ofReal_le_ofReal
      (cubic_decay_le_half_radius A ‖x‖ ‖y‖ hA hx (norm_nonneg y)
        (half_norm_le_of_mem_ball x y hy)))
  unfold coulombPotential
  rw [← lintegral_add_compl _
    (Metric.isOpen_ball.measurableSet : MeasurableSet (Metric.ball x (‖x‖ / 2)))]
  calc
    _ ≤ ENNReal.ofReal (8 * A / ‖x‖ ^ 3) * ENNReal.ofReal (2 * Real.pi * (‖x‖ / 2)) +
        ENNReal.ofReal (1 / (‖x‖ / 2)) * (planeMeasure F).withDensity f univ :=
      add_le_add
        (lintegral_coulombKernel_ball_withDensity_le n b x hn F f hf _ hr hfsmall)
        (lintegral_coulombKernel_compl_ball_le _ x hr)
    _ ≤ ENNReal.ofReal (8 * A / ‖x‖ ^ 3) * ENNReal.ofReal (2 * Real.pi * (‖x‖ / 2)) +
        ENNReal.ofReal (1 / (‖x‖ / 2)) * ENNReal.ofReal m :=
      add_le_add le_rfl (mul_le_mul_right hmass _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * A / ‖x‖ ^ 3),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (‖x‖ / 2)),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      ring

/-- For radii at least one the quadratic tail is absorbed into the linear tail. -/
lemma coulomb_decay_majorant_le (A m R : ℝ) (hA : 0 ≤ A)
    (hR : 1 ≤ R) :
    2 * m / R + 8 * Real.pi * A / R ^ 2 ≤ (2 * m + 8 * Real.pi * A) / R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRR : R ≤ R ^ 2 := by nlinarith only [hR]
  calc
    _ ≤ 2 * m / R + 8 * Real.pi * A / R :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) hRpos hRR)
    _ = _ := (add_div _ _ _).symm

/-- The explicit uniform decay bound for a bounded, cubically decaying planar density. -/
theorem coulombPotential_withDensity_planeMeasure_decay (n b : Position)
    (hn : ‖n‖ = 1) (F : PlaneFrame (affinePlane n b))
    (f : Position → ℝ≥0∞) (hf : Measurable f) (A B m : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hfB : ∀ᵐ y ∂planeMeasure F, f y ≤ ENNReal.ofReal B)
    (hfA : ∀ᵐ y ∂planeMeasure F, f y ≤ ENNReal.ofReal (A / (1 + ‖y‖) ^ 3))
    (hmass : (planeMeasure F).withDensity f univ ≤ ENNReal.ofReal m) (x : Position) :
    coulombPotential ((planeMeasure F).withDensity f) x ≤
      ENNReal.ofReal ((4 * Real.pi * B + 6 * m + 16 * Real.pi * A) / (1 + ‖x‖)) := by
  let D : ℝ := 2 * Real.pi * B + m
  let E : ℝ := 2 * m + 8 * Real.pi * A
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hden : 0 < 1 + ‖x‖ := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg x)
  have hC : 4 * Real.pi * B + 6 * m + 16 * Real.pi * A = 2 * D + 2 * E := by
    dsimp [D, E]
    ring
  rw [hC]
  by_cases hxsmall : ‖x‖ ≤ 1
  · calc
      _ ≤ ENNReal.ofReal D :=
        coulombPotential_withDensity_planeMeasure_le n b hn F f hf B m hB hm hfB hmass x
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hden]
        calc
          D * (1 + ‖x‖) ≤ D * 2 :=
            mul_le_mul_of_nonneg_left (by linarith only [hxsmall]) hD
          _ ≤ 2 * D + 2 * E := by
            rw [mul_comm D 2]
            exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hE)
  · have hx : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hxsmall)
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
    calc
      _ ≤ ENNReal.ofReal (2 * m / ‖x‖ + 8 * Real.pi * A / ‖x‖ ^ 2) :=
        coulombPotential_withDensity_planeMeasure_le_of_norm_pos n b hn F f hf A m hA hm
          hfA hmass x hxpos
      _ ≤ ENNReal.ofReal (E / ‖x‖) :=
        ENNReal.ofReal_le_ofReal (coulomb_decay_majorant_le A m ‖x‖ hA hx)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_div_iff₀ hxpos hden]
        calc
          E * (1 + ‖x‖) ≤ E * (2 * ‖x‖) :=
            mul_le_mul_of_nonneg_left (by linarith only [hx]) hE
          _ ≤ (2 * D + 2 * E) * ‖x‖ := by
            have h := mul_nonneg hD (norm_nonneg x)
            nlinarith only [h]

/-- A pointwise inverse-radius potential bound implies decay at spatial infinity. -/
theorem tendsto_coulombPotential_zero_of_decay (μ : Measure Position) (C : ℝ)
    (hdecay : ∀ x : Position, coulombPotential μ x ≤ ENNReal.ofReal (C / (1 + ‖x‖))) :
    Tendsto (coulombPotential μ) (Bornology.cobounded Position) (𝓝 0) := by
  have hreal : Tendsto (fun x : Position => C / (1 + ‖x‖))
      (Bornology.cobounded Position) (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_const_nhds.add_atTop tendsto_norm_cobounded_atTop)
  have henn : Tendsto (fun x : Position => ENNReal.ofReal (C / (1 + ‖x‖)))
      (Bornology.cobounded Position) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0
      |>.comp hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henn
    (Eventually.of_forall (fun _ => bot_le)) (Eventually.of_forall hdecay)

end LiebThirring

end
