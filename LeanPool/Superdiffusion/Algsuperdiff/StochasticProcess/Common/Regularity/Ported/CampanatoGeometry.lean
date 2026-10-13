/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.BallForcing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.GradientScaleReadout
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderBridge
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# CampanatoGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Sup-ball geometry for the small-contrast Campanato readout

The Campanato telescope is run on the ambient sup-balls.  Their volume is
exactly `(2*r)^d`, while the local gradient estimate is available on the
containing Euclidean ball of radius `d*r`.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

theorem euclideanBall_half_subset_unit_of_mem_half [NeZero d]
    {z : Vec d} (hz : z ∈ smallContrastBall d (1 / 2)) :
    euclideanBall z (1 / 2) ⊆ smallContrastUnitBall d := by
  apply euclideanBall_subset_of_center_distance_add_lt
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hzE := (mem_euclideanBall_toEuc_iff z 0
    (by norm_num : (0 : ℝ) < 1 / 2)).2 hz
  have hzlt : euclideanNorm z < 1 / 2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hzE
    have heq : ‖toEuc z - toEuc 0‖ = euclideanNorm z := by
      unfold euclideanNorm
      rw [show vecNormSq z = euclideanSqDist z 0 by
        simp [euclideanSqDist, vecNormSq]]
      rw [← norm_sq_toEuc_sub z 0, Real.sqrt_sq (norm_nonneg _)]
    rw [heq] at hzE
    exact hzE
  simpa only [sub_zero] using
    (show euclideanNorm z + 1 / 2 ≤ 1 by linarith only [hzlt])

/-- Every sup-ball of radius `r` is contained in the Euclidean ball of radius
`d*r`. -/
theorem metricBall_subset_euclideanBall_dimension [NeZero d]
    (z : Vec d) (r : ℝ) :
    Metric.ball z r ⊆ euclideanBall z ((d : ℝ) * r) := by
  intro x hx
  have hsup : ‖x - z‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hE := euclideanNorm_le_dimension_mul_norm (x - z)
  have hlt : euclideanNorm (x - z) < (d : ℝ) * r :=
    lt_of_le_of_lt hE (mul_lt_mul_of_pos_left hsup (by
      have : 0 < (d : ℝ) := by
        by_contra h
        have : (d : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg d)
        exact (NeZero.ne d) (Nat.cast_eq_zero.mp this)
      exact this))
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hsup
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hradius : 0 < (d : ℝ) * r := mul_pos hdpos hrpos
  apply (mem_euclideanBall_toEuc_iff x z hradius).1
  rw [Metric.mem_ball, dist_eq_norm]
  have heq : ‖toEuc x - toEuc z‖ = euclideanNorm (x - z) := by
    unfold euclideanNorm
    change ‖toEuc x - toEuc z‖ = Real.sqrt (euclideanSqDist x z)
    rw [← norm_sq_toEuc_sub x z, Real.sqrt_sq (norm_nonneg _)]
  rwa [heq]

/-- Real volume of a positive-radius sup-ball. -/
theorem volume_metricBall_toReal (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball z r)).toReal = (2 * r) ^ d := by
  rw [Real.volume_pi_ball z hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem volume_metricBall_toReal_pos (z : Vec d) {r : ℝ} (hr : 0 < r) :
    0 < (volume (Metric.ball z r)).toReal := by
  rw [volume_metricBall_toReal z hr]
  positivity

/-- The exact normalized-volume price from a radius-`r` sup-ball to its
Euclidean radius-`d*r` parent. -/
def metricToEuclideanVolumePrice (d : ℕ) : ℝ :=
  Real.sqrt
    ((volume (smallContrastUnitBall d)).toReal * (d : ℝ) ^ d / (2 : ℝ) ^ d)

theorem metricToEuclideanVolumePrice_nonneg (d : ℕ) :
    0 ≤ metricToEuclideanVolumePrice d :=
  Real.sqrt_nonneg _

theorem sqrt_volume_euclideanBall_dimension_div_metricBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((volume (euclideanBall z ((d : ℝ) * r))).toReal /
        (volume (Metric.ball z r)).toReal) =
      metricToEuclideanVolumePrice d := by
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [volume_euclideanBall_toReal_eq_unit_mul_pow z (mul_pos hdpos hr),
    volume_metricBall_toReal z hr]
  unfold metricToEuclideanVolumePrice
  congr 1
  rw [mul_pow]
  rw [mul_pow]
  field_simp [ne_of_gt hr, ne_of_gt hdpos]

/-- Normalized `L²` volume price for enlarging a sup-ball radius by `k`. -/
def ballVolumePrice (k : ℝ) (d : ℕ) : ℝ := Real.sqrt (k ^ d)

theorem ballVolumePrice_nonneg (k : ℝ) (d : ℕ) :
    0 ≤ ballVolumePrice k d := Real.sqrt_nonneg _

/-- Exact normalized-volume ratio for two sup-balls whose radii differ by a
positive factor `k`; their centres may differ because Lebesgue volume is
translation invariant. -/
theorem sqrt_volume_metricBall_ratio
    (x y : Vec d) {R r k : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hR : R = k * r) :
    Real.sqrt ((volume (Metric.ball x R)).toReal /
        (volume (Metric.ball y r)).toReal) = ballVolumePrice k d := by
  rw [volume_metricBall_toReal x (hR.symm ▸ mul_pos hk hr),
    volume_metricBall_toReal y hr]
  unfold ballVolumePrice
  congr 1
  rw [hR, show 2 * (k * r) = k * (2 * r) by ring, mul_pow]
  field_simp [hr.ne']

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
