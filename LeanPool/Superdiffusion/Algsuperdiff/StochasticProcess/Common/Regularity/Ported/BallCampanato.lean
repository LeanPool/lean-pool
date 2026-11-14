/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.BallPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CampanatoGeometry

/-!
# BallCampanato

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Campanato oscillation from the small-contrast gradient row
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- A fixed dimension-only top radius for the sup-ball Campanato telescope. -/
def smallContrastCampanatoRadius (d : ℕ) : ℝ := (12 * (d : ℝ))⁻¹

theorem smallContrastCampanatoRadius_pos [NeZero d] :
    0 < smallContrastCampanatoRadius d := by
  unfold smallContrastCampanatoRadius
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  positivity

theorem three_mul_dimension_mul_campanatoRadius [NeZero d] :
    3 * (d : ℝ) * smallContrastCampanatoRadius d = 1 / 4 := by
  unfold smallContrastCampanatoRadius
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne d
  field_simp
  ring

/-- The dimension-only Poincare/ball-comparison price. -/
def smallContrastCampanatoConstant (d : ℕ) : ℝ :=
  2 * (d : ℝ) * unitMeanZeroPoincareConst d * metricToEuclideanVolumePrice d

theorem smallContrastCampanatoConstant_nonneg (d : ℕ) :
    0 ≤ smallContrastCampanatoConstant d := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg d))
      (unitMeanZeroPoincareConst_nonneg d))
    (metricToEuclideanVolumePrice_nonneg d)

/-- Campanato oscillation on every sufficiently small sup-ball. -/
def HasSmallContrastBallCampanatoBound (alpha K : ℝ)
    (u : H1Function (smallContrastUnitBall d)) : Prop :=
  ∀ z ∈ smallContrastBall d (1 / 2), ∀ r : ℝ,
    0 < r → r ≤ 3 * smallContrastCampanatoRadius d →
    normalizedL2On (Metric.ball z r)
        (fun x => u.toFun x - volumeAverage (Metric.ball z r) u.toFun) ≤
      smallContrastCampanatoConstant d * K * r ^ alpha

private theorem r_mul_gradient_le_rpow_of_scale
    {alpha r N K : ℝ} (hr : 0 < r)
    (hscale : r ^ (1 - alpha) * N ≤ K) :
    r * N ≤ K * r ^ alpha := by
  have hrpow : r ^ alpha * r ^ (1 - alpha) = r := by
    rw [← Real.rpow_add hr]
    ring_nf
    rw [Real.rpow_one]
  have hpow : 0 ≤ r ^ alpha := Real.rpow_nonneg hr.le _
  have h := mul_le_mul_of_nonneg_left hscale hpow
  calc
    r * N = (r ^ alpha * r ^ (1 - alpha)) * N := by rw [hrpow]
    _ = r ^ alpha * (r ^ (1 - alpha) * N) := by ring
    _ ≤ r ^ alpha * K := h
    _ = K * r ^ alpha := by ring

/-- Poincare converts the local Morrey-gradient row into the literal
Campanato mean-oscillation row. -/
theorem ballCampanatoBound_of_interiorGradient [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hgrad : HasInteriorSmallContrastGradientScaleBound alpha K u) :
    HasSmallContrastBallCampanatoBound alpha K u := by
  intro z hz r hr hrTop
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hdr : 0 < (d : ℝ) * r := mul_pos hdpos hr
  have hdrquarter : (d : ℝ) * r ≤ 1 / 4 := by
      calc
        (d : ℝ) * r ≤ (d : ℝ) * (3 * smallContrastCampanatoRadius d) :=
          mul_le_mul_of_nonneg_left hrTop hdpos.le
        _ = 1 / 4 := by
          rw [show (d : ℝ) * (3 * smallContrastCampanatoRadius d) =
            3 * (d : ℝ) * smallContrastCampanatoRadius d by ring,
            three_mul_dimension_mul_campanatoRadius]
  have hdrhalf : (d : ℝ) * r ≤ 1 / 2 :=
    hdrquarter.trans (by norm_num)
  have hparent : euclideanBall z ((d : ℝ) * r) ⊆ smallContrastUnitBall d :=
    subset_trans (euclideanBall_subset_euclideanBall hdr.le
      (hdrquarter.trans_lt (by norm_num) : (d : ℝ) * r < 1 / 2))
      (euclideanBall_half_subset_unit_of_mem_half hz)
  have hQparent : Metric.ball z r ⊆ euclideanBall z ((d : ℝ) * r) :=
    metricBall_subset_euclideanBall_dimension z r
  have hQunit : Metric.ball z r ⊆ smallContrastUnitBall d :=
    subset_trans hQparent hparent
  let uQ : H1Function (Metric.ball z r) :=
    u.restrict Metric.isOpen_ball hQunit
  have hpo := normalizedL2On_metricBall_sub_average_le_vectorGradient
    (d := d) z hr uQ
  have hparentPos : 0 < (volume (euclideanBall z ((d : ℝ) * r))).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hdr))
  have hQpos : 0 < (volume (Metric.ball z r)).toReal :=
    volume_metricBall_toReal_pos z hr
  have hgradParent : MemLp (fun x => HilbertVec.ofVec (u.grad x)) 2
      (volume.restrict (euclideanBall z ((d : ℝ) * r))) := by
    exact (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2).mono_measure
      (Measure.restrict_mono hparent le_rfl)
  have hsubset := vectorNormalizedL2On_le_of_subset hQparent hparentPos hQpos hgradParent
  rw [sqrt_volume_euclideanBall_dimension_div_metricBall z hr] at hsubset
  have hscale := hgrad z hz ((d : ℝ) * r) hdr hdrhalf
  have hdimScale : r ^ (1 - alpha) *
        vectorNormalizedL2On (euclideanBall z ((d : ℝ) * r)) u.grad ≤ K := by
    have hpowmono : r ^ (1 - alpha) ≤ ((d : ℝ) * r) ^ (1 - alpha) := by
      have hdOne : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
      exact Real.rpow_le_rpow hr.le
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hdOne hr.le)
        (sub_nonneg.mpr halpha.2.le)
    have hN : 0 ≤ vectorNormalizedL2On
        (euclideanBall z ((d : ℝ) * r)) u.grad :=
      normalizedL2On_nonneg _ _
    exact (mul_le_mul_of_nonneg_right hpowmono hN).trans hscale
  have hrgrad : r * vectorNormalizedL2On
        (euclideanBall z ((d : ℝ) * r)) u.grad ≤ K * r ^ alpha :=
    r_mul_gradient_le_rpow_of_scale hr hdimScale
  have hconst : 0 ≤ unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) :=
    mul_nonneg (mul_nonneg (unitMeanZeroPoincareConst_nonneg d) (by positivity)) hdpos.le
  calc
    normalizedL2On (Metric.ball z r)
        (fun x => u.toFun x - volumeAverage (Metric.ball z r) u.toFun) =
      normalizedL2On (Metric.ball z r)
        (fun x => uQ.toFun x - volumeAverage (Metric.ball z r) uQ.toFun) := rfl
    _ ≤ unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) *
        vectorNormalizedL2On (Metric.ball z r) uQ.grad := hpo
    _ ≤ unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) *
        (metricToEuclideanVolumePrice d *
          vectorNormalizedL2On (euclideanBall z ((d : ℝ) * r)) u.grad) :=
      mul_le_mul_of_nonneg_left hsubset hconst
    _ = smallContrastCampanatoConstant d *
        (r * vectorNormalizedL2On (euclideanBall z ((d : ℝ) * r)) u.grad) := by
      rw [smallContrastCampanatoConstant]
      ring
    _ ≤ smallContrastCampanatoConstant d * (K * r ^ alpha) :=
      mul_le_mul_of_nonneg_left hrgrad (smallContrastCampanatoConstant_nonneg d)
    _ = smallContrastCampanatoConstant d * K * r ^ alpha := by ring

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
