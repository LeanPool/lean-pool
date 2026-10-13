/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CampanatoHolder
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.StoppingCubeGeometry
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# CampanatoRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Identification of the small-contrast Campanato representative

Lebesgue differentiation identifies the dyadic Campanato limit with the raw
Sobolev representative almost everywhere.  Open sup-balls are used by the
Campanato estimate and closed sup-balls by the Besicovitch Vitali family; their
boundaries have zero Lebesgue measure.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport Filter Topology
open HCPolySupport.CubeCalderonZygmund

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

def smallContrastValueIndicator
    (u : H1Function (smallContrastUnitBall d)) : Vec d → ℝ :=
  Set.indicator (smallContrastUnitBall d) u.toFun

theorem smallContrastValueIndicator_of_mem
    {u : H1Function (smallContrastUnitBall d)} {x : Vec d}
    (hx : x ∈ smallContrastUnitBall d) :
    smallContrastValueIndicator u x = u.toFun x :=
  Set.indicator_of_mem hx _

theorem integrable_smallContrastValueIndicator
    (u : H1Function (smallContrastUnitBall d)) :
    Integrable (smallContrastValueIndicator u) volume := by
  let : IsFiniteMeasure (volume.restrict (smallContrastUnitBall d)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2
        (HCPolySupport.Book.Ch01.volume_euclideanBall_ne_top (0 : Vec d) 1)⟩
  have hu : IntegrableOn u.toFun (smallContrastUnitBall d) volume := by
    simpa only [IntegrableOn] using u.memL2.integrable one_le_two
  exact hu.integrable_indicator
    (isOpen_euclideanBall 0 (1 : ℝ)).measurableSet

theorem ae_tendsto_setAverage_smallContrastValueIndicator
    (u : H1Function (smallContrastUnitBall d)) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r,
          smallContrastValueIndicator u y ∂volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (smallContrastValueIndicator u x)) := by
  have hu := integrable_smallContrastValueIndicator u
  filter_upwards [
    (Besicovitch.vitaliFamily (volume : Measure (Vec d))).ae_tendsto_average
      hu.locallyIntegrable] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt (volume : Measure (Vec d)) x)

theorem volumeAverage_metricBall_eq_setAverage_closedBall [NeZero d]
    (x : Vec d) {r : ℝ} (hr : 0 < r) (f : Vec d → ℝ) :
    volumeAverage (Metric.ball x r) f =
      ⨍ y in Metric.closedBall x r, f y ∂volume := by
  have hae : Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
    have h := axisCube_stoppingAxisCubeCorner_ae_eq_closedBall x
      (S := 1) (r := r) (by norm_num) hr
    rw [axisCube_stoppingAxisCubeCorner_eq_ball x (by norm_num) hr] at h
    simpa only [one_mul] using h
  rw [volumeAverage, setAverage_eq, smul_eq_mul, ← measureReal_def,
    measureReal_congr hae, setIntegral_congr_set hae]

theorem tendsto_smallContrastDyadicRadius_zero [NeZero d] :
    Tendsto (smallContrastDyadicRadius (smallContrastCampanatoRadius d)) atTop
      (𝓝[>] (0 : ℝ)) := by
  have hR : 0 < smallContrastCampanatoRadius d := smallContrastCampanatoRadius_pos
  rw [show smallContrastDyadicRadius (smallContrastCampanatoRadius d) =
      fun n : ℕ => smallContrastCampanatoRadius d * (1 / 2 : ℝ) ^ n by
        funext n
        rw [smallContrastDyadicRadius, Real.rpow_natCast]]
  have hfull : Tendsto
      (fun n : ℕ => smallContrastCampanatoRadius d * (1 / 2 : ℝ) ^ n) atTop
      (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) (r := (1 / 2 : ℝ))
          (by norm_num) (by norm_num)) :
        Tendsto (fun n : ℕ => smallContrastCampanatoRadius d * (1 / 2 : ℝ) ^ n)
          atTop (𝓝 (smallContrastCampanatoRadius d * 0)))
  exact tendsto_inf.2
    ⟨hfull,
      tendsto_principal.2 (Eventually.of_forall fun n => mul_pos hR (by positivity))⟩

/-- The Campanato representative is the Sobolev representative almost
everywhere on the interior half-ball. -/
theorem campanatoRepresentative_ae_eq [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u) :
    smallContrastCampanatoRepresentative (d := d) u.toFun =ᵐ[
      volume.restrict (smallContrastBall d (1 / 2))] u.toFun := by
  refine (ae_restrict_iff'
    (isOpen_euclideanBall 0 (1 / 2 : ℝ)).measurableSet).2 ?_
  filter_upwards [ae_tendsto_setAverage_smallContrastValueIndicator u] with x hx hxin
  have hxunit : x ∈ smallContrastUnitBall d :=
    euclideanBall_subset_euclideanBall (by norm_num) (by norm_num) hxin
  have hballs : ∀ n : ℕ,
      Metric.ball x
          (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n) ⊆
        smallContrastUnitBall d := by
    intro n
    exact metricBall_dyadic_subset_unit hxin n
  have havg : ∀ n : ℕ,
      smallContrastCampanatoAverage (d := d) u.toFun x n =
        ⨍ y in Metric.closedBall x
          (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n),
            smallContrastValueIndicator u y ∂volume := by
    intro n
    have hr := smallContrastDyadicRadius_pos
      (smallContrastCampanatoRadius_pos (d := d)) n
    rw [smallContrastCampanatoAverage,
      volumeAverage_metricBall_eq_setAverage_closedBall x hr]
    apply setAverage_congr_fun measurableSet_closedBall
    have haeBall : Metric.ball x
        (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n) =ᵐ[volume]
        Metric.closedBall x
          (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n) := by
      have h := axisCube_stoppingAxisCubeCorner_ae_eq_closedBall x
        (S := 1)
        (r := smallContrastDyadicRadius (smallContrastCampanatoRadius d) n)
        (by norm_num) hr
      rw [axisCube_stoppingAxisCubeCorner_eq_ball x (by norm_num) hr] at h
      simpa only [one_mul] using h
    filter_upwards [haeBall] with y hy
    intro hyclosed
    have hyopen : y ∈ Metric.ball x
        (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n) :=
      hy.mpr hyclosed
    exact (smallContrastValueIndicator_of_mem (hballs n hyopen)).symm
  have hLeb : Tendsto (smallContrastCampanatoAverage (d := d) u.toFun x) atTop
      (𝓝 (u.toFun x)) := by
    have hcomp := hx.comp (tendsto_smallContrastDyadicRadius_zero (d := d))
    rw [smallContrastValueIndicator_of_mem hxunit] at hcomp
    exact hcomp.congr' (Eventually.of_forall fun n => (havg n).symm)
  exact tendsto_nhds_unique
    (tendsto_smallContrastCampanatoAverage halpha hcamp hxin) hLeb

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
