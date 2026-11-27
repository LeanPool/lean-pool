/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import LeanPool.VenNullClockRoundRates.SphereModel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Normalized round area in Cartesian sphere coordinates
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace VenRateUpper

/-- The three-dimensional Euclidean ambient space. -/
abbrev RoundAmbient := EuclideanSpace ℝ (Fin 3)
/-- The unit metric sphere around the origin in the Euclidean ambient space. -/
abbrev MetricUnitSphere := Metric.sphere (0 : RoundAmbient) 1

instance : BorelSpace VenMask.UnitSphere := by
  change BorelSpace {q : ℝ × ℝ × ℝ // q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1}
  infer_instance

/-- Map the Euclidean sphere to the Cartesian sphere of the observation model. -/
def fromMetricSphere (q : MetricUnitSphere) : VenMask.UnitSphere :=
  ⟨(q.1 0, q.1 1, q.1 2), by
    have h := mem_sphere_zero_iff_norm.mp q.2
    have hsq : ‖q.1‖ ^ 2 = 1 := by rw [h]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hsq
    exact hsq⟩

/-- Interpret a Cartesian point on the model sphere as a Euclidean unit vector. -/
def toMetricSphere (q : VenMask.UnitSphere) : MetricUnitSphere :=
  ⟨WithLp.toLp 2 ![q.val.1, q.val.2.1, q.val.2.2], by
    apply mem_sphere_zero_iff_norm.mpr
    have h : ‖(WithLp.toLp 2 ![q.val.1, q.val.2.1, q.val.2.2] : RoundAmbient)‖ ^ 2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, PiLp.toLp_apply] using q.property
    have h₀ : 0 ≤ ‖(WithLp.toLp 2 ![q.val.1, q.val.2.1, q.val.2.2] : RoundAmbient)‖ :=
      norm_nonneg _
    nlinarith⟩

/-- Cartesian coordinates identify the Euclidean sphere with the accepted sphere type. -/
def metricSphereHomeomorph : MetricUnitSphere ≃ₜ VenMask.UnitSphere where
  toFun := fromMetricSphere
  invFun := toMetricSphere
  left_inv q := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  right_inv q := by
    apply Subtype.ext
    rcases q with ⟨⟨x, y, z⟩, h⟩
    rfl
  continuous_toFun := by
    apply continuous_induced_rng.2
    have h (i : Fin 3) : Continuous (fun q : MetricUnitSphere ↦ q.1 i) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp continuous_subtype_val
    exact (h 0).prodMk ((h 1).prodMk (h 2))
  continuous_invFun := by
    apply continuous_induced_rng.2
    apply (PiLp.continuous_toLp 2 fun _ : Fin 3 ↦ ℝ).comp
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · exact continuous_fst.comp continuous_subtype_val
    · exact continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
    · exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)

/-- Euclidean area of the unit sphere, transported by the coordinate identification.
The Mathlib cone construction assigns each measurable patch three times the volume of
its unit radial cone. -/
def roundAreaUnnormalized : Measure VenMask.UnitSphere :=
  Measure.map metricSphereHomeomorph ((volume : Measure RoundAmbient).toSphere)

instance : IsFiniteMeasure roundAreaUnnormalized := by
  unfold roundAreaUnnormalized
  infer_instance

instance : roundAreaUnnormalized.IsOpenPosMeasure :=
  metricSphereHomeomorph.continuous.isOpenPosMeasure_map
    (μ := (volume : Measure RoundAmbient).toSphere) metricSphereHomeomorph.surjective

private theorem roundAreaUnnormalized_ne_zero : roundAreaUnnormalized univ ≠ 0 := by
  rw [roundAreaUnnormalized, Measure.map_apply metricSphereHomeomorph.measurable
    MeasurableSet.univ, preimage_univ]
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by simp)
    (Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.2 zero_lt_one))

/-- Normalized Euclidean round area on the accepted sphere. -/
def roundArea : Measure VenMask.UnitSphere :=
  (roundAreaUnnormalized univ)⁻¹ • roundAreaUnnormalized

instance instProbabilityRoundArea : IsProbabilityMeasure roundArea where
  measure_univ := ENNReal.inv_mul_cancel roundAreaUnnormalized_ne_zero
    (measure_ne_top roundAreaUnnormalized univ)

instance instOpenPosRoundArea : roundArea.IsOpenPosMeasure where
  open_pos U hU hne := by
    rw [roundArea, smul_apply, smul_eq_mul]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top roundAreaUnnormalized univ))
      (hU.measure_ne_zero roundAreaUnnormalized hne)

theorem roundAreaUnnormalized_apply {U : Set VenMask.UnitSphere} (hU : MeasurableSet U) :
    roundAreaUnnormalized U =
      3 * (volume : Measure RoundAmbient)
        (Ioo (0 : ℝ) 1 • (Subtype.val '' (metricSphereHomeomorph ⁻¹' U))) := by
  rw [roundAreaUnnormalized, Measure.map_apply metricSphereHomeomorph.measurable hU,
    Measure.toSphere_apply' _ (metricSphereHomeomorph.measurable hU)]
  simp

end VenRateUpper
