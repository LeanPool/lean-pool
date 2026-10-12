/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.ProbabilityMoments
public import Mathlib.Probability.Kernel.Representation
import Mathlib.Tactic.Measurability

/-!
# Realization on the unit interval
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal unitInterval

namespace GrothendieckBessel

/-- Standard Borel realization of a probability measure by a map from
Mathlib's canonical measured unit interval. -/
theorem realization_on_unit_interval
    (X : Type*) [MeasurableSpace X] [StandardBorelSpace X]
    (_nonemptyX : Nonempty X)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ f : I → X, Measurable f ∧ Measure.map f volume = μ := by
  let := _nonemptyX
  exact Measure.exists_measurable_map_eq μ

/-- Extend one coordinate of a disk-product random variable on Mathlib's
canonical unit interval to an ambient representative on `ℝ`. -/
def unitIntervalRealizedCoordinate
    {J : Type*}
    (g : I → ClosedComplexUnitDiskProduct J) (j : J) : ℝ → ℂ :=
  Function.extend ((↑) : I → ℝ)
    (fun x : I => ((g x j : ClosedComplexUnitDisk) : ℂ))
    (fun _ : ℝ => 0)

theorem unitIntervalRealizedCoordinate_apply
    {J : Type*}
    (g : I → ClosedComplexUnitDiskProduct J) (j : J) (x : I) :
    unitIntervalRealizedCoordinate g j (x : ℝ) =
      ((g x j : ClosedComplexUnitDisk) : ℂ) := by
  simp [unitIntervalRealizedCoordinate]

theorem unitIntervalRealizedCoordinate_aestronglyMeasurable
    {J : Type*}
    {g : I → ClosedComplexUnitDiskProduct J}
    (hg_meas : Measurable g) (j : J) :
    AEStronglyMeasurable (unitIntervalRealizedCoordinate g j) (μOn unitInterval) := by
  have hcoord : Measurable fun x : I => ((g x j : ClosedComplexUnitDisk) : ℂ) := by
    measurability
  have hext : Measurable (unitIntervalRealizedCoordinate g j) := by
    exact unitInterval.measurableEmbedding_coe.measurable_extend hcoord measurable_const
  exact hext.aestronglyMeasurable

theorem unitIntervalRealizedCoordinate_bound
    {J : Type*}
    (g : I → ClosedComplexUnitDiskProduct J) (j : J) {t : ℝ}
    (ht : t ∈ unitInterval) :
    ‖unitIntervalRealizedCoordinate g j t‖ ≤ 1 := by
  let x : I := ⟨t, by simpa [unitInterval] using ht⟩
  have hx : (x : ℝ) = t := rfl
  rw [← hx, unitIntervalRealizedCoordinate_apply]
  exact ClosedComplexUnitDisk.norm_coe_le_one (g x j)

theorem unitIntervalRealizedCoordinate_moment
    {J : Type*} [Countable J]
    {ν : ProbabilityMeasure (ClosedComplexUnitDiskProduct J)}
    {g : I → ClosedComplexUnitDiskProduct J}
    (hg_meas : Measurable g)
    (hg_map : Measure.map g volume =
      (ν : Measure (ClosedComplexUnitDiskProduct J)))
    (j k : J) :
    l2InnerOn unitInterval (unitIntervalRealizedCoordinate g j)
        (unitIntervalRealizedCoordinate g k) =
      ∫ x, diskMomentBCF j k x
        ∂(ν : Measure (ClosedComplexUnitDiskProduct J)) := by
  have hcoe := unitInterval.measurePreserving_coe.integral_comp
    unitInterval.measurableEmbedding_coe
    (fun t : ℝ => unitIntervalRealizedCoordinate g j t *
      star (unitIntervalRealizedCoordinate g k t))
  unfold l2InnerOn
  change ∫ t : ℝ, unitIntervalRealizedCoordinate g j t *
      star (unitIntervalRealizedCoordinate g k t) ∂μOn unitInterval =
    ∫ x, diskMomentBCF j k x ∂(ν : Measure (ClosedComplexUnitDiskProduct J))
  rw [μOn]
  change ∫ t : ℝ, unitIntervalRealizedCoordinate g j t *
      star (unitIntervalRealizedCoordinate g k t) ∂volume.restrict unitInterval =
    ∫ x, diskMomentBCF j k x ∂(ν : Measure (ClosedComplexUnitDiskProduct J))
  have hcoe_unit :
      ∫ x : I, unitIntervalRealizedCoordinate g j (x : ℝ) *
          star (unitIntervalRealizedCoordinate g k (x : ℝ)) ∂volume =
        ∫ t : ℝ, unitIntervalRealizedCoordinate g j t *
          star (unitIntervalRealizedCoordinate g k t) ∂volume.restrict unitInterval := by
    simpa [unitInterval] using hcoe
  rw [← hcoe_unit]
  rw [← hg_map]
  rw [MeasureTheory.integral_map hg_meas.aemeasurable
    (by exact (diskMomentBCF j k).continuous.measurable.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with x
  simp [diskMomentBCF, unitIntervalRealizedCoordinate_apply]

/--
Countable bounded realization of a positive-contraction moment family on the
unit interval.
-/
theorem countable_unit_interval_realization
    {J : Type*} [Countable J]
    (h : J → J → ℂ)
    (hh : FiniteHermitianPositiveContraction h) :
    ∃ f : J → ℝ → ℂ,
      (∀ j, AEStronglyMeasurable (f j) (μOn unitInterval)) ∧
        (∀ j t, t ∈ unitInterval → ‖f j t‖ ≤ 1) ∧
          (∀ j k, l2InnerOn unitInterval (f j) (f k) = h j k) := by
  rcases countable_moment_measure h hh with ⟨ν, hν⟩
  rcases realization_on_unit_interval
      (ClosedComplexUnitDiskProduct J)
      (by infer_instance)
      (ν : Measure (ClosedComplexUnitDiskProduct J)) with
    ⟨g, hg_meas, hg_map⟩
  refine ⟨fun j => unitIntervalRealizedCoordinate g j, ?_, ?_, ?_⟩
  · intro j
    exact unitIntervalRealizedCoordinate_aestronglyMeasurable hg_meas j
  · intro j t ht
    exact unitIntervalRealizedCoordinate_bound g j ht
  · intro j k
    rw [unitIntervalRealizedCoordinate_moment hg_meas hg_map j k]
    exact hν j k

end GrothendieckBessel
