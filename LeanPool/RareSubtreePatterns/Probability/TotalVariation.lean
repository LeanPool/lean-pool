/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Defs
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Tactic.Linarith

/-!
# Probability-normalized total variation

The probability convention used for Poisson approximation is half of mathlib's
`MeasureTheory.tvDist`. For probability measures, the distance defined here is
in `[0, 1]` and is exactly the maximum absolute discrepancy over measurable
events. The event bound and its attained converse justify the normalization.

This is a general library bridge, not a proof of a Poisson approximation or of
any conditioned-tree theorem from the paper. The definition `paperTVDist` itself is in
`PoissonDeclumping.Statements.Defs` (shared verbatim with `Challenge.lean`).
-/

@[expose] public section

open MeasureTheory

namespace PoissonDeclumping

variable {α : Type*} [MeasurableSpace α]

/-- The normalized distance is nonnegative. -/
lemma paperTVDist_nonneg (μ ν : Measure α) : 0 ≤ paperTVDist μ ν :=
  div_nonneg tvDist_nonneg (by norm_num)

/-- A measure has zero distance from itself. -/
@[simp] lemma paperTVDist_self (μ : Measure α) : paperTVDist μ μ = 0 := by
  simp [paperTVDist]

/-- Symmetry of normalized total variation. -/
lemma paperTVDist_comm (μ ν : Measure α) : paperTVDist μ ν = paperTVDist ν μ := by
  rw [paperTVDist, paperTVDist, tvDist_comm]

private lemma abs_sub_measureReal_univ_le_tvDist (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    |μ.real Set.univ - ν.real Set.univ| ≤ tvDist μ ν := by
  have hfinite : (μ.toSignedMeasure - ν.toSignedMeasure).variation Set.univ ≠ ⊤ := by
    simpa only [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist] using
      etvDist_ne_top μ ν
  have h := VectorMeasure.norm_measure_le_variation hfinite
  simpa only [_root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    Real.norm_eq_abs, Measure.real, tvDist, etvDist_eq_etvDist_toSignedMeasure,
    VectorMeasure.etvDist] using h

/-- The probability difference of any measurable event is bounded by the
paper-normalized total variation distance. -/
lemma abs_sub_measureReal_le_paperTVDist (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| ≤ paperTVDist μ ν := by
  have h₁ := abs_sub_measureReal_univ_le_tvDist (μ.restrict s) (ν.restrict s)
  have h₂ := abs_sub_measureReal_univ_le_tvDist (μ.restrict sᶜ) (ν.restrict sᶜ)
  simp only [measureReal_restrict_apply_univ] at h₁ h₂
  have hcomp : |μ.real sᶜ - ν.real sᶜ| = |μ.real s - ν.real s| := by
    rw [probReal_compl_eq_one_sub hs, probReal_compl_eq_one_sub hs]
    have : (1 - μ.real s) - (1 - ν.real s) = -(μ.real s - ν.real s) := by ring
    rw [this, abs_neg]
  rw [hcomp] at h₂
  have hsplit := tvDist_restrict_add_compl (μ := μ) (ν := ν) hs
  dsimp [paperTVDist]
  linarith

/-- The normalized distance between probability measures is at most one. -/
lemma paperTVDist_le_one (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : paperTVDist μ ν ≤ 1 := by
  have h := tvDist_le_add (μ := μ) (ν := ν)
  simp only [probReal_univ] at h
  dsimp [paperTVDist]
  linarith

/-- On finite measures, zero distance characterizes equality. -/
@[simp] lemma paperTVDist_eq_zero_iff (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : paperTVDist μ ν = 0 ↔ μ = ν := by
  simp [paperTVDist]

/-- The triangle inequality, with the same finiteness condition as mathlib's
real-valued total variation distance. -/
lemma paperTVDist_triangle (μ ν ξ : Measure α) [IsFiniteMeasure ν] :
    paperTVDist μ ξ ≤ paperTVDist μ ν + paperTVDist ν ξ := by
  have h := tvDist_triangle μ ν ξ
  dsimp [paperTVDist]
  linarith

/-- A Hahn decomposition supplies a measurable event attaining the normalized
total variation distance between two probability measures. -/
lemma exists_measurableSet_abs_sub_measureReal_eq_paperTVDist (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ s : Set α, MeasurableSet s ∧ |μ.real s - ν.real s| = paperTVDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine ⟨s, hs.measurableSet, ?_⟩
  have ht := hs.tvDist_eq
  rw [probReal_compl_eq_one_sub hs.measurableSet,
    probReal_compl_eq_one_sub hs.measurableSet] at ht
  have hnonneg : 0 ≤ ν.real s - μ.real s := by
    have h := tvDist_nonneg (μ := μ) (ν := ν)
    linarith
  rw [abs_sub_comm, abs_of_nonneg hnonneg]
  dsimp [paperTVDist]
  linarith

/-- Bounding normalized total variation is equivalent to uniformly bounding
the probability discrepancy of every measurable event. -/
lemma paperTVDist_le_iff (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ε : ℝ) :
    paperTVDist μ ν ≤ ε ↔ ∀ s : Set α, MeasurableSet s → |μ.real s - ν.real s| ≤ ε := by
  constructor
  · intro h s hs
    exact (abs_sub_measureReal_le_paperTVDist μ ν hs).trans h
  · intro h
    obtain ⟨s, hs, heq⟩ := exists_measurableSet_abs_sub_measureReal_eq_paperTVDist μ ν
    rw [← heq]
    exact h s hs

end PoissonDeclumping
