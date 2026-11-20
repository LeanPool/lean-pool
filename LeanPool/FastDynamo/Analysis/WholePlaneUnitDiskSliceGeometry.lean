/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneTwoJumpIntegrationByParts

/-!
# Unit-disk slice geometry for two-jump integration by parts

The disk geometry used with the two-jump slice identity of
`FastDynamo/Analysis/WholePlaneTwoJumpIntegrationByParts.lean`.  For transverse parameters
in `(-1, 1)` the slice endpoints are the circle intersections `±sqrt (1 - x^2)`; on
exterior fibres the artificial separated endpoints `-1` and `1` are used, the middle branch is
the exterior field as well, and both artificial jumps vanish.  The module provides these
endpoints, the membership facts for slice points on interior and exterior fibres, and the
fact that almost every transverse parameter is interior or exterior (tangent fibres form a
null set).

The module is separate from `FastDynamo/Analysis/WholePlaneTwoJumpIntegrationByParts.lean`
for build weight: nothing in the one-dimensional identity there refers to any declaration
below.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set Topology
open scoped LineDeriv SchwartzMap

/-- Half the length of a formal unit-disk coordinate chord.  It is used geometrically only for
transverse coordinates in `(-1, 1)`. -/
def wholePlaneUnitDiskSliceRadius (x : ℝ) : ℝ :=
  Real.sqrt (1 - x ^ 2)

/-- Lower slice endpoint: the lower circle point on interior fibers and `-1` on
exterior fibers. -/
def wholePlaneUnitDiskSliceLower (x : ℝ) : ℝ :=
  if x ∈ Ioo (-1 : ℝ) 1 then -wholePlaneUnitDiskSliceRadius x else -1

/-- Upper slice endpoint: the upper circle point on interior fibers and `1` on
exterior fibers. -/
def wholePlaneUnitDiskSliceUpper (x : ℝ) : ℝ :=
  if x ∈ Ioo (-1 : ℝ) 1 then wholePlaneUnitDiskSliceRadius x else 1

/-- The artificial convention keeps the two endpoints separated on every fiber. -/
theorem wholePlaneUnitDiskSliceLower_lt_upper (x : ℝ) :
    wholePlaneUnitDiskSliceLower x < wholePlaneUnitDiskSliceUpper x := by
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · rw [wholePlaneUnitDiskSliceLower, wholePlaneUnitDiskSliceUpper,
      ite_eq_left hx, ite_eq_left hx]
    have hrad : 0 < wholePlaneUnitDiskSliceRadius x := by
      apply Real.sqrt_pos.2
      rcases hx with ⟨hxLower, hxUpper⟩
      nlinarith
    linarith
  · rw [wholePlaneUnitDiskSliceLower, wholePlaneUnitDiskSliceUpper,
      ite_eq_right hx, ite_eq_right hx]
    norm_num

/-- On an interior transverse fiber, the entire interval between the chosen endpoints lies in
the closed unit disk. -/
theorem wholePlaneSliceEquiv_mem_unitDisk_of_mem_endpointInterval
    (j : Fin 2) {x t : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Icc (wholePlaneUnitDiskSliceLower x)
      (wholePlaneUnitDiskSliceUpper x)) :
    wholePlaneSliceEquiv j (x, t) ∈ wholePlaneUnitDisk := by
  have ht' : -wholePlaneUnitDiskSliceRadius x ≤ t ∧
      t ≤ wholePlaneUnitDiskSliceRadius x := by
    simpa [wholePlaneUnitDiskSliceLower, wholePlaneUnitDiskSliceUpper, hx] using ht
  have hnonneg : 0 ≤ 1 - x ^ 2 := by
    rcases hx with ⟨hxLower, hxUpper⟩
    nlinarith
  have hradius : (wholePlaneUnitDiskSliceRadius x) ^ 2 = 1 - x ^ 2 := by
    simpa [wholePlaneUnitDiskSliceRadius] using Real.sq_sqrt hnonneg
  have hradiusNonneg : 0 ≤ wholePlaneUnitDiskSliceRadius x := Real.sqrt_nonneg _
  have htSq : t ^ 2 ≤ (wholePlaneUnitDiskSliceRadius x) ^ 2 := by
    nlinarith [sq_nonneg (t + wholePlaneUnitDiskSliceRadius x),
      sq_nonneg (wholePlaneUnitDiskSliceRadius x - t)]
  have hnormSq := norm_sq_wholePlaneSliceEquiv j x t
  have hnorm : ‖wholePlaneSliceEquiv j (x, t)‖ ≤ 1 := by
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t))]
  rw [wholePlaneUnitDisk, Metric.mem_closedBall]
  simpa only [dist_zero_right] using hnorm

/-- Away from the closed transverse interval `[-1, 1]`, every point of the coordinate fiber is
outside the closed unit disk. -/
theorem wholePlaneSliceEquiv_notMem_unitDisk_of_transverse_notMem
    (j : Fin 2) {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) (t : ℝ) :
    wholePlaneSliceEquiv j (x, t) ∉ wholePlaneUnitDisk := by
  have hxOuter : x < -1 ∨ 1 < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  have hxSq : 1 < x ^ 2 := by
    rcases hxOuter with hxLower | hxUpper <;> nlinarith [sq_nonneg x]
  have hnormSq := norm_sq_wholePlaneSliceEquiv j x t
  have hnorm : 1 < ‖wholePlaneSliceEquiv j (x, t)‖ := by
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t)), sq_nonneg t]
  intro hmem
  have hle : ‖wholePlaneSliceEquiv j (x, t)‖ ≤ 1 := by
    simpa [wholePlaneUnitDisk, Metric.mem_closedBall] using hmem
  exact (not_lt_of_ge hle) hnorm

/-- Except for the two tangent parameters, every outer coordinate is either a
two-crossing fiber or a strict exterior fiber. -/
theorem ae_mem_unitDiskSliceInterior_or_transverse_notMem :
    ∀ᵐ x : ℝ ∂volume,
      x ∈ Ioo (-1 : ℝ) 1 ∨ x ∉ Icc (-1 : ℝ) 1 := by
  filter_upwards [(volume : Measure ℝ).ae_ne (-1 : ℝ),
    (volume : Measure ℝ).ae_ne (1 : ℝ)] with x hxLower hxUpper
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · exact Or.inl hx
  · refine Or.inr ?_
    intro hxClosed
    apply hx
    exact ⟨lt_of_le_of_ne hxClosed.1 hxLower.symm,
      lt_of_le_of_ne hxClosed.2 hxUpper⟩

/-- A point of an open unit-disk slice has Euclidean norm strictly less than
one. -/
theorem norm_wholePlaneSliceEquiv_lt_one_of_mem_open_endpointInterval
    (j : Fin 2) {x t : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (wholePlaneUnitDiskSliceLower x)
      (wholePlaneUnitDiskSliceUpper x)) :
    ‖wholePlaneSliceEquiv j (x, t)‖ < 1 := by
  have hnonneg : 0 ≤ 1 - x ^ 2 := by
    rcases hx with ⟨hxLower, hxUpper⟩
    nlinarith
  have hradius : (wholePlaneUnitDiskSliceRadius x) ^ 2 = 1 - x ^ 2 := by
    simpa [wholePlaneUnitDiskSliceRadius] using Real.sq_sqrt hnonneg
  have ht' : -wholePlaneUnitDiskSliceRadius x < t ∧
      t < wholePlaneUnitDiskSliceRadius x := by
    simpa [wholePlaneUnitDiskSliceLower, wholePlaneUnitDiskSliceUpper, hx] using ht
  have hprod : 0 <
      (wholePlaneUnitDiskSliceRadius x - t) *
        (wholePlaneUnitDiskSliceRadius x + t) :=
    mul_pos (sub_pos.mpr ht'.2) (by linarith [ht'.1])
  have htSq : t ^ 2 < (wholePlaneUnitDiskSliceRadius x) ^ 2 := by
    nlinarith
  have hnormSq := norm_sq_wholePlaneSliceEquiv j x t
  nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t))]

end

end FastDynamo
