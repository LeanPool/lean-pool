/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleSlices
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorDecay

/-!
# The radius along Cartesian coordinate slices

Along either coordinate slice `t ↦ wholePlaneSliceEquiv j (x, t)` of the plane, the Euclidean
radius tends to infinity at both ends (`tendsto_norm_wholePlaneSliceEquiv_atTop`,
`tendsto_norm_wholePlaneSliceEquiv_atBot`); the slice depends continuously on its variable and
its norm dominates the varying coordinate.  These are the slice-geometry inputs of the
coordinate-slice integrations by parts in `Local/HorizontalModeH1.lean` and
`Local/HorizontalModeEigenpair.lean`.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace WholePlaneSliceRadius

open Filter Metric MeasureTheory Set Topology
open scoped SchwartzMap
open ComplexRadius
open PonomarenkoCartesianExteriorDecay

/-! ## Coordinate-slice geometry -/

/-- A coordinate slice depends continuously on its inner variable. -/
theorem wholePlaneSliceEquiv_continuous (j : Fin 2) (x : ℝ) :
    Continuous (fun t : ℝ ↦ wholePlaneSliceEquiv j (x, t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (wholePlaneSliceEquiv_hasDerivAt j x t).continuousAt

/-- The norm of a slice point dominates the absolute value of the varying coordinate. -/
theorem abs_le_norm_wholePlaneSliceEquiv (j : Fin 2) (x t : ℝ) :
    |t| ≤ ‖wholePlaneSliceEquiv j (x, t)‖ := by
  have h := PiLp.norm_apply_le (wholePlaneSliceEquiv j (x, t)) j
  simpa [wholePlaneSliceEquiv_apply_selected, Real.norm_eq_abs] using h

/-- The physical radius tends to infinity at the positive end of every coordinate slice. -/
theorem tendsto_norm_wholePlaneSliceEquiv_atTop (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ ‖wholePlaneSliceEquiv j (x, t)‖) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop |b|] with t ht
  have ht0 : 0 ≤ t := (abs_nonneg b).trans ht
  calc
    b ≤ |b| := le_abs_self b
    _ ≤ |t| := by simpa [abs_of_nonneg ht0] using ht
    _ ≤ ‖wholePlaneSliceEquiv j (x, t)‖ := abs_le_norm_wholePlaneSliceEquiv j x t

/-- The physical radius also tends to infinity at the negative end of every coordinate slice. -/
theorem tendsto_norm_wholePlaneSliceEquiv_atBot (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ ‖wholePlaneSliceEquiv j (x, t)‖) atBot atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [eventually_le_atBot (-|b|)] with t ht
  have ht0 : t ≤ 0 := ht.trans (neg_nonpos.mpr (abs_nonneg b))
  calc
    b ≤ |b| := le_abs_self b
    _ ≤ |t| := by rw [abs_of_nonpos ht0]; linarith
    _ ≤ ‖wholePlaneSliceEquiv j (x, t)‖ := abs_le_norm_wholePlaneSliceEquiv j x t

end WholePlaneSliceRadius
end FastDynamo
