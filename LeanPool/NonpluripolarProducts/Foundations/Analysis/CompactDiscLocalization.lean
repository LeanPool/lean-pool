/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Plurisubharmonic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Tactic.Linarith

/-!
# Uniform compact neighborhoods for a family of complex discs

A compact subset of an open set has a positive closed thickening contained in
that open set. The estimate `‖z • v‖ ≤ R * ‖v‖` then gives one compact set
containing every sufficiently small affine disc centered in the compact set.
The radius `δ / (‖v‖ + 1)` works even when `v = 0`. No nonemptiness of the
compact set is assumed; a thickening of the empty set remains empty.
-/

@[expose] public section

open Set Metric

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Increasing the radius enlarges an affine closed disc. -/
theorem affineClosedDisc_mono_radius (x v : E) {r R : ℝ} (hrR : r ≤ R) :
    affineClosedDisc x v r ⊆ affineClosedDisc x v R :=
  image_mono (closedBall_subset_closedBall hrR)

/-- The metric radius of an affine disc is bounded by the parameter radius
times the norm of its direction. Negative radii cause no exception: the disc
is then empty. -/
theorem affineClosedDisc_subset_closedBall (x v : E) (r : ℝ) :
    affineClosedDisc x v r ⊆ closedBall x (r * ‖v‖) := by
  rintro y ⟨z, hz, rfl⟩
  have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul] using
    mul_le_mul_of_nonneg_right hz' (norm_nonneg v)

/-- A disc centered in a set lies in its closed thickening when its metric
radius is no larger than the thickening radius. -/
theorem affineClosedDisc_subset_cthickening {K : Set E} {x : E} (hx : x ∈ K)
    (v : E) {r δ : ℝ} (hrδ : r * ‖v‖ ≤ δ) :
    affineClosedDisc x v r ⊆ cthickening δ K :=
  (affineClosedDisc_subset_closedBall x v r).trans
    ((closedBall_subset_closedBall hrδ).trans (closedBall_subset_cthickening hx δ))

/-- In a proper complex normed space, sufficiently small discs with centers in
a compact subset of an open set all lie in one compact subset of that open set.
This also applies to an empty compact set. -/
theorem exists_compact_affineClosedDisc_neighborhood [ProperSpace E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (v : E) :
    ∃ R > 0, ∃ L : Set E, IsCompact L ∧ L ⊆ U ∧
      ∀ x ∈ K, affineClosedDisc x v R ⊆ L := by
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; linarith
  have hδU : cthickening δ K ⊆ U :=
    (cthickening_subset_thickening' hε hδε K).trans hεU
  have hv : 0 < ‖v‖ + 1 := by positivity
  let R : ℝ := δ / (‖v‖ + 1)
  have hR : 0 < R := div_pos hδ hv
  have hRδ : R * ‖v‖ ≤ δ := by
    calc
      R * ‖v‖ ≤ R * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hR.le
      _ = δ := div_mul_cancel₀ δ (ne_of_gt hv)
  refine ⟨R, hR, cthickening δ K, hK.cthickening, hδU, ?_⟩
  exact fun x hx ↦ affineClosedDisc_subset_cthickening hx v hRδ

/-- The finite-dimensional form, with every smaller radius included. The same
compact set also contains all centers. The real and complex scalar actions
need no extra relation for this purely metric assertion. -/
theorem exists_compact_affineClosedDisc_family [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (v : E) :
    ∃ R > 0, ∃ L : Set E, IsCompact L ∧ L ⊆ U ∧ K ⊆ L ∧
      ∀ x ∈ K, ∀ r : ℝ, r ≤ R → affineClosedDisc x v r ⊆ L := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨R, hR, L, hL, hLU, hdisc⟩ :=
    exists_compact_affineClosedDisc_neighborhood hK hU hKU v
  refine ⟨R, hR, L, hL, hLU, ?_, ?_⟩
  · intro x hx
    exact hdisc x hx (center_mem_affineClosedDisc x v hR.le)
  · intro x hx r hr
    exact (affineClosedDisc_mono_radius x v hr).trans (hdisc x hx)

end SGPT.Foundations.Analysis
