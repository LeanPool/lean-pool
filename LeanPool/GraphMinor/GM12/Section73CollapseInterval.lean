/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Collapsing a real interval in strip coordinates

For the radial-edge contractions in XII (7.3), page 261, flatten the
axis interval of a strip to its left endpoint. The map is increasing
on either side, and its only repeated values come from the flattened
interval. Interpolation with the identity is strictly increasing until
the final collapse. These facts supply the local coordinate map for
contracting a drawn edge.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set

/-- The axis map flattening `[l,r]` to `l`, used for the local edge
contraction in XII (7.3). Outside the interval it has positive slope. -/
def collapseInterval (l r x : ℝ) : ℝ := min x l + max (2 * (x - r)) 0

/-- The axis map is continuous. -/
theorem continuous_collapseInterval (l r : ℝ) : Continuous (collapseInterval l r) := by
  unfold collapseInterval
  fun_prop

/-- The axis map is monotone. -/
theorem monotone_collapseInterval (l r : ℝ) : Monotone (collapseInterval l r) := by
  intro x y hxy
  apply add_le_add (min_le_min_right l hxy)
  apply max_le_max _ le_rfl
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hxy r) (by norm_num)

/-- To the left of the interval, the map is the identity. -/
theorem collapseInterval_of_le {l r x : ℝ} (hlr : l ≤ r) (hx : x ≤ l) :
    collapseInterval l r x = x := by
  unfold collapseInterval
  rw [min_eq_left hx, max_eq_right (by linarith : 2 * (x - r) ≤ 0), add_zero]

/-- Every point of the interval maps to its left end. -/
theorem collapseInterval_of_mem {l r x : ℝ} (hx : x ∈ Icc l r) :
    collapseInterval l r x = l := by
  unfold collapseInterval
  rw [min_eq_right hx.1, max_eq_right (by linarith [hx.2] : 2 * (x - r) ≤ 0), add_zero]

/-- To the right, the map has slope two. -/
theorem collapseInterval_of_ge {l r x : ℝ} (hlr : l ≤ r) (hx : r ≤ x) :
    collapseInterval l r x = l + 2 * (x - r) := by
  unfold collapseInterval
  rw [min_eq_right (hlr.trans hx), max_eq_left (by linarith : 0 ≤ 2 * (x - r))]

private theorem collapseInterval_strict {l r x y : ℝ} (hlr : l ≤ r) (hxy : x < y)
    (hout : x < l ∨ r < y) : collapseInterval l r x < collapseInterval l r y := by
  rcases hout with hxl | hry
  · rw [collapseInterval_of_le hlr hxl.le]
    by_cases hyl : y ≤ l
    · rw [collapseInterval_of_le hlr hyl]
      exact hxy
    · have hle := monotone_collapseInterval l r (le_of_not_ge hyl)
      rw [collapseInterval_of_mem ⟨le_rfl, hlr⟩] at hle
      exact hxl.trans_le hle
  · rw [collapseInterval_of_ge hlr hry.le]
    by_cases hrx : r ≤ x
    · rw [collapseInterval_of_ge hlr hrx]
      linarith
    · have hle := monotone_collapseInterval l r (le_of_not_ge hrx)
      rw [collapseInterval_of_mem ⟨hlr, le_rfl⟩] at hle
      linarith

/-- The flattened interval is the only non-singleton fibre. -/
theorem collapseInterval_eq_iff {l r x y : ℝ} (hlr : l ≤ r) :
    collapseInterval l r x = collapseInterval l r y ↔
      x = y ∨ (x ∈ Icc l r ∧ y ∈ Icc l r) := by
  constructor
  · intro heq
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · right
      have hlx : l ≤ x := by
        by_contra hn
        exact (ne_of_lt (collapseInterval_strict hlr hxy (Or.inl (lt_of_not_ge hn)))) heq
      have hyr : y ≤ r := by
        by_contra hn
        exact (ne_of_lt (collapseInterval_strict hlr hxy (Or.inr (lt_of_not_ge hn)))) heq
      exact ⟨⟨hlx, hxy.le.trans hyr⟩, ⟨hlx.trans hxy.le, hyr⟩⟩
    · exact Or.inl hxy
    · right
      have hly : l ≤ y := by
        by_contra hn
        exact (ne_of_lt (collapseInterval_strict hlr hyx (Or.inl (lt_of_not_ge hn)))) heq.symm
      have hxr : x ≤ r := by
        by_contra hn
        exact (ne_of_lt (collapseInterval_strict hlr hyx (Or.inr (lt_of_not_ge hn)))) heq.symm
      exact ⟨⟨hly.trans hyx.le, hxr⟩, ⟨hly, hyx.le.trans hxr⟩⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [collapseInterval_of_mem hx, collapseInterval_of_mem hy]

/-- Interpolation remains monotone at the final collapse. -/
theorem collapseInterval_interpolation_monotone {l r t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Monotone (fun x => (1 - t) * x + t * collapseInterval l r x) := by
  intro x y hxy
  exact add_le_add (mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left (monotone_collapseInterval l r hxy) ht)

/-- Interpolation with the identity is strictly increasing before
the final collapse. -/
theorem collapseInterval_interpolation_strictMono {l r t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    StrictMono (fun x => (1 - t) * x + t * collapseInterval l r x) := by
  intro x y hxy
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxy (sub_pos.mpr ht1))
    (mul_le_mul_of_nonneg_left (monotone_collapseInterval l r hxy.le) ht)

/-- The strip endpoints stay fixed during interpolation. -/
theorem collapseInterval_interpolation_endpoints {l r t : ℝ} (hlr : l ≤ r) :
    ((1 - t) * (2 * l - r) + t * collapseInterval l r (2 * l - r) = 2 * l - r) ∧
      ((1 - t) * (2 * r - l) + t * collapseInterval l r (2 * r - l) = 2 * r - l) := by
  rw [collapseInterval_of_le hlr (by linarith), collapseInterval_of_ge hlr (by linarith)]
  constructor <;> ring

end GraphMinor.GM12
