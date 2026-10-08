/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCell
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# High-contrast homogenization: Provider.Recurrence.AlignedSubdivision

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The aligned subdivision of an adapted cell

The coarse-block properties taken from HC state that for a rounded grid `q` at
alignment `ℓ` and integers `p ≥ j ≥ ℓ` the cell `⋄_p^q` is partitioned by exactly
`3^{d(p-j)}` cells `z + ⋄_j^q` with `z ∈ 3^j 𝕃_q ∩ ⋄_p^q`, all of whose
translation vectors are integral.

The adapted cubes are open, so their union omits the interior
faces of the subdivision, a Lebesgue null set; the partition is a partition up to
a null set, which is the form in which `e.fixed.geometry.parent.child`
consumes it.  Concretely, a point of the parent cell that misses every child cell
has, in the coordinates of the grid, some coordinate exactly halfway between two
consecutive multiples of `3^j`, and the countably many hyperplanes carrying such
points are null.  Rounding each coordinate to the nearest multiple of `3^j`
produces the child containing the point, and the parent's own bounds place that
child's index in the admissible range.

Together with the containment, disjointness, counting and integrality clauses of
the companion files, this closes the aligned subdivision.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## The exceptional hyperplanes -/

/-- A coordinate hyperplane is null. -/
theorem volume_coord_eq (i : Fin d) (c : ℝ) :
    volume {x : Vec d | x i = c} = 0 := by
  classical
  have hsub : {x : Vec d | x i = c}
      ⊆ Set.pi Set.univ fun k => if k = i then ({c} : Set ℝ) else Set.univ := by
    intro x hx k _
    by_cases hk : k = i
    · subst hk; simpa using hx
    · simp [hk]
  refine measure_mono_null hsub ?_
  rw [volume_pi, MeasureTheory.Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The grid faces at scale `j` — the points with some coordinate exactly halfway
between two consecutive multiples of `3^j` — form a null set. -/
theorem volume_gridFaces (j : ℤ) :
    volume (⋃ (i : Fin d) (k : ℤ), {x : Vec d | x i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ j})
      = 0 :=
  measure_iUnion_null fun i => measure_iUnion_null fun _ => volume_coord_eq i _

/-! ## Rounding a point of the parent cube to a child -/

/-- **The children cover the parent cube off the grid faces.**  Rounding each
coordinate to the nearest multiple of `3^j` lands in an admissible child unless
the coordinate sits exactly on a face. -/
theorem centeredCube_subset_iUnion_standardCell_union_gridFaces {j p : ℤ} (hjp : j ≤ p) :
    centeredCube d p ⊆
      (⋃ w ∈ {w : Fin d → ℤ | ∀ i, 2 * |w i| < (3 : ℤ) ^ (p - j).toNat},
          standardCell d j w) ∪
        ⋃ (i : Fin d) (k : ℤ), {x : Vec d | x i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ j} := by
  classical
  intro x hx
  by_cases hface : ∃ (i : Fin d) (k : ℤ), x i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ j
  · obtain ⟨i, k, hik⟩ := hface
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, hik⟩⟩)
  push Not at hface
  have hc : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  obtain ⟨m, hm⟩ := odd_three_pow (p - j).toNat
  rw [mem_centeredCube_iff] at hx
  obtain ⟨w, hwdef⟩ : ∃ w : Fin d → ℤ, ∀ i, w i = ⌊x i / (3 : ℝ) ^ j + 1 / 2⌋ :=
    ⟨fun i => ⌊x i / (3 : ℝ) ^ j + 1 / 2⌋, fun _ => rfl⟩
  have hcancel : ∀ i, x i / (3 : ℝ) ^ j * (3 : ℝ) ^ j = x i := fun i =>
    div_mul_cancel₀ (x i) hc.ne'
  have hfloorle : ∀ i, ((w i : ℝ)) ≤ x i / (3 : ℝ) ^ j + 1 / 2 := by
    intro i
    rw [hwdef i]
    exact Int.floor_le (x i / (3 : ℝ) ^ j + 1 / 2)
  have hupper : ∀ i, x i / (3 : ℝ) ^ j < (w i : ℝ) + 1 / 2 := by
    intro i
    rw [hwdef i]
    have := Int.lt_floor_add_one (x i / (3 : ℝ) ^ j + 1 / 2)
    linarith only [this]
  have hlower : ∀ i, ((w i : ℝ)) - 1 / 2 < x i / (3 : ℝ) ^ j := by
    intro i
    rcases lt_or_eq_of_le (hfloorle i) with h | h
    · linarith only [h]
    · exfalso
      refine hface i (w i - 1) ?_
      have hstep : ((w i : ℝ)) - 1 / 2 = x i / (3 : ℝ) ^ j := by rw [h]; ring
      have hxi : x i = (((w i : ℝ)) - 1 / 2) * (3 : ℝ) ^ j := by
        rw [hstep, hcancel i]
      rw [hxi]
      push_cast
      ring
  have hmemcell : x ∈ standardCell d j w := by
    rw [mem_standardCell_iff]
    intro i
    constructor
    · have := mul_lt_mul_of_pos_right (hlower i) hc
      rw [hcancel i] at this
      exact this
    · have := mul_lt_mul_of_pos_right (hupper i) hc
      rw [hcancel i] at this
      exact this
  have hindex : ∀ i, 2 * |w i| < (3 : ℤ) ^ (p - j).toNat := by
    intro i
    obtain ⟨h1, h2⟩ := hx i
    rw [zpow_three_split hjp] at h1 h2
    have hR : x i / (3 : ℝ) ^ j < (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) / 2 := by
      refine lt_of_mul_lt_mul_right ?_ hc.le
      rw [hcancel i]
      linarith only [h2]
    have hL : -((((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) / 2) < x i / (3 : ℝ) ^ j := by
      refine lt_of_mul_lt_mul_right ?_ hc.le
      rw [hcancel i]
      linarith only [h1]
    have hRw : (2 : ℝ) * ((w i : ℝ)) < (((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) + 1 := by
      linarith only [hR, hfloorle i]
    have hLw : -((((3 : ℤ) ^ (p - j).toNat : ℤ) : ℝ) + 1) < (2 : ℝ) * ((w i : ℝ)) := by
      linarith only [hL, hupper i]
    have hRZ : 2 * w i < (3 : ℤ) ^ (p - j).toNat + 1 := by exact_mod_cast hRw
    have hLZ : -((3 : ℤ) ^ (p - j).toNat + 1) < 2 * w i := by exact_mod_cast hLw
    rcases abs_cases (w i) with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] <;> omega
  exact Or.inl (Set.mem_biUnion (by exact hindex) hmemcell)

/-- **The children of the parent cube cover it up to a null set.** -/
theorem volume_centeredCube_diff_iUnion_standardCell {j p : ℤ} (hjp : j ≤ p) :
    volume (centeredCube d p \
        ⋃ w ∈ {w : Fin d → ℤ | ∀ i, 2 * |w i| < (3 : ℤ) ^ (p - j).toNat},
          standardCell d j w) = 0 := by
  refine measure_mono_null ?_ (volume_gridFaces (d := d) j)
  intro x hx
  rcases centeredCube_subset_iUnion_standardCell_union_gridFaces hjp hx.1 with h | h
  · exact absurd h hx.2
  · exact h

/-! ## Transport to the adapted cells -/

/-- The image of a null set under a grid map is null. -/
theorem volume_image_matVecMul_eq_zero (q : Mat d) {s : Set (Vec d)} (hs : volume s = 0) :
    volume (matVecMul q '' s) = 0 := by
  have h := MeasureTheory.Measure.addHaar_image_linearMap
    (μ := (volume : Measure (Vec d))) (Matrix.mulVecLin q) s
  rw [hs, mul_zero] at h
  exact h

/-- **The aligned children cover the adapted parent cell up to a null set.**
This is the partition clause of the coarse-block properties taken from HC, in
the form `e.fixed.geometry.parent.child` consumes it. -/
theorem volume_adaptedCell_diff_iUnion_adaptedCellAt {q : Mat d} (hq : q.PosDef)
    {j p : ℤ} (hjp : j ≤ p) :
    volume (adaptedCell q p \
        ⋃ w ∈ {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p},
          adaptedCellAt q j w) = 0 := by
  have hindex : {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p}
      = {w : Fin d → ℤ | ∀ i, 2 * |w i| < (3 : ℤ) ^ (p - j).toNat} := by
    ext w
    exact adaptedCellCenter_mem_adaptedCell_iff hq hjp w
  have hunion : (⋃ w ∈ {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p},
      adaptedCellAt q j w)
      = matVecMul q '' ⋃ w ∈ {w : Fin d → ℤ | ∀ i, 2 * |w i| < (3 : ℤ) ^ (p - j).toNat},
        standardCell d j w := by
    rw [Set.image_iUnion₂, hindex]
    exact Set.iUnion₂_congr fun w _ => adaptedCellAt_eq_image q j w
  have himage : (adaptedCell q p \
      ⋃ w ∈ {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p},
        adaptedCellAt q j w)
      = matVecMul q '' (centeredCube d p \
        ⋃ w ∈ {w : Fin d → ℤ | ∀ i, 2 * |w i| < (3 : ℤ) ^ (p - j).toNat},
          standardCell d j w) := by
    rw [Set.image_sdiff (matVecMul_injective hq), hunion]
    rfl
  rw [himage]
  exact volume_image_matVecMul_eq_zero q (volume_centeredCube_diff_iUnion_standardCell hjp)

/-! ## The aligned subdivision -/

/-- **The aligned subdivision of the adapted cubes.**  For a rounded
grid at alignment `ℓ` and scales `ℓ ≤ j ≤ p`, the aligned scale-`j` cells whose
centers lie in `⋄_p^q` are contained in it, are pairwise disjoint, cover it up to
a null set, number exactly `3^{d(p-j)}`, and have integral translation
vectors. -/
theorem aligned_subdivision {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {j p : ℤ}
    (hlj : l ≤ j) (hjp : j ≤ p) :
    ∃ Z : Finset (Fin d → ℤ),
      ↑Z = {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p} ∧
        Z.card = 3 ^ (d * (p - j).toNat) ∧
        (∀ w ∈ Z, adaptedCellAt q j w ⊆ adaptedCell q p) ∧
        (↑Z : Set (Fin d → ℤ)).PairwiseDisjoint (adaptedCellAt q j) ∧
        volume (adaptedCell q p \
          ⋃ w ∈ (↑Z : Set (Fin d → ℤ)), adaptedCellAt q j w) = 0 ∧
        ∀ w ∈ Z, ∃ v : Fin d → ℤ,
          adaptedCellCenter q j w = fun i => (v i : ℝ) := by
  have hqPD : q.PosDef := posDef_of_isRoundedGrid hq
  obtain ⟨Z, hZ, hcard⟩ := exists_finset_adaptedCellCenter_mem hqPD hjp
  refine ⟨Z, hZ, hcard, fun w hw => ?_,
    fun w _ w' _ hww => disjoint_adaptedCellAt hqPD j hww, ?_,
    fun w _ => exists_intVec_adaptedCellCenter hq hlj w⟩
  · exact adaptedCellAt_subset_adaptedCell hqPD hjp
      ((Set.ext_iff.mp hZ w).mp (Finset.mem_coe.mpr hw))
  · rw [hZ]
    exact volume_adaptedCell_diff_iUnion_adaptedCellAt hqPD hjp

end

end Recurrence
end HighContrast
end HCPolySupport
