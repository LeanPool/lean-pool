/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4780T1HullHalfspaces
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

-- [TABLET NODE: P4780T1IntegerCoverage]

/-!
# P4780T1IntegerCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1IntegerCoverage :
    (⋃ k : Int × Int,
      (fun p : Real × Real => p + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon) = Set.univ := by
-- BODY
  ext p
  simp only [Set.mem_univ, iff_true, Set.mem_iUnion]
  let m : Int := ⌊p.1⌋
  let n : Int := ⌊p.2⌋
  let u : Real := p.1 - (m : Real)
  let v : Real := p.2 - (n : Real)
  have hu0 : 0 ≤ u := sub_nonneg.mpr (Int.floor_le p.1)
  have hv0 : 0 ≤ v := sub_nonneg.mpr (Int.floor_le p.2)
  have hu1 : u < 1 := Int.fract_lt_one p.1
  have hv1 : v < 1 := Int.fract_lt_one p.2
  suffices ∃ i j : Int, (u - (i : Real), v - (j : Real)) ∈ P4715T1Hexagon by
    rcases this with ⟨i, j, hij⟩
    refine ⟨(m + i, n + j), _, hij, ?_⟩
    ext <;> simp [u, v, Int.cast_add]
  by_cases hA : u ≤ 2*v
  · by_cases hB : 2*u-v ≤ 1
    · refine ⟨1, 1, ?_⟩
      rw [P4780T1HullHalfspaces]
      norm_num only [Int.cast_ofNat]
      change -2 ≤ 2*(u-1)-(v-1) ∧ 2*(u-1)-(v-1) ≤ 0 ∧
        -1 ≤ (u-1)-2*(v-1) ∧ (u-1)-2*(v-1) ≤ 1 ∧
        -2 ≤ (u-1)+(v-1) ∧ (u-1)+(v-1) ≤ 0
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩
    · have hsum : 1 ≤ u+v := by linarith
      refine ⟨2, 1, ?_⟩
      rw [P4780T1HullHalfspaces]
      norm_num only [Int.cast_ofNat]
      change -2 ≤ 2*(u-2)-(v-1) ∧ 2*(u-2)-(v-1) ≤ 0 ∧
        -1 ≤ (u-2)-2*(v-1) ∧ (u-2)-2*(v-1) ≤ 1 ∧
        -2 ≤ (u-2)+(v-1) ∧ (u-2)+(v-1) ≤ 0
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩
  · by_cases hsum : u+v ≤ 1
    · refine ⟨1, 0, ?_⟩
      rw [P4780T1HullHalfspaces]
      norm_num only [Int.cast_ofNat, Int.cast_zero]
      change -2 ≤ 2*(u-1)-(v-0) ∧ 2*(u-1)-(v-0) ≤ 0 ∧
        -1 ≤ (u-1)-2*(v-0) ∧ (u-1)-2*(v-0) ≤ 1 ∧
        -2 ≤ (u-1)+(v-0) ∧ (u-1)+(v-0) ≤ 0
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩
    · have hX : 1 < 2*u-v := by linarith
      refine ⟨2, 1, ?_⟩
      rw [P4780T1HullHalfspaces]
      norm_num only [Int.cast_ofNat]
      change -2 ≤ 2*(u-2)-(v-1) ∧ 2*(u-2)-(v-1) ≤ 0 ∧
        -1 ≤ (u-2)-2*(v-1) ∧ (u-2)-2*(v-1) ≤ 1 ∧
        -2 ≤ (u-2)+(v-1) ∧ (u-2)+(v-1) ≤ 0
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩

end ApollonianSuperharmonic

end
