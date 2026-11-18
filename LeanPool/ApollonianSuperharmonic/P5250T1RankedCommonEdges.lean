/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices

-- [TABLET NODE: P5250T1RankedCommonEdges]

/-!
# P5250T1RankedCommonEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5250T1RankedCommonEdges (X Y : ProtoTile)
    (hX : X.cells.Nonempty) (hY : Y.cells.Nonempty)
    (f : Nat → GaussianInt) (N : Nat) (s c : Int) (hs : s = 1 ∨ s = -1)
    (hV : BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y =
      {v | ∃ j ≤ N, v = f j})
    (hrank : ∀ j ≤ N, (f j).re + s * (f j).im + c = (j : Int)) :
    BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y ⊆
      {e | ∃ j < N, e = {f j, f (j + 1)}} := by
-- BODY
  classical
  intro e he
  have ep (z : GaussianInt) (hz : z ∈ e) : ∃ j ≤ N, z = f j := by
    have hb : z ∈ BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y :=
      ⟨by rw [BoundaryFootprintVertices, ite_eq_left hX]; exact ⟨e, he.1, hz⟩,
       by rw [BoundaryFootprintVertices, ite_eq_left hY]; exact ⟨e, he.2, hz⟩⟩
    rw [hV] at hb
    exact hb
  obtain ⟨z, hz⟩ := he.1
  rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · obtain ⟨i, hi, h0⟩ := ep z (by simp)
    obtain ⟨j, hj, h1⟩ := ep (z + 1) (by simp)
    have r0 := hrank i hi
    have r1 := hrank j hj
    rw [← h0] at r0
    rw [← h1] at r1
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
      add_zero] at r1
    have ij : j = i + 1 := by omega
    exact ⟨i, by omega, by rw [h1, h0, ij]⟩
  · obtain ⟨i, hi, h0⟩ := ep z (by simp)
    obtain ⟨j, hj, h1⟩ := ep (z + ⟨0, 1⟩) (by simp)
    have r0 := hrank i hi
    have r1 := hrank j hj
    rw [← h0] at r0
    rw [← h1] at r1
    rcases hs with rfl | rfl
    · simp only [Zsqrtd.re_add, Zsqrtd.im_add, add_zero, one_mul] at r0 r1
      have ij : j = i + 1 := by omega
      exact ⟨i, by omega, by rw [h1, h0, ij]⟩
    · simp only [Zsqrtd.re_add, Zsqrtd.im_add, add_zero, neg_one_mul] at r0 r1
      have ji : i = j + 1 := by omega
      exact ⟨j, by omega, by rw [h1, h0, ji, Finset.pair_comm]⟩

end ApollonianSuperharmonic

end
