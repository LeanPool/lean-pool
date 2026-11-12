/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintEdges

-- [TABLET NODE: CellDisjointCommonEdgesBoundary]

/-!
# CellDisjointCommonEdgesBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem CellDisjointCommonEdgesBoundary (U V : ProtoTile)
    (hdisjoint : Disjoint U.cells V.cells) :
    FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := by
-- BODY
  classical
  let I : GaussianInt := ⟨0, 1⟩
  have horiz_unique (x y : GaussianInt)
      (h : ({x, x + 1} : Finset GaussianInt) = {y, y + 1}) : x = y := by
    have hx : x = y ∨ x = y + 1 := by
      have : x ∈ ({y, y + 1} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hy : y = x ∨ y = x + 1 := by
      have : y ∈ ({x, x + 1} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hx with hxy | hxy
    · exact hxy
    rcases hy with hyx | hyx
    · exact hyx.symm
    · exfalso
      have hre := congrArg Zsqrtd.re hxy
      have hre' := congrArg Zsqrtd.re hyx
      norm_num at hre hre'
      omega
  have vert_unique (x y : GaussianInt)
      (h : ({x, x + I} : Finset GaussianInt) = {y, y + I}) : x = y := by
    have hx : x = y ∨ x = y + I := by
      have : x ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hy : y = x ∨ y = x + I := by
      have : y ∈ ({x, x + I} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hx with hxy | hxy
    · exact hxy
    rcases hy with hyx | hyx
    · exact hyx.symm
    · exfalso
      have him := congrArg Zsqrtd.im hxy
      have him' := congrArg Zsqrtd.im hyx
      simp [I] at him him'
      omega
  have horiz_ne_vert (x y : GaussianInt) :
      ({x, x + 1} : Finset GaussianInt) ≠ {y, y + I} := by
    intro h
    have hx : x = y ∨ x = y + I := by
      have : x ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hx1 : x + 1 = y ∨ x + 1 = y + I := by
      have : x + 1 ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hx with hx | hx <;> rcases hx1 with hx1 | hx1
    all_goals
      have hre := congrArg Zsqrtd.re hx
      have him := congrArg Zsqrtd.im hx
      have hre1 := congrArg Zsqrtd.re hx1
      have him1 := congrArg Zsqrtd.im hx1
      simp [I] at hre him hre1 him1
      omega
  have footprint_normalize (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) :
      (∃ z, e = {z, z + 1} ∧ (z ∈ T.cells ∨ z - I ∈ T.cells)) ∨
      (∃ z, e = {z, z + I} ∧ (z ∈ T.cells ∨ z - 1 ∈ T.cells)) := by
    rcases he with ⟨x, hx, h | h | h | h⟩
    · exact Or.inl ⟨x, h, Or.inl hx⟩
    · exact Or.inr ⟨x, h, Or.inl hx⟩
    · refine Or.inr ⟨x + 1, h, Or.inr ?_⟩
      simpa [add_sub_cancel_right] using hx
    · refine Or.inl ⟨x + I, ?_, Or.inr ?_⟩
      · simpa [I, Zsqrtd.ext_iff, add_comm, add_left_comm, add_assoc] using h
      simpa [I, Zsqrtd.ext_iff] using hx
  have boundary_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T := by
    rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        congr 1 <;> simp [I, Zsqrtd.ext_iff]
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        congr 1 <;> simp
  ext e
  constructor
  · rintro ⟨heU, heV⟩
    have hd := Finset.disjoint_left.mp hdisjoint
    rcases footprint_normalize U e heU with ⟨z, hz, hzU⟩ | ⟨z, hz, hzU⟩ <;>
      rcases footprint_normalize V e heV with ⟨w, hw, hwV⟩ | ⟨w, hw, hwV⟩
    · have bzw : z = w := horiz_unique z w (hz.symm.trans hw)
      subst w
      constructor <;> refine ⟨z, Or.inl ⟨?_, ?_⟩⟩
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inl ⟨hzU, fun hbad => hd hbad hzV⟩
        · exact Or.inr ⟨fun hbad => hd hbad hzV, hzU⟩
        · exact (hd hzU hzV).elim
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inr ⟨fun hbad => hd hzU hbad, hzV⟩
        · exact Or.inl ⟨hzV, fun hbad => hd hzU hbad⟩
        · exact (hd hzU hzV).elim
    · exact (horiz_ne_vert z w (hz.symm.trans hw)).elim
    · exact (horiz_ne_vert w z (hw.symm.trans hz)).elim
    · have bzw : z = w := vert_unique z w (hz.symm.trans hw)
      subst w
      constructor <;> refine ⟨z, Or.inr ⟨?_, ?_⟩⟩
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inl ⟨hzU, fun hbad => hd hbad hzV⟩
        · exact Or.inr ⟨fun hbad => hd hbad hzV, hzU⟩
        · exact (hd hzU hzV).elim
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inr ⟨fun hbad => hd hzU hbad, hzV⟩
        · exact Or.inl ⟨hzV, fun hbad => hd hzU hbad⟩
        · exact (hd hzU hzV).elim
  · rintro ⟨heU, heV⟩
    exact ⟨boundary_footprint U e heU, boundary_footprint V e heV⟩

end ApollonianSuperharmonic

end
