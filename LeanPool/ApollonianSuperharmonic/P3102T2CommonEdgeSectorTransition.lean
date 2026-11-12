/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell

-- [TABLET NODE: P3102T2CommonEdgeSectorTransition]

/-!
# P3102T2CommonEdgeSectorTransition

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3102T2CommonEdgeSectorTransition
    (U V : ProtoTile) (x : GaussianInt) (e : Finset GaussianInt)
    (hdisjoint : Disjoint U.cells V.cells) (hxe : x ∈ e)
    (he : e ∈ FootprintEdges U ∩ FootprintEdges V) :
    ∃ j : Fin 4,
      e = ![{x, x + ⟨0, 1⟩}, {x - 1, x},
        {x - ⟨0, 1⟩, x}, {x, x + 1}] j ∧
      ((LatticeVertexIncidentCell x j ∈ U.cells ∧
          LatticeVertexIncidentCell x (j + 1) ∈ V.cells) ∨
        (LatticeVertexIncidentCell x j ∈ V.cells ∧
          LatticeVertexIncidentCell x (j + 1) ∈ U.cells)) := by
-- BODY
  classical
  let I : GaussianInt := ⟨0, 1⟩
  let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
    ![{x, x + I}, {x - 1, x}, {x - I, x}, {x, x + 1}]
  have horiz_unique (u v : GaussianInt)
      (h : ({u, u + 1} : Finset GaussianInt) = {v, v + 1}) : u = v := by
    have hu : u = v ∨ u = v + 1 := by
      have : u ∈ ({v, v + 1} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hv : v = u ∨ v = u + 1 := by
      have : v ∈ ({u, u + 1} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hu with huv | huv
    · exact huv
    rcases hv with hvu | hvu
    · exact hvu.symm
    · have hre := congrArg Zsqrtd.re huv
      have hre' := congrArg Zsqrtd.re hvu
      norm_num at hre hre'
      omega
  have vert_unique (u v : GaussianInt)
      (h : ({u, u + I} : Finset GaussianInt) = {v, v + I}) : u = v := by
    have hu : u = v ∨ u = v + I := by
      have : u ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hv : v = u ∨ v = u + I := by
      have : v ∈ ({u, u + I} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hu with huv | huv
    · exact huv
    rcases hv with hvu | hvu
    · exact hvu.symm
    · have him := congrArg Zsqrtd.im huv
      have him' := congrArg Zsqrtd.im hvu
      simp [I] at him him'
      omega
  have horiz_ne_vert (u v : GaussianInt) :
      ({u, u + 1} : Finset GaussianInt) ≠ {v, v + I} := by
    intro h
    have hu : u = v ∨ u = v + I := by
      have : u ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hu1 : u + 1 = v ∨ u + 1 = v + I := by
      have : u + 1 ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hu with hu | hu <;> rcases hu1 with hu1 | hu1
    all_goals
      have hre := congrArg Zsqrtd.re hu
      have him := congrArg Zsqrtd.im hu
      have hre1 := congrArg Zsqrtd.re hu1
      have him1 := congrArg Zsqrtd.im hu1
      simp [I] at hre him hre1 him1
      omega
  have hd := Finset.disjoint_left.mp hdisjoint
  rw [CellDisjointCommonEdgesBoundary U V hdisjoint] at he
  rcases he.1 with ⟨u, ⟨heu, hu⟩ | ⟨heu, hu⟩⟩
  · rcases he.2 with ⟨v, ⟨hev, hv⟩ | ⟨hev, hv⟩⟩
    · have huv : u = v := horiz_unique u v (heu.symm.trans hev)
      subst v
      have hxuv : x = u ∨ x = u + 1 := by
        rw [heu] at hxe
        simpa using hxe
      rcases hxuv with rfl | rfl
      · rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact (hd hu.1 hv.1).elim
        · refine ⟨3, by simpa [edgeAt], Or.inr ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I] using hv.2
          · simpa [LatticeVertexIncidentCell, I] using hu.1
        · refine ⟨3, by simpa [edgeAt], Or.inl ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I] using hu.2
          · simpa [LatticeVertexIncidentCell, I] using hv.1
        · exact (hd hu.2 hv.2).elim
      · rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact (hd hu.1 hv.1).elim
        · refine ⟨1, by simpa [edgeAt, I, Zsqrtd.ext_iff], Or.inl ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I] using hu.1
          · simpa [LatticeVertexIncidentCell, I] using hv.2
        · refine ⟨1, by simpa [edgeAt, I, Zsqrtd.ext_iff], Or.inr ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I] using hv.1
          · simpa [LatticeVertexIncidentCell, I] using hu.2
        · exact (hd hu.2 hv.2).elim
    · exact (horiz_ne_vert u v (heu.symm.trans hev)).elim
  · rcases he.2 with ⟨v, ⟨hev, hv⟩ | ⟨hev, hv⟩⟩
    · exact (horiz_ne_vert v u (hev.symm.trans heu)).elim
    · have huv : u = v := vert_unique u v (heu.symm.trans hev)
      subst v
      have hxuv : x = u ∨ x = u + I := by
        rw [heu] at hxe
        simpa using hxe
      rcases hxuv with rfl | rfl
      · rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact (hd hu.1 hv.1).elim
        · refine ⟨0, by simpa [edgeAt], Or.inl ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I] using hu.1
          · simpa [LatticeVertexIncidentCell, I] using hv.2
        · refine ⟨0, by simpa [edgeAt], Or.inr ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I] using hv.1
          · simpa [LatticeVertexIncidentCell, I] using hu.2
        · exact (hd hu.2 hv.2).elim
      · rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact (hd hu.1 hv.1).elim
        · refine ⟨2, by simpa [edgeAt, I, Zsqrtd.ext_iff], Or.inr ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc] using hv.2
          · simpa [LatticeVertexIncidentCell, I] using hu.1
        · refine ⟨2, by simpa [edgeAt, I, Zsqrtd.ext_iff], Or.inl ⟨?_, ?_⟩⟩
          · simpa [LatticeVertexIncidentCell, I, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc] using hu.2
          · simpa [LatticeVertexIncidentCell, I] using hv.1
        · exact (hd hu.2 hv.2).elim

end ApollonianSuperharmonic

end
