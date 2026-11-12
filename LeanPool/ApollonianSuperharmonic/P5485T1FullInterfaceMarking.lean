/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure

-- [TABLET NODE: P5485T1FullInterfaceMarking]

/-!
# P5485T1FullInterfaceMarking

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5485T1FullInterfaceMarking
    (A B U : ProtoTile) (data : ExactTileInterfaceTriple A B U)
    (hA : LatticeTile A) (hB : LatticeTile B) (hU : LatticeTile U)
    (hAB : Disjoint A.cells B.cells)
    (hAU : Disjoint A.cells U.cells) (hBU : Disjoint B.cells U.cells)
    (htouch : TouchingTriple A B U) (x : GaussianInt)
    (hedge : ∃ e : Finset GaussianInt,
      x ∈ e ∧ e ∈ FootprintEdges A ∩ FootprintEdges B)
    (hother : x ≠ data.otherAB) :
    (¬ (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
        z = x - 1 - ⟨0, 1⟩ → z ∈ A.cells ∨ z ∈ B.cells) ↔
      x ∈ FootprintVertices U) := by
-- BODY
  have incident (U : ProtoTile) (hne : U.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ FootprintVertices U) :
      ∃ k : Fin 4, LatticeVertexIncidentCell z k ∈ U.cells := by
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hz
    rcases hz with ⟨c, hc, rfl | rfl | rfl | rfl⟩
    · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using hc⟩
  have coverage :
      (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
        z = x - 1 - ⟨0, 1⟩ → z ∈ A.cells ∨ z ∈ B.cells) ↔
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ A.cells ∨
        LatticeVertexIncidentCell x j ∈ B.cells := by
    constructor
    · intro h j
      apply h
      fin_cases j <;> simp [LatticeVertexIncidentCell]
    · intro h z hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [LatticeVertexIncidentCell] using h 0
      · simpa [LatticeVertexIncidentCell] using h 1
      · simpa [LatticeVertexIncidentCell] using h 3
      · simpa [LatticeVertexIncidentCell] using h 2
  rw [coverage]
  rcases SimpleGridPathPointTrichotomy _ _ data.point data.otherAB x
      data.pathAB hedge with hpoint | hwrong | hinterior
  · have hcommon := (data.unique_common x).2 hpoint
    obtain ⟨j, hj⟩ := (LocalLatticeInterfaceSectors.1 A B U x hA hB hU
      htouch hcommon).2.2.2.1
    constructor
    · intro _
      exact hcommon.2
    · intro _ hall
      rcases hall j with ha | hb
      · exact Finset.disjoint_left.mp hAU ha hj
      · exact Finset.disjoint_left.mp hBU hb hj
  · exact (hother hwrong).elim
  · have hall := (LocalLatticeInterfaceSectors.2 A B x hA hB hAB hinterior).1
    constructor
    · intro h
      exact (h hall).elim
    · intro hu _
      obtain ⟨j, hj⟩ := incident U (LatticeTileGridStructure U hU).1.1 x hu
      rcases hall j with ha | hb
      · exact Finset.disjoint_left.mp hAU ha hj
      · exact Finset.disjoint_left.mp hBU hb hj

end ApollonianSuperharmonic

end
