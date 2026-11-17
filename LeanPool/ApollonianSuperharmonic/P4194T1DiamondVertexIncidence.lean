/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary

-- [TABLET NODE: P4194T1DiamondVertexIncidence]

/-!
# P4194T1DiamondVertexIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4194T1DiamondVertexIncidence (n : Nat) (hn : 0 < n) (z : GaussianInt) :
    (z ∈ FootprintVertices (DiamondTile n) ↔
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain n) ∧
    (z ∈ BoundaryFootprintVertices (DiamondTile n) ↔
      (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain n) ∧
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∉ DiamondCellDomain n) := by
-- BODY
  classical
  have hne : (DiamondTile n).cells.Nonempty := by
    refine ⟨0, (P4194T1DiamondCellRows n 0).1.mpr ?_⟩
    norm_num
    omega
  have foot : z ∈ FootprintVertices (DiamondTile n) ↔
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain n := by
    rw [FootprintVertices, ite_eq_left hne]
    constructor
    · rintro ⟨w, hw, rfl | rfl | rfl | rfl⟩
      · exact ⟨0, hw⟩
      · exact ⟨1, by simpa [LatticeVertexIncidentCell, DiamondTile] using hw⟩
      · exact ⟨3, by simpa [LatticeVertexIncidentCell, DiamondTile] using hw⟩
      · exact ⟨2, by simpa [LatticeVertexIncidentCell, DiamondTile, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using hw⟩
    · rintro ⟨j, hj⟩
      refine ⟨LatticeVertexIncidentCell z j, hj, ?_⟩
      fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm]
  refine ⟨foot, ?_⟩
  constructor
  · intro hb
    have pair : (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ (DiamondTile n).cells) ∧
        ∃ j : Fin 4, LatticeVertexIncidentCell z j ∉ (DiamondTile n).cells := by
      simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hb
      obtain ⟨e, ⟨w, he⟩, hz⟩ := hb
      rcases he with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · rcases hw with ⟨hi, ho⟩ | ⟨ho, hi⟩
          · exact ⟨⟨0, hi⟩, ⟨3, ho⟩⟩
          · exact ⟨⟨3, hi⟩, ⟨0, ho⟩⟩
        · rcases hw with ⟨hi, ho⟩ | ⟨ho, hi⟩
          · exact ⟨⟨1, by simpa [LatticeVertexIncidentCell] using hi⟩,
              ⟨2, by simpa [LatticeVertexIncidentCell] using ho⟩⟩
          · exact ⟨⟨2, by simpa [LatticeVertexIncidentCell] using hi⟩,
              ⟨1, by simpa [LatticeVertexIncidentCell] using ho⟩⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · rcases hw with ⟨hi, ho⟩ | ⟨ho, hi⟩
          · exact ⟨⟨0, hi⟩, ⟨1, ho⟩⟩
          · exact ⟨⟨1, hi⟩, ⟨0, ho⟩⟩
        · rcases hw with ⟨hi, ho⟩ | ⟨ho, hi⟩
          · exact ⟨⟨3, by simpa [LatticeVertexIncidentCell] using hi⟩,
              ⟨2, by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
                add_assoc, add_comm, add_left_comm] using ho⟩⟩
          · exact ⟨⟨2, by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
                add_assoc, add_comm, add_left_comm] using hi⟩,
              ⟨3, by simpa [LatticeVertexIncidentCell] using ho⟩⟩
    exact pair
  · rintro ⟨hsome, hmissing⟩
    exact P3161T2IncidentBoundary (DiamondTile n) z hsome hmissing

end ApollonianSuperharmonic

end
