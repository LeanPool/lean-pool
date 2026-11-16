/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: P5290T1RawBoundaryInterfaces]

/-!
# P5290T1RawBoundaryInterfaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5290T1RawBoundaryInterfaces (T U : ProtoTile)
    (hT : T.cells.Nonempty) (hU : U.cells.Nonempty)
    (hd : Disjoint T.cells U.cells) :
    FootprintVertices T ∩ FootprintVertices U =
        BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U ∧
      FootprintEdges T ∩ FootprintEdges U =
        BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U := by
-- BODY
  have incident (A : ProtoTile) (hne : A.cells.Nonempty) (z : GaussianInt) :
      z ∈ FootprintVertices A ↔
        ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ A.cells := by
    rw [FootprintVertices, ite_eq_left hne]
    constructor
    · rintro ⟨c, hc, rfl | rfl | rfl | rfl⟩
      · exact ⟨0, hc⟩
      · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hc⟩
      · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hc⟩
      · exact ⟨2, by simpa [LatticeVertexIncidentCell, add_sub_assoc,
          add_comm, add_left_comm, add_assoc] using hc⟩
    · rintro ⟨j, hj⟩
      fin_cases j
      · exact ⟨z, hj, Or.inl rfl⟩
      · exact ⟨z - 1, hj, Or.inr (Or.inl (by simp))⟩
      · exact ⟨z - 1 - ⟨0, 1⟩, hj,
          Or.inr (Or.inr (Or.inr (by abel)))⟩
      · exact ⟨z - ⟨0, 1⟩, hj, Or.inr (Or.inr (Or.inl (by simp)))⟩
  have boundary_raw (A : ProtoTile) (hne : A.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ BoundaryFootprintVertices A) :
      z ∈ FootprintVertices A := by
    rw [BoundaryFootprintVertices, ite_eq_left hne] at hz
    obtain ⟨e, ⟨c, he⟩, hz⟩ := hz
    rw [FootprintVertices, ite_eq_left hne]
    rcases he with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · rcases hc with ⟨hc, _⟩ | ⟨_, hc⟩
      · have hz : z = c ∨ z = c + 1 := by simpa using hz
        exact ⟨c, hc, hz.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
      · have hz : z = c ∨ z = c + 1 := by simpa using hz
        refine ⟨c - ⟨0, 1⟩, hc, ?_⟩
        rcases hz with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl (by simp)))
        · exact Or.inr (Or.inr (Or.inr (by simp [sub_add_eq_add_sub])))
    · rcases hc with ⟨hc, _⟩ | ⟨_, hc⟩
      · have hz : z = c ∨ z = c + ⟨0, 1⟩ := by simpa using hz
        exact ⟨c, hc, hz.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))⟩
      · have hz : z = c ∨ z = c + ⟨0, 1⟩ := by simpa using hz
        refine ⟨c - 1, hc, ?_⟩
        rcases hz with rfl | rfl
        · exact Or.inr (Or.inl (by simp))
        · exact Or.inr (Or.inr (Or.inr (by simp)))
  refine ⟨?_, CellDisjointCommonEdgesBoundary T U hd⟩
  ext z
  constructor
  · rintro ⟨hzT, hzU⟩
    obtain ⟨i, hi⟩ := (incident T hT z).mp hzT
    obtain ⟨j, hj⟩ := (incident U hU z).mp hzU
    exact ⟨P3161T2IncidentBoundary T z ⟨i, hi⟩
      ⟨j, fun hh => Finset.disjoint_left.mp hd hh hj⟩,
      P3161T2IncidentBoundary U z ⟨j, hj⟩
        ⟨i, fun hh => Finset.disjoint_left.mp hd hi hh⟩⟩
  · rintro ⟨hzT, hzU⟩
    exact ⟨boundary_raw T hT z hzT, boundary_raw U hU z hzU⟩

end ApollonianSuperharmonic

end
