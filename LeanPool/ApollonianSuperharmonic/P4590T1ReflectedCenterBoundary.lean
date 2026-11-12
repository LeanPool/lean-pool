/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3776T1CellCenterMembership
public import LeanPool.ApollonianSuperharmonic.P4456T2VertexInterior
public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint

-- [TABLET NODE: P4590T1ReflectedCenterBoundary]

/-!
# P4590T1ReflectedCenterBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1ReflectedCenterBoundary (U V : ProtoTile) (x : GaussianInt)
    (hU : U.cells.Nonempty) (hV : V.cells.Nonempty)
    (hR : CentrallyReflectedAt (GaussianRealPoint x) U V) :
    x ∈ BoundaryFootprintVertices U ↔ x ∈ BoundaryFootprintVertices V := by
-- BODY
  classical
  let R : Real × Real → Real × Real := fun p =>
    (2 * (GaussianRealPoint x).1 - p.1, 2 * (GaussianRealPoint x).2 - p.2)
  have hR2 (p : Real × Real) : R (R p) = p := by
    ext <;> dsimp [R] <;> ring
  have hreal (p : Real × Real) : p ∈ TileRealization U ↔ R p ∈ TileRealization V := by
    change TileRealization V = R '' TileRealization U at hR
    rw [hR]
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      have heq : q = p := by
        have h := congrArg R hqp
        simpa only [hR2] using h
      exact heq ▸ hq
  have hcell (j : Fin 4) :
      LatticeVertexIncidentCell x j ∈ U.cells ↔
        LatticeVertexIncidentCell x (j + 2) ∈ V.cells := by
    rw [← P3776T1CellCenterMembership, ← P3776T1CellCenterMembership]
    simp only [GaussianRealPoint, Prod.mk_add_mk]
    rw [hreal]
    have heq : R
        (((LatticeVertexIncidentCell x j).re : Real) + 1 / 2,
          ((LatticeVertexIncidentCell x j).im : Real) + 1 / 2) =
        (((LatticeVertexIncidentCell x (j + 2)).re : Real) + 1 / 2,
          ((LatticeVertexIncidentCell x (j + 2)).im : Real) + 1 / 2) := by
      fin_cases j <;> ext <;> simp [R, GaussianRealPoint, LatticeVertexIncidentCell] <;> ring
    rw [heq]
  have htwo (j : Fin 4) : j + 2 + 2 = j := by fin_cases j <;> rfl
  have boundary_sectors (W : ProtoTile) (hne : W.cells.Nonempty)
      (hb : x ∈ BoundaryFootprintVertices W) :
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ W.cells) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ W.cells) := by
    have hraw : x ∈ FootprintVertices W := by
      simp only [BoundaryFootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hb
      obtain ⟨e, he, hx⟩ := hb
      simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
      obtain ⟨a, ⟨rfl, ha⟩ | ⟨rfl, ha⟩⟩ := he
      all_goals
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases ha with ⟨ha, _⟩ | ⟨_, ha⟩
        · refine ⟨a, ha, ?_⟩
          rcases hx with rfl | rfl <;> simp
        · refine ⟨_, ha, ?_⟩
          rcases hx with rfl | rfl <;>
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    refine ⟨?_, ?_⟩
    · simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hraw
      rcases hraw with ⟨a, ha, rfl | rfl | rfl | rfl⟩
      · exact ⟨0, by simpa [LatticeVertexIncidentCell] using ha⟩
      · exact ⟨1, by simpa [LatticeVertexIncidentCell] using ha⟩
      · exact ⟨3, by simpa [LatticeVertexIncidentCell] using ha⟩
      · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_sub] using ha⟩
    · by_contra! hall
      exact ((P4456T2VertexInterior W hne x hraw).2.mpr hall) hb
  constructor
  · intro hb
    obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := boundary_sectors U hU hb
    exact P3161T2IncidentBoundary V x ⟨j + 2, (hcell j).mp hj⟩
      ⟨k + 2, fun hv => hk ((hcell k).mpr hv)⟩
  · intro hb
    obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := boundary_sectors V hV hb
    refine P3161T2IncidentBoundary U x ⟨j + 2, (hcell (j + 2)).mpr ?_⟩
      ⟨k + 2, fun hu => hk ?_⟩
    · simpa only [htwo] using hj
    · simpa only [htwo] using (hcell (k + 2)).mp hu

end ApollonianSuperharmonic

end
