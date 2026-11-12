/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import Mathlib.Tactic.FinCases

-- [TABLET NODE: P3161T2IncidentBoundary]

/-!
# P3161T2IncidentBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3161T2IncidentBoundary (T : ProtoTile) (x : GaussianInt)
    (hsome : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells)
    (hmissing : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ T.cells) :
    x ∈ BoundaryFootprintVertices T := by
-- BODY
  classical
  have hne : T.cells.Nonempty := by
    obtain ⟨j, hj⟩ := hsome
    exact ⟨_, hj⟩
  let I : GaussianInt := ⟨0, 1⟩
  have edge01 (h : (x ∈ T.cells ∧ x - 1 ∉ T.cells) ∨
      (x ∉ T.cells ∧ x - 1 ∈ T.cells)) :
      x ∈ BoundaryFootprintVertices T := by
    simp only [BoundaryFootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
    refine ⟨{x, x + I}, ?_, by simp⟩
    exact ⟨x, Or.inr ⟨rfl, h⟩⟩
  have edge12 (h : (x - 1 ∈ T.cells ∧ x - 1 - I ∉ T.cells) ∨
      (x - 1 ∉ T.cells ∧ x - 1 - I ∈ T.cells)) :
      x ∈ BoundaryFootprintVertices T := by
    simp only [BoundaryFootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
    refine ⟨{x - 1, x - 1 + 1}, ?_, ?_⟩
    · exact ⟨x - 1, Or.inl ⟨rfl, h⟩⟩
    simp [Zsqrtd.ext_iff]
  have edge23 (h : (x - I ∈ T.cells ∧ x - I - 1 ∉ T.cells) ∨
      (x - I ∉ T.cells ∧ x - I - 1 ∈ T.cells)) :
      x ∈ BoundaryFootprintVertices T := by
    simp only [BoundaryFootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
    refine ⟨{x - I, x - I + I}, ?_, ?_⟩
    · exact ⟨x - I, Or.inr ⟨rfl, h⟩⟩
    simp [I, Zsqrtd.ext_iff]
  have hs : x ∈ T.cells ∨ x - 1 ∈ T.cells ∨ x - 1 - I ∈ T.cells ∨
      x - I ∈ T.cells := by
    rcases hsome with ⟨j, hj⟩
    fin_cases j
    · exact Or.inl (by simpa [LatticeVertexIncidentCell] using hj)
    · exact Or.inr (Or.inl (by simpa [LatticeVertexIncidentCell] using hj))
    · exact Or.inr (Or.inr (Or.inl (by
        simpa [LatticeVertexIncidentCell, I] using hj)))
    · exact Or.inr (Or.inr (Or.inr (by
        simpa [LatticeVertexIncidentCell] using hj)))
  have hm : x ∉ T.cells ∨ x - 1 ∉ T.cells ∨ x - 1 - I ∉ T.cells ∨
      x - I ∉ T.cells := by
    rcases hmissing with ⟨j, hj⟩
    fin_cases j
    · exact Or.inl (by simpa [LatticeVertexIncidentCell] using hj)
    · exact Or.inr (Or.inl (by simpa [LatticeVertexIncidentCell] using hj))
    · exact Or.inr (Or.inr (Or.inl (by
        simpa [LatticeVertexIncidentCell, I] using hj)))
    · exact Or.inr (Or.inr (Or.inr (by
        simpa [LatticeVertexIncidentCell] using hj)))
  by_cases h0 : x ∈ T.cells
  · by_cases h1 : x - 1 ∈ T.cells
    · by_cases h2 : x - 1 - I ∈ T.cells
      · by_cases h3 : x - I ∈ T.cells
        · exact (hm.elim (fun hn => hn h0)
            (fun h => h.elim (fun hn => hn h1)
              (fun h => h.elim (fun hn => hn h2) (fun hn => hn h3)))).elim
        · exact edge23 (Or.inr ⟨h3, by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2⟩)
      · exact edge12 (Or.inl ⟨h1, h2⟩)
    · exact edge01 (Or.inl ⟨h0, h1⟩)
  · by_cases h1 : x - 1 ∈ T.cells
    · exact edge01 (Or.inr ⟨h0, h1⟩)
    · by_cases h2 : x - 1 - I ∈ T.cells
      · exact edge12 (Or.inr ⟨h1, h2⟩)
      · by_cases h3 : x - I ∈ T.cells
        · exact edge23 (Or.inl ⟨h3, by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2⟩)
        · exact (hs.elim h0
            (fun h => h.elim h1 (fun h => h.elim h2 h3))).elim

end ApollonianSuperharmonic

end
