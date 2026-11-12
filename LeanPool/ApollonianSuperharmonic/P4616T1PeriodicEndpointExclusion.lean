/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralPeriodicBlockCells
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell

-- [TABLET NODE: P4616T1PeriodicEndpointExclusion]

/-!
# P4616T1PeriodicEndpointExclusion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4616T1PeriodicEndpointExclusion
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (S : ProtoTile) (hS : S.cells.Nonempty) (hST : S.cells ⊆ T.cells)
    (m n : Int) (hmn : (m, n) ≠ (0, 0)) (x y : GaussianInt)
    (hroot : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells)
    (hy : y ∈ FootprintVertices (TileTranslation S
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v))) :
    x ≠ y := by
-- BODY
  let d := (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v
  have hSep : Disjoint T.cells (TileTranslation T d).cells := by
    have h := (BandOrderedGeneralPeriodicBlockCells q cfg C T cert).2
      0 0 m n hmn.symm
    have hz : GaussianTranslation (0 : GaussianInt) = id := funext add_zero
    simpa [d, TileTranslation, hz, Finset.image_id] using h
  have hne : (TileTranslation S d).cells.Nonempty := by
    exact hS.image _
  have incident (R : ProtoTile) (z : GaussianInt)
      (hne : R.cells.Nonempty) (hz : z ∈ FootprintVertices R) :
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ R.cells := by
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hz
    rcases hz with ⟨a, ha, h | h | h | h⟩
    · exact ⟨0, by simpa [LatticeVertexIncidentCell] using h ▸ ha⟩
    · refine ⟨1, ?_⟩
      rw [h]
      simpa [LatticeVertexIncidentCell] using ha
    · refine ⟨3, ?_⟩
      rw [h]
      simpa [LatticeVertexIncidentCell] using ha
    · refine ⟨2, ?_⟩
      change z - 1 - ⟨0, 1⟩ ∈ R.cells
      rw [h]
      convert ha using 1
      ext <;> simp
  intro hxy
  obtain ⟨j, hj⟩ := incident (TileTranslation S d) y hne hy
  have hjT : LatticeVertexIncidentCell y j ∈ (TileTranslation T d).cells := by
    exact Finset.image_subset_image hST hj
  exact Finset.disjoint_left.mp hSep (by simpa [hxy] using hroot j) hjT

end ApollonianSuperharmonic

end
