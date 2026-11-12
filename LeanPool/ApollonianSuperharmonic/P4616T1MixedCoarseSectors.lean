/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure

-- [TABLET NODE: P4616T1MixedCoarseSectors]

/-!
# P4616T1MixedCoarseSectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4616T1MixedCoarseSectors
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T) :
    let U : Fin 6 → ProtoTile := ![cert.P 0 true, cert.P 0 true,
      cert.P 0 false, cert.P 0 false, cert.P 1 true, cert.P 1 false]
    let W : Fin 6 → ProtoTile := ![cert.P 1 false, cert.P 2 false,
      cert.P 1 true, cert.P 2 true, cert.P 2 false, cert.P 2 true]
    let K : Fin 6 → ProtoTile := ![cert.P 0 false, cert.P 1 true,
      cert.P 0 true, cert.P 1 false, cert.P 0 true, cert.P 0 false]
    ∀ k (z : GaussianInt), z ∈ FootprintVertices (U k) →
      z ∈ FootprintVertices (W k) → z ∈ FootprintVertices (K k) →
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ (K k).cells ∧
        LatticeVertexIncidentCell z j ∉ (U k).cells ∧
        LatticeVertexIncidentCell z j ∉ (W k).cells := by
-- BODY
  classical
  obtain ⟨_, _, _, _, _, _, hABO, separate⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  have incident (N : ProtoTile) (hne : N.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ FootprintVertices N) :
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ N.cells := by
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hz
    rcases hz with ⟨a, ha, h | h | h | h⟩
    · exact ⟨0, by simpa [LatticeVertexIncidentCell] using h ▸ ha⟩
    · refine ⟨1, ?_⟩; rw [h]; simpa [LatticeVertexIncidentCell] using ha
    · refine ⟨3, ?_⟩; rw [h]; simpa [LatticeVertexIncidentCell] using ha
    · refine ⟨2, ?_⟩
      change z - 1 - ⟨0, 1⟩ ∈ N.cells
      rw [h]
      convert ha using 1
      ext <;> simp
  have corner (N : ProtoTile) (z : GaussianInt) (j : Fin 4)
      (hj : LatticeVertexIncidentCell z j ∈ N.cells) : z ∈ FootprintVertices N := by
    have hne : N.cells.Nonempty := ⟨_, hj⟩
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
    refine ⟨LatticeVertexIncidentCell z j, hj, ?_⟩
    fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
  have outside (U W K : ProtoTile) (hne : K.cells.Nonempty)
      (hKU : Disjoint K.cells U.cells) (hKW : Disjoint K.cells W.cells)
      (z : GaussianInt) (hk : z ∈ FootprintVertices K) :
      ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ K.cells ∧
        LatticeVertexIncidentCell z j ∉ U.cells ∧
        LatticeVertexIncidentCell z j ∉ W.cells := by
    obtain ⟨j, hj⟩ := incident K hne z hk
    exact ⟨j, hj, fun h => Finset.disjoint_left.mp hKU hj h,
      fun h => Finset.disjoint_left.mp hKW hj h⟩
  have noO (V : ProtoTile) (hne : V.cells.Nonempty)
      (hVA : Disjoint V.cells (cert.P 0 true).cells)
      (hVB : Disjoint V.cells (cert.P 0 false).cells)
      (z : GaussianInt) (hz : z ∈ FootprintVertices V) :
      z ∉ FootprintVertices cert.O := by
    intro hzO
    obtain ⟨j, hj⟩ := incident V hne z hz
    have hs : z ∈ FootprintVertices
        (⟨{LatticeVertexIncidentCell z j}, LatticeVertexIncidentCell z j⟩ : ProtoTile) :=
      corner _ z j (by simp)
    have hzero : GaussianTranslation (0 : GaussianInt) = id := funext add_zero
    have hi := cert.precursor_isolated 0 0 z
      (by simpa [TileTranslation, hzero, Finset.image_id] using hzO)
      (LatticeVertexIncidentCell z j) hs
    have hi' : LatticeVertexIncidentCell z j ∈ (cert.P 0 true).cells ∨
        LatticeVertexIncidentCell z j ∈ (cert.P 0 false).cells := by
      simpa [SubtileOccurrenceInterpretation, TileTranslation, hzero, Finset.image_id] using hi
    exact hi'.elim (fun h => Finset.disjoint_left.mp hVA hj h)
      (fun h => Finset.disjoint_left.mp hVB hj h)
  have ne (i : Fin 3) (s : Bool) : (cert.P i s).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1
  dsimp only
  intro k z hu hw hk
  fin_cases k
  · dsimp at hu hw hk ⊢
    obtain ⟨j, hj⟩ := incident _ (ne 0 false) z hk
    refine ⟨j, hj, ?_, fun h => Finset.disjoint_left.mp
      (separate 0 false 1 false (by decide) (by decide)) hj h⟩
    intro hjA
    have hjO : LatticeVertexIncidentCell z j ∈ cert.O.cells := by
      rw [← hABO]
      exact Finset.mem_inter.mpr ⟨hjA, hj⟩
    exact noO _ (ne 1 false)
      (separate 1 false 0 true (by decide) (by decide))
      (separate 1 false 0 false (by decide) (by decide)) z hw (corner _ z j hjO)
  · exact outside _ _ _ (ne 1 true)
      (separate 1 true 0 true (by decide) (by decide))
      (separate 1 true 2 false (by decide) (by decide)) z hk
  · dsimp at hu hw hk ⊢
    obtain ⟨j, hj⟩ := incident _ (ne 0 true) z hk
    refine ⟨j, hj, ?_, fun h => Finset.disjoint_left.mp
      (separate 0 true 1 true (by decide) (by decide)) hj h⟩
    intro hjB
    have hjO : LatticeVertexIncidentCell z j ∈ cert.O.cells := by
      rw [← hABO]
      exact Finset.mem_inter.mpr ⟨hj, hjB⟩
    exact noO _ (ne 1 true)
      (separate 1 true 0 true (by decide) (by decide))
      (separate 1 true 0 false (by decide) (by decide)) z hw (corner _ z j hjO)
  · exact outside _ _ _ (ne 1 false)
      (separate 1 false 0 false (by decide) (by decide))
      (separate 1 false 2 true (by decide) (by decide)) z hk
  · exact outside _ _ _ (ne 0 true)
      (separate 0 true 1 true (by decide) (by decide))
      (separate 0 true 2 false (by decide) (by decide)) z hk
  · exact outside _ _ _ (ne 0 false)
      (separate 0 false 1 false (by decide) (by decide))
      (separate 0 false 2 true (by decide) (by decide)) z hk

end ApollonianSuperharmonic

end
