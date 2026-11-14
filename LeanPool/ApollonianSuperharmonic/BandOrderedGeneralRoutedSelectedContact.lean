/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRowExists
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.P3102T2IsolatedRoutedCellSurvival
public import LeanPool.ApollonianSuperharmonic.P3102T2OppositeOwnersCommonEdge

-- [TABLET NODE: BandOrderedGeneralRoutedSelectedContact]

/-!
# BandOrderedGeneralRoutedSelectedContact

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralRoutedSelectedContact
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    ∀ (a b : PeriodicSubtileIndex) (x : GaussianInt) (j : Fin 4),
      (a = ⟨.A, -1, -1⟩ ∨ a = ⟨.A, 0, -1⟩ ∨
       a = ⟨.C, 1, 0⟩ ∨ a = ⟨.C, 1, 1⟩ ∨
       a = ⟨.E, 0, 1⟩ ∨ a = ⟨.E, -1, 0⟩ ∨
       a = ⟨.B, 1, 1⟩ ∨ a = ⟨.B, 0, 1⟩ ∨
       a = ⟨.D, -1, 0⟩ ∨ a = ⟨.D, -1, -1⟩ ∨
       a = ⟨.F, 0, -1⟩ ∨ a = ⟨.F, 1, 0⟩) →
      (b = ⟨.A, 0, 0⟩ ∨ b = ⟨.B, 0, 0⟩ ∨
       b = ⟨.C, 0, 0⟩ ∨ b = ⟨.D, 0, 0⟩ ∨
       b = ⟨.E, 0, 0⟩ ∨ b = ⟨.F, 0, 0⟩) →
      LatticeVertexIncidentCell x j ∈ (occurrence a).cells →
      LatticeVertexIncidentCell x (j + 2) ∈ (occurrence b).cells →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (occurrence a) ∨
          y ∈ FootprintVertices (occurrence b)) →
      ∃ e : Finset GaussianInt,
        x ∈ e ∧
        e ∈ FootprintEdges (occurrence a) ∩
          FootprintEdges (occurrence b) ∧
        Nonempty (BandOrderedGeneralSelectedContactRow
          q cfg C₀ T cert a b) := by
-- BODY
  classical
  intro occurrence a b x j ha hb hca hcb hcover
  have hacoords : ¬ (a.first = 0 ∧ a.second = 0) := by
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp
  have hbcoords : b.first = 0 ∧ b.second = 0 := by
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  have hab : a ≠ b := by
    intro he
    apply hacoords
    simpa only [he] using hbcoords
  have hpair : ¬ ((a.label = .A ∧ b.label = .B ∨
      a.label = .B ∧ b.label = .A) ∧
      a.first = b.first ∧ a.second = b.second) := by
    intro h
    exact hacoords ⟨h.2.1.trans hbcoords.1, h.2.2.trans hbcoords.2⟩
  have hpair' : ¬ ((b.label = .A ∧ a.label = .B ∨
      b.label = .B ∧ a.label = .A) ∧
      b.first = a.first ∧ b.second = a.second) := by
    intro h
    apply hpair
    exact ⟨h.1.elim (fun h => Or.inr ⟨h.2, h.1⟩)
      (fun h => Or.inl ⟨h.2, h.1⟩), h.2.1.symm, h.2.2.symm⟩
  have hOA : cert.O.cells ⊆ (cert.P 0 true).cells := by
    intro z hz
    apply (cert.plus_union z).mpr
    exact ⟨0, false, by simpa [← cert.precursor_eq] using hz⟩
  have hOB : cert.O.cells ⊆ (cert.P 0 false).cells := by
    intro z hz
    apply (cert.minus_union z).mpr
    exact ⟨0, true, by simpa [← cert.precursor_cells] using hz⟩
  have corner (k : Fin 4) : x ∈ FootprintVertices
      (⟨{LatticeVertexIncidentCell x k}, LatticeVertexIncidentCell x k⟩ : ProtoTile) := by
    simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
      Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left]
    fin_cases k <;> simp [LatticeVertexIncidentCell,
      Zsqrtd.ext_iff]
  have hma : LatticeVertexIncidentCell x j ∈
      (ModifiedSubtileOccurrenceInterpretation cert.P cert.O cert.u cert.v a).cells :=
    P3102T2IsolatedRoutedCellSurvival cert.P cert.O cert.u cert.v
      hOA hOB cert.partition cert.precursor_isolated a b hab hpair
      x _ _ hca hcb (corner j) (corner (j + 2))
  have hmb : LatticeVertexIncidentCell x (j + 2) ∈
      (ModifiedSubtileOccurrenceInterpretation cert.P cert.O cert.u cert.v b).cells :=
    P3102T2IsolatedRoutedCellSurvival cert.P cert.O cert.u cert.v
      hOA hOB cert.partition cert.precursor_isolated b a (Ne.symm hab) hpair'
      x _ _ hcb hca (corner (j + 2)) (corner j)
  have hmodified_edge : ∃ e : Finset GaussianInt, x ∈ e ∧
      e ∈ FootprintEdges (cert.modified.tile a) ∩
        FootprintEdges (cert.modified.tile b) := by
    have hpartition : ∀ c : LatticeCell, ∃! o : PeriodicSubtileIndex,
        c ∈ (cert.modified.tile o).cells := by
      intro c
      simpa only [cert.modified_tile] using cert.partition c
    exact P3102T2OppositeOwnersCommonEdge cert.modified hpartition a b hab x j
      (by simpa only [cert.modified_tile] using hma)
      (by simpa only [cert.modified_tile] using hmb)
  have modified_subset (o : PeriodicSubtileIndex) :
      (cert.modified.tile o).cells ⊆ (occurrence o).cells := by
    rw [cert.modified_tile]
    cases o with
    | mk label m n =>
      cases label with
      | B | C | D | E | F => exact Finset.Subset.refl _
      | A =>
        intro z hz
        obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨c, (Finset.mem_sdiff.mp hc).1, he⟩
  have restore (o : PeriodicSubtileIndex) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges (cert.modified.tile o)) :
      e ∈ FootprintEdges (occurrence o) := by
    obtain ⟨c, hc, hedge⟩ := he
    exact ⟨c, modified_subset o hc, hedge⟩
  obtain ⟨e, hxe, hea, heb⟩ := hmodified_edge
  have he : e ∈ FootprintEdges (occurrence a) ∩ FootprintEdges (occurrence b) :=
    ⟨restore a e hea, restore b e heb⟩
  exact ⟨e, hxe, he,
    BandOrderedGeneralSelectedContactRowExists q cfg C₀ T cert a b ha hb ⟨e, he⟩⟩

end ApollonianSuperharmonic

end
