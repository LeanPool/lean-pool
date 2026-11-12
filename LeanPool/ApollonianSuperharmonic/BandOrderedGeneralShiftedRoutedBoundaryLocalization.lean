/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRowExists
public import LeanPool.ApollonianSuperharmonic.BandOriginalOccurrenceIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex
public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex
public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionPaths
public import LeanPool.ApollonianSuperharmonic.P3102T2IsolatedRoutedCellSurvival
public import LeanPool.ApollonianSuperharmonic.P3102T2OppositeOwnersCommonEdge
public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.TopologicalDisk

-- [TABLET NODE: BandOrderedGeneralShiftedRoutedBoundaryLocalization]

/-!
# BandOrderedGeneralShiftedRoutedBoundaryLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralShiftedRoutedBoundaryLocalization
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (a b : PeriodicSubtileIndex) (x : GaussianInt) (j : Fin 4)
    (k : Fin 3) (positive : Bool)
    (hshift :
      (positive = true /\
        ((k = 0 /\ a.first = 1 /\ a.second = 0) \/
         (k = 1 /\ a.first = 0 /\ a.second = 1) \/
         (k = 2 /\ a.first = -1 /\ a.second = -1))) \/
      (positive = false /\
        ((k = 0 /\ a.first = -1 /\ a.second = 0) \/
         (k = 1 /\ a.first = 0 /\ a.second = -1) \/
         (k = 2 /\ a.first = 1 /\ a.second = 1))))
    (hcentral :
      b = ⟨.A, 0, 0⟩ \/ b = ⟨.B, 0, 0⟩ \/
      b = ⟨.C, 0, 0⟩ \/ b = ⟨.D, 0, 0⟩ \/
      b = ⟨.E, 0, 0⟩ \/ b = ⟨.F, 0, 0⟩)
    (ha : LatticeVertexIncidentCell x j ∈
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells)
    (hb : LatticeVertexIncidentCell x (j + 2) ∈
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells)
    (hstar : forall y,
      y = x \/ y = x + 1 \/ y = x - 1 \/
        y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
      y ∈ FootprintVertices
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) \/
        y ∈ FootprintVertices
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)) :
    exists edge : Finset GaussianInt,
      x ∈ edge /\
      edge ∈
        FootprintEdges
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
          FootprintEdges
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) /\
      ((positive = true /\
          ((k = 0 /\
              (a = ⟨.C, 1, 0⟩ \/ a = ⟨.F, 1, 0⟩)) \/
           (k = 1 /\
              (a = ⟨.E, 0, 1⟩ \/ a = ⟨.B, 0, 1⟩)) \/
           (k = 2 /\
              (a = ⟨.A, -1, -1⟩ \/ a = ⟨.D, -1, -1⟩)))) \/
        (positive = false /\
          ((k = 0 /\
              (a = ⟨.D, -1, 0⟩ \/ a = ⟨.E, -1, 0⟩)) \/
           (k = 1 /\
              (a = ⟨.F, 0, -1⟩ \/ a = ⟨.A, 0, -1⟩)) \/
           (k = 2 /\
              (a = ⟨.B, 1, 1⟩ \/ a = ⟨.C, 1, 1⟩))))) /\
      Nonempty (BandOrderedGeneralSelectedContactRow q cfg C0 T cert a b) := by
-- BODY
  classical
  have hcoords :
      (a.first = 1 ∧ a.second = 0) ∨
      (a.first = 0 ∧ a.second = 1) ∨
      (a.first = -1 ∧ a.second = -1) ∨
      (a.first = -1 ∧ a.second = 0) ∨
      (a.first = 0 ∧ a.second = -1) ∨
      (a.first = 1 ∧ a.second = 1) := by
    rcases hshift with ⟨_, h⟩ | ⟨_, h⟩
    · rcases h with h | h | h
      · exact Or.inl ⟨h.2.1, h.2.2⟩
      · exact Or.inr (Or.inl ⟨h.2.1, h.2.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩))
    · rcases h with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2.1, h.2.2⟩))))
  have hbzero : b.first = 0 ∧ b.second = 0 := by
    rcases hcentral with h | h | h | h | h | h <;> simp_all
  have hab : a ≠ b := by
    intro he
    have hfirst := congrArg PeriodicSubtileIndex.first he
    have hsecond := congrArg PeriodicSubtileIndex.second he
    rcases hcoords with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  have hpair : ¬ ((a.label = .A ∧ b.label = .B ∨
      a.label = .B ∧ b.label = .A) ∧
      a.first = b.first ∧ a.second = b.second) := by
    intro h
    have hfirst := h.2.1
    have hsecond := h.2.2
    rcases hcoords with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
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
  have corner (r : Fin 4) : x ∈ FootprintVertices
      (⟨{LatticeVertexIncidentCell x r}, LatticeVertexIncidentCell x r⟩ : ProtoTile) := by
    simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
      Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left]
    fin_cases r <;> simp [LatticeVertexIncidentCell, Zsqrtd.ext_iff]
  have hma : LatticeVertexIncidentCell x j ∈
      (ModifiedSubtileOccurrenceInterpretation cert.P cert.O cert.u cert.v a).cells :=
    P3102T2IsolatedRoutedCellSurvival cert.P cert.O cert.u cert.v
      hOA hOB cert.partition cert.precursor_isolated a b hab hpair
      x _ _ ha hb (corner j) (corner (j + 2))
  have hmb : LatticeVertexIncidentCell x (j + 2) ∈
      (ModifiedSubtileOccurrenceInterpretation cert.P cert.O cert.u cert.v b).cells :=
    P3102T2IsolatedRoutedCellSurvival cert.P cert.O cert.u cert.v
      hOA hOB cert.partition cert.precursor_isolated b a (Ne.symm hab) hpair'
      x _ _ hb ha (corner (j + 2)) (corner j)
  have hpartition : ∀ c : LatticeCell, ∃! o : PeriodicSubtileIndex,
      c ∈ (cert.modified.tile o).cells := by
    intro c
    simpa only [cert.modified_tile] using cert.partition c
  have hmodified_edge := P3102T2OppositeOwnersCommonEdge cert.modified
    hpartition a b hab x j
    (by simpa only [cert.modified_tile] using hma)
    (by simpa only [cert.modified_tile] using hmb)
  have modified_subset (o : PeriodicSubtileIndex) :
      (cert.modified.tile o).cells ⊆
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v o).cells := by
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
      e ∈ FootprintEdges
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v o) := by
    obtain ⟨c, hc, hedge⟩ := he
    exact ⟨c, modified_subset o hc, hedge⟩
  obtain ⟨e, hxe, hea, heb⟩ := hmodified_edge
  have he : e ∈ FootprintEdges
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
      FootprintEdges (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) :=
    ⟨restore a e hea, restore b e heb⟩
  have hinc : AllowedSubtileIncidence a b :=
    (BandOriginalOccurrenceIntersectionClassification q cfg C0 T cert a b hab).1
      ⟨e, he⟩
  let shiftedBoundaryLabels (z : PeriodicSubtileIndex) : Prop :=
    ((z.first = 1 ∧ z.second = 0) → z.label = .C ∨ z.label = .F) ∧
    ((z.first = 0 ∧ z.second = 1) → z.label = .E ∨ z.label = .B) ∧
    ((z.first = -1 ∧ z.second = -1) → z.label = .A ∨ z.label = .D) ∧
    ((z.first = -1 ∧ z.second = 0) → z.label = .D ∨ z.label = .E) ∧
    ((z.first = 0 ∧ z.second = -1) → z.label = .F ∨ z.label = .A) ∧
    ((z.first = 1 ∧ z.second = 1) → z.label = .B ∨ z.label = .C)
  have ledger (u v : PeriodicSubtileIndex) (h : AllowedSubtileIncidence u v) :
      (v.first = 0 ∧ v.second = 0 → shiftedBoundaryLabels u) ∧
      (u.first = 0 ∧ u.second = 0 → shiftedBoundaryLabels v) := by
    induction h with
    | symm h ih => exact And.symm ih
    | AB m n | AB01 m n | AB11 m n | AC m n | AC11 m n
      | AD m n | AE01 m n | AF m n | BC m n | BDm1m1 m n
      | BD m n | BE m n | BF0m1 m n | CDm10 m n | CEm10 m n
      | CF m n | DE m n | DF10 m n =>
        constructor <;> rintro hm <;>
          simp [shiftedBoundaryLabels] at * <;> omega
  have hlabels := (ledger a b hinc).1 hbzero
  have index_eq (label : SixSubtileLabel) (m n : Int)
      (hl : a.label = label) (hm : a.first = m) (hn : a.second = n) :
      a = ⟨label, m, n⟩ := by
    cases a with
    | mk actual first second =>
      change actual = label at hl
      change first = m at hm
      change second = n at hn
      subst actual
      subst first
      subst second
      rfl
  have htable :
      ((positive = true /\
          ((k = 0 /\
              (a = ⟨.C, 1, 0⟩ \/ a = ⟨.F, 1, 0⟩)) \/
           (k = 1 /\
              (a = ⟨.E, 0, 1⟩ \/ a = ⟨.B, 0, 1⟩)) \/
           (k = 2 /\
              (a = ⟨.A, -1, -1⟩ \/ a = ⟨.D, -1, -1⟩)))) \/
        (positive = false /\
          ((k = 0 /\
              (a = ⟨.D, -1, 0⟩ \/ a = ⟨.E, -1, 0⟩)) \/
           (k = 1 /\
              (a = ⟨.F, 0, -1⟩ \/ a = ⟨.A, 0, -1⟩)) \/
           (k = 2 /\
              (a = ⟨.B, 1, 1⟩ \/ a = ⟨.C, 1, 1⟩))))) := by
    rcases hshift with ⟨hp, hs⟩ | ⟨hp, hs⟩
    · rcases hs with h0 | h1 | h2
      · rcases hlabels.1 ⟨h0.2.1, h0.2.2⟩ with hl | hl
        · exact Or.inl ⟨hp, Or.inl ⟨h0.1, Or.inl (index_eq .C 1 0 hl h0.2.1 h0.2.2)⟩⟩
        · exact Or.inl ⟨hp, Or.inl ⟨h0.1, Or.inr (index_eq .F 1 0 hl h0.2.1 h0.2.2)⟩⟩
      · rcases hlabels.2.1 ⟨h1.2.1, h1.2.2⟩ with hl | hl
        · exact Or.inl ⟨hp, Or.inr (Or.inl ⟨h1.1, Or.inl (index_eq .E 0 1 hl h1.2.1 h1.2.2)⟩)⟩
        · exact Or.inl ⟨hp, Or.inr (Or.inl ⟨h1.1, Or.inr (index_eq .B 0 1 hl h1.2.1 h1.2.2)⟩)⟩
      · rcases hlabels.2.2.1 ⟨h2.2.1, h2.2.2⟩ with hl | hl
        · exact Or.inl ⟨hp, Or.inr (Or.inr (⟨h2.1, Or.inl (index_eq .A (-1) (-1) hl h2.2.1
            h2.2.2)⟩))⟩
        · exact Or.inl ⟨hp, Or.inr (Or.inr (⟨h2.1, Or.inr (index_eq .D (-1) (-1) hl h2.2.1
            h2.2.2)⟩))⟩
    · rcases hs with h0 | h1 | h2
      · rcases hlabels.2.2.2.1 ⟨h0.2.1, h0.2.2⟩ with hl | hl
        · exact Or.inr ⟨hp, Or.inl ⟨h0.1, Or.inl (index_eq .D (-1) 0 hl h0.2.1 h0.2.2)⟩⟩
        · exact Or.inr ⟨hp, Or.inl ⟨h0.1, Or.inr (index_eq .E (-1) 0 hl h0.2.1 h0.2.2)⟩⟩
      · rcases hlabels.2.2.2.2.1 ⟨h1.2.1, h1.2.2⟩ with hl | hl
        · exact Or.inr ⟨hp, Or.inr (Or.inl ⟨h1.1, Or.inl (index_eq .F 0 (-1) hl h1.2.1 h1.2.2)⟩)⟩
        · exact Or.inr ⟨hp, Or.inr (Or.inl ⟨h1.1, Or.inr (index_eq .A 0 (-1) hl h1.2.1 h1.2.2)⟩)⟩
      · rcases hlabels.2.2.2.2.2 ⟨h2.2.1, h2.2.2⟩ with hl | hl
        · exact Or.inr ⟨hp, Or.inr (Or.inr ⟨h2.1, Or.inl (index_eq .B 1 1 hl h2.2.1 h2.2.2)⟩)⟩
        · exact Or.inr ⟨hp, Or.inr (Or.inr ⟨h2.1, Or.inr (index_eq .C 1 1 hl h2.2.1 h2.2.2)⟩)⟩
  have haExterior :
      (a = ⟨.A, -1, -1⟩ ∨ a = ⟨.A, 0, -1⟩ ∨
       a = ⟨.C, 1, 0⟩ ∨ a = ⟨.C, 1, 1⟩ ∨
       a = ⟨.E, 0, 1⟩ ∨ a = ⟨.E, -1, 0⟩ ∨
       a = ⟨.B, 1, 1⟩ ∨ a = ⟨.B, 0, 1⟩ ∨
       a = ⟨.D, -1, 0⟩ ∨ a = ⟨.D, -1, -1⟩ ∨
       a = ⟨.F, 0, -1⟩ ∨ a = ⟨.F, 1, 0⟩) := by
    rcases htable with ⟨_, h⟩ | ⟨_, h⟩
    · rcases h with ⟨_, z⟩ | ⟨_, z⟩ | ⟨_, z⟩
      · rcases z with h | h <;> simp [h]
      · rcases z with h | h <;> simp [h]
      · rcases z with h | h <;> simp [h]
    · rcases h with ⟨_, z⟩ | ⟨_, z⟩ | ⟨_, z⟩
      · rcases z with h | h <;> simp [h]
      · rcases z with h | h <;> simp [h]
      · rcases z with h | h <;> simp [h]
  exact ⟨e, hxe, he,
    htable,
    BandOrderedGeneralSelectedContactRowExists q cfg C0 T cert a b haExterior hcentral ⟨e, he⟩⟩

end ApollonianSuperharmonic

end
