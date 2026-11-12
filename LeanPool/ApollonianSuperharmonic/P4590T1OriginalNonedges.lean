/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralGeometricSectors
public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry

-- [TABLET NODE: P4590T1OriginalNonedges]

/-!
# P4590T1OriginalNonedges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1OriginalNonedges (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T) :
    FootprintVertices (cert.P 0 true) ∩ FootprintVertices (cert.P 2 true) = ∅ ∧
    FootprintVertices (cert.P 0 false) ∩ FootprintVertices (cert.P 2 false) = ∅ ∧
    FootprintVertices (cert.P 1 true) ∩ FootprintVertices (cert.P 1 false) = ∅ ∧
    FootprintVertices (cert.P 1 true) ∩ FootprintVertices (cert.P 2 true) = ∅ ∧
    FootprintVertices (cert.P 1 false) ∩ FootprintVertices (cert.P 2 false) = ∅ ∧
    FootprintVertices (cert.P 2 true) ∩ FootprintVertices (cert.P 2 false) = ∅ := by
-- BODY
  classical
  obtain ⟨whole, hw, hT, _, _⟩ := BandOrderedGeneralFinitePatches q cfg C T cert
  have hNP := (BandOrderedGeneralGeometricSectors q cfg C T cert whole hw hT).1
  have hn (a b : PeriodicSubtileIndex) (ha : a ∈ whole.indices)
      (hb : b ∈ whole.indices) (hab : a ≠ b)
      (hnab : ¬ AllowedSubtileIncidence a b) :
      FootprintVertices (cert.modified.tile a) ∩
        FootprintVertices (cert.modified.tile b) = ∅ := by
    rw [hNP a ha b hb hab]
    have hnot : ¬ (FootprintEdges (cert.modified.tile a) ∩
        FootprintEdges (cert.modified.tile b)).Nonempty := by
      intro he
      exact hnab ((cert.modified_adjacency a b).mp
        (((PeriodicTileIntersectionClassification cert.modified).1 a b hab).1.mp he))
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨e, he, _⟩
    exact hnot ⟨e, he⟩
  have htranslation_zero : GaussianTranslation 0 = id := by
    funext z
    exact add_zero z
  have hM (l : SixSubtileLabel) : cert.modified.tile ⟨l, 0, 0⟩ =
      match l with
      | .A => TileCellComplement (cert.P 0 true) cert.O
      | .B => cert.P 0 false
      | .C => cert.P 1 true
      | .D => cert.P 1 false
      | .E => cert.P 2 true
      | .F => cert.P 2 false := by
    rw [cert.modified_tile]
    cases l <;> simp [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
      htranslation_zero]
  have hnoledger (a b : SixSubtileLabel)
      (hpair : (a = .A ∧ b = .E) ∨ (a = .B ∧ b = .F) ∨
        (a = .C ∧ b = .D) ∨ (a = .C ∧ b = .E) ∨
        (a = .D ∧ b = .F) ∨ (a = .E ∧ b = .F)) :
      ¬ AllowedSubtileIncidence ⟨a, 0, 0⟩ ⟨b, 0, 0⟩ := by
    intro h
    have haux : ∀ {u v : PeriodicSubtileIndex}, AllowedSubtileIncidence u v →
        ¬ ((u.first = 0 ∧ u.second = 0 ∧ v.first = 0 ∧ v.second = 0) ∧
          ((u.label = .A ∧ v.label = .E) ∨ (u.label = .E ∧ v.label = .A) ∨
          (u.label = .B ∧ v.label = .F) ∨ (u.label = .F ∧ v.label = .B) ∨
          (u.label = .C ∧ v.label = .D) ∨ (u.label = .D ∧ v.label = .C) ∨
          (u.label = .C ∧ v.label = .E) ∨ (u.label = .E ∧ v.label = .C) ∨
          (u.label = .D ∧ v.label = .F) ∨ (u.label = .F ∧ v.label = .D) ∨
          (u.label = .E ∧ v.label = .F) ∨ (u.label = .F ∧ v.label = .E))) := by
      as_aux_lemma =>
      intro u v huv
      induction huv with
      | symm h ih =>
        rintro ⟨⟨h1, h2, h3, h4⟩, hp⟩
        apply ih
        refine ⟨⟨h3, h4, h1, h2⟩, ?_⟩
        simpa only [and_comm, or_comm, or_left_comm, or_assoc] using hp
      | _ =>
        simp
        all_goals omega
    apply haux h
    simp only
    refine ⟨by simp, ?_⟩
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hraw (a b : SixSubtileLabel) (hne : a ≠ b)
      (hpair : (a = .A ∧ b = .E) ∨ (a = .B ∧ b = .F) ∨
        (a = .C ∧ b = .D) ∨ (a = .C ∧ b = .E) ∨
        (a = .D ∧ b = .F) ∨ (a = .E ∧ b = .F)) :
      FootprintVertices (cert.modified.tile ⟨a, 0, 0⟩) ∩
        FootprintVertices (cert.modified.tile ⟨b, 0, 0⟩) = ∅ := by
    apply hn
    · rw [hw]; cases a <;> simp
    · rw [hw]; cases b <;> simp
    · intro he
      exact hne (congrArg PeriodicSubtileIndex.label he)
    · exact hnoledger a b hpair
  have hAE := hraw .A .E (by decide) (by simp)
  have hBF := hraw .B .F (by decide) (by simp)
  have hCD := hraw .C .D (by decide) (by simp)
  have hCE := hraw .C .E (by decide) (by simp)
  have hDF := hraw .D .F (by decide) (by simp)
  have hEF := hraw .E .F (by decide) (by simp)
  simp only [hM] at hAE hBF hCD hCE hDF hEF
  refine ⟨?_, hBF, hCD, hCE, hDF, hEF⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxA, hxE⟩
  have hAne : (cert.P 0 true).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice 0 true)).1.1
  have hEne : (cert.P 2 true).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice 2 true)).1.1
  obtain ⟨a, ha, hxa⟩ := (show ∃ a ∈ (cert.P 0 true).cells,
      x = a ∨ x = a + 1 ∨ x = a + ⟨0, 1⟩ ∨ x = a + 1 + ⟨0, 1⟩ from by
    simpa [FootprintVertices, hAne] using hxA)
  by_cases haO : a ∈ cert.O.cells
  · have hxO : x ∈ FootprintVertices cert.O := by
      simp only [FootprintVertices, show cert.O.cells.Nonempty from ⟨a, haO⟩, ite_true]
      exact ⟨a, haO, hxa⟩
    obtain ⟨b, hb, hxb⟩ := (show ∃ b ∈ (cert.P 2 true).cells,
        x = b ∨ x = b + 1 ∨ x = b + ⟨0, 1⟩ ∨ x = b + 1 + ⟨0, 1⟩ from by
      simpa [FootprintVertices, hEne] using hxE)
    have hxb' : x ∈ FootprintVertices (⟨{b}, b⟩ : ProtoTile) := by
      simpa [FootprintVertices] using hxb
    have hiso := cert.precursor_isolated 0 0 x (by
      simpa [TileTranslation, htranslation_zero] using hxO) b hxb'
    have hsep := (P4339T1PrecursorSupportGeometry C q cfg T cert).2.2.2.2.2.2.2
    simp only [SubtileOccurrenceInterpretation, TileTranslation, htranslation_zero,
      Int.cast_zero, zero_mul, zero_add, Finset.image_id] at hiso
    rcases hiso with hiso | hiso
    · exact Finset.disjoint_left.mp (hsep 0 true 2 true (by decide) (by decide)) hiso hb
    · exact Finset.disjoint_left.mp (hsep 0 false 2 true (by decide) (by decide)) hiso hb
  · have hxmod : x ∈ FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) := by
      have ha' : a ∈ (TileCellComplement (cert.P 0 true) cert.O).cells := by
        exact Finset.mem_sdiff.mpr ⟨ha, haO⟩
      simp only [FootprintVertices, show (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty
        from ⟨a, ha'⟩, ite_true]
      exact ⟨a, ha', hxa⟩
    have : x ∈ (∅ : Set GaussianInt) := hAE ▸ ⟨hxmod, hxE⟩
    exact this

end ApollonianSuperharmonic

end
