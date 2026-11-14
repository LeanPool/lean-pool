/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: BandOrderedGeneralPeriodicBlockCells]

/-!
# BandOrderedGeneralPeriodicBlockCells

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralPeriodicBlockCells
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (layout : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    (∀ m n : Int, ∀ x : LatticeCell,
      (x ∈ (TileTranslation T
          ((m : GaussianInt) * layout.u + (n : GaussianInt) * layout.v)).cells ↔
        ∃ label : SixSubtileLabel,
          x ∈ (ModifiedSubtileOccurrenceInterpretation layout.P layout.O
            layout.u layout.v ⟨label, m, n⟩).cells)) ∧
    ∀ m n r s : Int, (m, n) ≠ (r, s) →
      Disjoint
        (TileTranslation T
          ((m : GaussianInt) * layout.u + (n : GaussianInt) * layout.v)).cells
        (TileTranslation T
          ((r : GaussianInt) * layout.u + (s : GaussianInt) * layout.v)).cells := by
-- BODY
  classical
  have precursor_in_second : layout.O.cells ⊆ (layout.P 0 false).cells := by
    intro x hx
    rw [layout.precursor_cells] at hx
    apply (layout.minus_union x).2
    exact ⟨0, true, hx⟩
  have base_union : ∀ x : LatticeCell, x ∈ T.cells ↔
      ∃ label : SixSubtileLabel,
        x ∈ (ModifiedSubtileOccurrenceInterpretation layout.P layout.O
          layout.u layout.v ⟨label, 0, 0⟩).cells := by
    intro x
    rw [layout.outer_union]
    constructor
    · rintro ⟨i, s, hs⟩
      fin_cases i <;> fin_cases s
      · by_cases ho : x ∈ layout.O.cells
        · exact ⟨.B, by simpa [ModifiedSubtileOccurrenceInterpretation,
            TileTranslation, GaussianTranslation] using precursor_in_second ho⟩
        · exact ⟨.A, by simpa [ModifiedSubtileOccurrenceInterpretation,
            TileTranslation, GaussianTranslation, TileCellComplement] using ⟨hs, ho⟩⟩
      · exact ⟨.B, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      · exact ⟨.C, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      · exact ⟨.D, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      · exact ⟨.E, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      · exact ⟨.F, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
    · rintro ⟨label, hs⟩
      cases label with
      | A =>
          have hs' : x ∈ (TileCellComplement (layout.P 0 true) layout.O).cells := by
            simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
              GaussianTranslation] using hs
          simp only [TileCellComplement, Fin.isValue, Finset.mem_sdiff] at hs'
          exact ⟨0, true, hs'.1⟩
      | B => exact ⟨0, false, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      | C => exact ⟨1, true, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      | D => exact ⟨1, false, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      | E => exact ⟨2, true, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
      | F => exact ⟨2, false, by simpa [ModifiedSubtileOccurrenceInterpretation,
          TileTranslation, GaussianTranslation] using hs⟩
  have zero_decode (label : SixSubtileLabel) (y : LatticeCell) :
      y ∈ (ModifiedSubtileOccurrenceInterpretation layout.P layout.O
        layout.u layout.v ⟨label, 0, 0⟩).cells ↔
        y ∈ (match label with
          | .A => TileCellComplement (layout.P 0 true) layout.O
          | .B => layout.P 0 false
          | .C => layout.P 1 true
          | .D => layout.P 1 false
          | .E => layout.P 2 true
          | .F => layout.P 2 false).cells := by
    cases label <;> simp [ModifiedSubtileOccurrenceInterpretation,
      TileTranslation, GaussianTranslation]
  have cell_iff : ∀ m n : Int, ∀ x : LatticeCell,
      (x ∈ (TileTranslation T
          ((m : GaussianInt) * layout.u + (n : GaussianInt) * layout.v)).cells ↔
        ∃ label : SixSubtileLabel,
          x ∈ (ModifiedSubtileOccurrenceInterpretation layout.P layout.O
            layout.u layout.v ⟨label, m, n⟩).cells) := by
    intro m n x
    let d : GaussianInt := (m : GaussianInt) * layout.u +
      (n : GaussianInt) * layout.v
    rw [(TileTranslationFormulas T d).1]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      obtain ⟨label, hlabel⟩ := (base_union y).mp hy
      refine ⟨label, ?_⟩
      change x ∈ (TileTranslation _ d).cells
      rw [(TileTranslationFormulas _ d).1]
      exact Finset.mem_image.mpr ⟨y, (zero_decode label y).mp hlabel, hxy⟩
    · rintro ⟨label, hx⟩
      change x ∈ (TileTranslation _ d).cells at hx
      rw [(TileTranslationFormulas _ d).1] at hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨y, (base_union y).mpr (by
        exact ⟨label, (zero_decode label y).mpr hy⟩), hxy⟩
  constructor
  · exact cell_iff
  · intro m n r s hmn
    rw [Finset.disjoint_left]
    intro x hmx hrx
    obtain ⟨lm, hml⟩ := (cell_iff m n x).mp hmx
    obtain ⟨lr, hrl⟩ := (cell_iff r s x).mp hrx
    have heq := (layout.partition x).unique hml hrl
    exact hmn (by
      cases heq
      rfl)

end ApollonianSuperharmonic

end
