/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation

-- [TABLET NODE: BandOriginalPairSeparation]

/-!
# BandOriginalPairSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOriginalPairSeparation (P : Fin 3 -> Bool -> ProtoTile)
    (O : ProtoTile) (u v : GaussianInt)
    (hOA : O.cells ⊆ (P 0 true).cells)
    (hOB : O.cells ⊆ (P 0 false).cells)
    (hpartition : ∀ x : LatticeCell, ∃! o : PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells) :
    (forall m n : Int,
      (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∩
          (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells =
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells) ∧
    forall a b : PeriodicSubtileIndex, a ≠ b ->
      ¬ ((a.label = .A ∧ b.label = .B ∨
            a.label = .B ∧ b.label = .A) ∧
          a.first = b.first ∧ a.second = b.second) ->
      Disjoint (SubtileOccurrenceInterpretation P u v a).cells
        (SubtileOccurrenceInterpretation P u v b).cells := by
-- BODY
  classical
  have translation_cells (T : ProtoTile) (w : GaussianInt) :
      (TileTranslation T w).cells = T.cells.image (GaussianTranslation w) :=
    (TileTranslationFormulas T w).1
  have modified_a (m n : Int) :
      (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩).cells =
        (TileCellComplement (P 0 true) O).cells.image
          (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v)) := by
    rfl
  have modified_b (m n : Int) :
      (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.B, m, n⟩).cells =
        (P 0 false).cells.image
          (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v)) := by
    rfl
  have original_cells (o : PeriodicSubtileIndex) :
      (SubtileOccurrenceInterpretation P u v o).cells =
        (match o.label with
          | .A => (P 0 true).cells
          | .B => (P 0 false).cells
          | .C => (P 1 true).cells
          | .D => (P 1 false).cells
          | .E => (P 2 true).cells
          | .F => (P 2 false).cells).image
          (GaussianTranslation ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v)) := by
    cases o with
    | mk label first second =>
      cases label <;> rfl
  constructor
  · intro m n
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rcases Finset.mem_inter.1 hx with ⟨ha, hb⟩
      change x ∈ (P 0 true).cells.image
          (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v)) at ha
      change x ∈ (P 0 false).cells.image
          (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v)) at hb
      rcases Finset.mem_image.1 ha with ⟨z, hz, rfl⟩
      by_cases ho : z ∈ O.cells
      · apply Finset.mem_image.2
        exact ⟨z, ho, rfl⟩
      · have hza : z ∈ (TileCellComplement (P 0 true) O).cells := by
          exact Finset.mem_sdiff.2 ⟨hz, ho⟩
        have hma : (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v) z) ∈
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩).cells := by
          rw [modified_a]
          exact Finset.mem_image.2 ⟨z, hza, rfl⟩
        have hmb : (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v) z) ∈
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.B, m, n⟩).cells := by
          rw [modified_b]
          exact hb
        have heq := (hpartition _).unique hma hmb
        exact False.elim (by
          have : (PeriodicSubtileIndex.mk .A m n) = (PeriodicSubtileIndex.mk .B m n) := heq
          cases this)
    · intro hx
      rw [translation_cells] at hx
      rcases Finset.mem_image.1 hx with ⟨z, hz, he⟩
      apply Finset.mem_inter.2
      constructor
      · change x ∈ (P 0 true).cells.image
            (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v))
        exact Finset.mem_image.2 ⟨z, hOA hz, he⟩
      · change x ∈ (P 0 false).cells.image
            (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v))
        exact Finset.mem_image.2 ⟨z, hOB hz, he⟩
  · intro a b hab hpair
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have choose := hpartition x
    have split_member (o : PeriodicSubtileIndex)
        (ho : x ∈ (SubtileOccurrenceInterpretation P u v o).cells) :
        x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells ∨
          (o.label = .A ∧
            x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v
              ⟨.B, o.first, o.second⟩).cells) := by
      cases o with
      | mk label first second =>
        cases label with
        | A =>
          change x ∈ (P 0 true).cells.image
              (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at ho
          rcases Finset.mem_image.1 ho with ⟨z, hz, he⟩
          by_cases hzO : z ∈ O.cells
          · right
            constructor
            · rfl
            · rw [modified_b]
              apply Finset.mem_image.2
              exact ⟨z, hOB hzO, he⟩
          · left
            rw [modified_a]
            apply Finset.mem_image.2
            exact ⟨z, Finset.mem_sdiff.2 ⟨hz, hzO⟩, he⟩
        | B | C | D | E | F =>
          left
          simpa [SubtileOccurrenceInterpretation, ModifiedSubtileOccurrenceInterpretation,
            TileTranslation] using ho
    rcases split_member a hxa with hma | ⟨ha, hca⟩
    · rcases split_member b hxb with hmb | ⟨hb, hcb⟩
      · exact hab (choose.unique hma hmb)
      · have heq := choose.unique hma hcb
        have hl := congrArg PeriodicSubtileIndex.label heq
        have hf := congrArg PeriodicSubtileIndex.first heq
        have hs := congrArg PeriodicSubtileIndex.second heq
        cases a with
        | mk la af as =>
          cases b with
          | mk lb bf bs =>
            cases la <;> cases lb <;> simp_all
    · rcases split_member b hxb with hmb | ⟨hb, hcb⟩
      · have heq := choose.unique hca hmb
        have hl := congrArg PeriodicSubtileIndex.label heq
        have hf := congrArg PeriodicSubtileIndex.first heq
        have hs := congrArg PeriodicSubtileIndex.second heq
        cases a with
        | mk la af as =>
          cases b with
          | mk lb bf bs =>
            cases la <;> cases lb <;> simp_all
      · have heq := choose.unique hca hcb
        have hf := congrArg PeriodicSubtileIndex.first heq
        have hs := congrArg PeriodicSubtileIndex.second heq
        exact hab (by
          cases a with
          | mk la af as =>
            cases b with
            | mk lb bf bs =>
              simp_all)

end ApollonianSuperharmonic

end
