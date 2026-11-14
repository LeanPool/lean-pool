/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: P3102T2IsolatedRoutedCellSurvival]

/-!
# P3102T2IsolatedRoutedCellSurvival

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3102T2IsolatedRoutedCellSurvival
    (P : Fin 3 → Bool → ProtoTile) (O : ProtoTile) (u v : GaussianInt)
    (hOA : O.cells ⊆ (P 0 true).cells)
    (hOB : O.cells ⊆ (P 0 false).cells)
    (hpartition : ∀ z : LatticeCell, ∃! o : PeriodicSubtileIndex,
      z ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells)
    (hisolated : ∀ m n : Int,
      ∀ x ∈ FootprintVertices
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)),
        ∀ d : GaussianInt, x ∈ FootprintVertices (⟨{d}, d⟩ : ProtoTile) →
          d ∈ (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨
            d ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells)
    (a b : PeriodicSubtileIndex) (hab : a ≠ b)
    (hpair : ¬ ((a.label = .A ∧ b.label = .B ∨
        a.label = .B ∧ b.label = .A) ∧
      a.first = b.first ∧ a.second = b.second))
    (x c d : GaussianInt)
    (hc : c ∈ (SubtileOccurrenceInterpretation P u v a).cells)
    (hd : d ∈ (SubtileOccurrenceInterpretation P u v b).cells)
    (hxc : x ∈ FootprintVertices (⟨{c}, c⟩ : ProtoTile))
    (hxd : x ∈ FootprintVertices (⟨{d}, d⟩ : ProtoTile)) :
    c ∈ (ModifiedSubtileOccurrenceInterpretation P O u v a).cells := by
-- BODY
  classical
  obtain ⟨_, hseparate⟩ := BandOriginalPairSeparation P O u v hOA hOB hpartition
  cases a with
  | mk label m n =>
    cases label with
    | B | C | D | E | F => exact hc
    | A =>
      change c ∈ (P 0 true).cells.image
        (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v)) at hc
      obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hc
      change c ∈ ((P 0 true).cells \ O.cells).image
        (GaussianTranslation ((m : GaussianInt) * u + (n : GaussianInt) * v))
      refine Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, ?_⟩, heq⟩
      intro hzO
      have hcO : c ∈
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells :=
        Finset.mem_image.mpr ⟨z, hzO, heq⟩
      have hxO : x ∈ FootprintVertices
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) := by
        simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
          Finset.mem_singleton, exists_eq_left, Set.mem_ofPred_eq] at hxc
        have hne : (TileTranslation O
            ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells.Nonempty := ⟨c, hcO⟩
        simp only [FootprintVertices, hne, ite_true,
          Set.mem_ofPred_eq]
        exact ⟨c, hcO, hxc⟩
      have hbA : b ≠ (⟨.A, m, n⟩ : PeriodicSubtileIndex) := Ne.symm hab
      have hbB : b ≠ (⟨.B, m, n⟩ : PeriodicSubtileIndex) := by
        intro h
        subst b
        exact hpair ⟨Or.inl ⟨rfl, rfl⟩, rfl, rfl⟩
      have hdisA := hseparate ⟨.A, m, n⟩ b hab hpair
      have hdisB : Disjoint
          (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells
          (SubtileOccurrenceInterpretation P u v b).cells := by
        apply hseparate _ _ (Ne.symm hbB)
        intro h
        rcases h with ⟨hlabels, hm, hn⟩
        have hlabel : b.label = .A := by simpa using hlabels
        apply hbA
        cases b with
        | mk lb mb nb => simp_all
      rcases hisolated m n x hxO d hxd with hdA | hdB
      · exact Finset.disjoint_left.mp hdisA hdA hd
      · exact Finset.disjoint_left.mp hdisB hdB hd

end ApollonianSuperharmonic

end
