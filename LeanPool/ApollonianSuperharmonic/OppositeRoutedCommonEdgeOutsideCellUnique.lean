/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell

-- [TABLET NODE: OppositeRoutedCommonEdgeOutsideCellUnique]

/-!
# OppositeRoutedCommonEdgeOutsideCellUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem OppositeRoutedCommonEdgeOutsideCellUnique
    (E F : ProtoTile) (x : GaussianInt) (j : Fin 4)
    (edge : Finset GaussianInt)
    (hdisjoint : Disjoint E.cells F.cells)
    (hx : x ∈ edge)
    (hedge : edge ∈ FootprintEdges E ∩ FootprintEdges F)
    (hE : LatticeVertexIncidentCell x j ∈ E.cells)
    (hF : LatticeVertexIncidentCell x (j + 2) ∈ F.cells) :
    ∀ r s : Fin 4,
      LatticeVertexIncidentCell x r ∉ E.cells →
      LatticeVertexIncidentCell x r ∉ F.cells →
      LatticeVertexIncidentCell x s ∉ E.cells →
      LatticeVertexIncidentCell x s ∉ F.cells →
      LatticeVertexIncidentCell x r = LatticeVertexIncidentCell x s := by
-- BODY
  let I : GaussianInt := ⟨0, 1⟩
  obtain ⟨a, _, ha⟩ :=
    P3102T2CommonEdgeSectorTransition E F x edge hdisjoint hx hedge
  have ha0 : LatticeVertexIncidentCell x a ∈ E.cells ∨
      LatticeVertexIncidentCell x a ∈ F.cells := by
    rcases ha with ha | ha
    · exact Or.inl ha.1
    · exact Or.inr ha.1
  have ha1 : LatticeVertexIncidentCell x (a + 1) ∈ E.cells ∨
      LatticeVertexIncidentCell x (a + 1) ∈ F.cells := by
    rcases ha with ha | ha
    · exact Or.inr ha.2
    · exact Or.inl ha.2
  have remaining_unique : ∀ a j r s : Fin 4,
      (r ≠ a ∧ r ≠ a + 1 ∧ r ≠ j ∧ r ≠ j + 2) →
      (s ≠ a ∧ s ≠ a + 1 ∧ s ≠ j ∧ s ≠ j + 2) → r = s := by
    decide +kernel
  intro r s hrE hrF hsE hsF
  have absent (t : Fin 4)
      (htE : LatticeVertexIncidentCell x t ∉ E.cells)
      (htF : LatticeVertexIncidentCell x t ∉ F.cells) :
      t ≠ a ∧ t ≠ a + 1 ∧ t ≠ j ∧ t ≠ j + 2 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro rfl
      exact ha0.elim htE htF
    · rintro rfl
      exact ha1.elim htE htF
    · rintro rfl
      exact htE hE
    · rintro rfl
      exact htF hF
  exact congrArg (LatticeVertexIncidentCell x)
    (remaining_unique a j r s (absent r hrE hrF) (absent s hsE hsF))

end ApollonianSuperharmonic

end
