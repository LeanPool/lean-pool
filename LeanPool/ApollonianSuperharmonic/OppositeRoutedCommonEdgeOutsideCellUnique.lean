/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary

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
  have horiz_unique (u v : GaussianInt)
      (h : ({u, u + 1} : Finset GaussianInt) = {v, v + 1}) : u = v := by
    have hu : u = v ∨ u = v + 1 := by
      have : u ∈ ({v, v + 1} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hv : v = u ∨ v = u + 1 := by
      have : v ∈ ({u, u + 1} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hu with huv | huv
    · exact huv
    rcases hv with hvu | hvu
    · exact hvu.symm
    · have hre := congrArg Zsqrtd.re huv
      have hre' := congrArg Zsqrtd.re hvu
      norm_num at hre hre'
      omega
  have vert_unique (u v : GaussianInt)
      (h : ({u, u + I} : Finset GaussianInt) = {v, v + I}) : u = v := by
    have hu : u = v ∨ u = v + I := by
      have : u ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hv : v = u ∨ v = u + I := by
      have : v ∈ ({u, u + I} : Finset GaussianInt) := by rw [h]; simp
      simpa using this
    rcases hu with huv | huv
    · exact huv
    rcases hv with hvu | hvu
    · exact hvu.symm
    · have him := congrArg Zsqrtd.im huv
      have him' := congrArg Zsqrtd.im hvu
      simp [I] at him him'
      omega
  have horiz_ne_vert (u v : GaussianInt) :
      ({u, u + 1} : Finset GaussianInt) ≠ {v, v + I} := by
    intro h
    have hu : u = v ∨ u = v + I := by
      have : u ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hu1 : u + 1 = v ∨ u + 1 = v + I := by
      have : u + 1 ∈ ({v, v + I} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hu with hu | hu <;> rcases hu1 with hu1 | hu1
    all_goals
      have hre := congrArg Zsqrtd.re hu
      have him := congrArg Zsqrtd.im hu
      have hre1 := congrArg Zsqrtd.re hu1
      have him1 := congrArg Zsqrtd.im hu1
      simp [I] at hre him hre1 him1
      omega
  -- A common boundary edge separates a consecutive pair of occupied cells.
  have common_edge_transition (U V : ProtoTile) (y : GaussianInt)
      (e : Finset GaussianInt) (hdUV : Disjoint U.cells V.cells)
      (hye : y ∈ e)
      (he : e ∈ BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) :
      ∃ a : Fin 4,
        ((LatticeVertexIncidentCell y a ∈ U.cells ∧
            LatticeVertexIncidentCell y (a + 1) ∈ V.cells) ∨
          (LatticeVertexIncidentCell y a ∈ V.cells ∧
            LatticeVertexIncidentCell y (a + 1) ∈ U.cells)) := by
    have hd := Finset.disjoint_left.mp hdUV
    rcases he.1 with ⟨u, ⟨heu, hu⟩ | ⟨heu, hu⟩⟩
    · rcases he.2 with ⟨v, ⟨hev, hv⟩ | ⟨hev, hv⟩⟩
      · have huv : u = v := horiz_unique u v (heu.symm.trans hev)
        subst v
        have hyuv : y = u ∨ y = u + 1 := by
          rw [heu] at hye
          simpa using hye
        rcases hyuv with rfl | rfl
        · rcases hu with hu | hu <;> rcases hv with hv | hv
          · exact (hd hu.1 hv.1).elim
          · refine ⟨3, Or.inr ⟨?_, ?_⟩⟩
            · simpa [LatticeVertexIncidentCell, I] using hv.2
            · simpa [LatticeVertexIncidentCell, I] using hu.1
          · refine ⟨3, Or.inl ⟨?_, ?_⟩⟩
            · simpa [LatticeVertexIncidentCell, I] using hu.2
            · simpa [LatticeVertexIncidentCell, I] using hv.1
          · exact (hd hu.2 hv.2).elim
        · rcases hu with hu | hu <;> rcases hv with hv | hv
          · exact (hd hu.1 hv.1).elim
          · refine ⟨1, Or.inl ⟨?_, ?_⟩⟩
            · simpa [LatticeVertexIncidentCell, I] using hu.1
            · simpa [LatticeVertexIncidentCell, I] using hv.2
          · refine ⟨1, Or.inr ⟨?_, ?_⟩⟩
            · simpa [LatticeVertexIncidentCell, I] using hv.1
            · simpa [LatticeVertexIncidentCell, I] using hu.2
          · exact (hd hu.2 hv.2).elim
      · exact (horiz_ne_vert u v (heu.symm.trans hev)).elim
    · rcases he.2 with ⟨v, ⟨hev, hv⟩ | ⟨hev, hv⟩⟩
      · exact (horiz_ne_vert v u (hev.symm.trans heu)).elim
      · have huv : u = v := vert_unique u v (heu.symm.trans hev)
        subst v
        have hyuv : y = u ∨ y = u + I := by
          rw [heu] at hye
          simpa using hye
        rcases hyuv with rfl | rfl
        · rcases hu with hu | hu <;> rcases hv with hv | hv
          · exact (hd hu.1 hv.1).elim
          · refine ⟨0, Or.inl ⟨?_, ?_⟩⟩
            · simpa [LatticeVertexIncidentCell, I] using hu.1
            · simpa [LatticeVertexIncidentCell, I] using hv.2
          · refine ⟨0, Or.inr ⟨?_, ?_⟩⟩
            · simpa [LatticeVertexIncidentCell, I] using hv.1
            · simpa [LatticeVertexIncidentCell, I] using hu.2
          · exact (hd hu.2 hv.2).elim
        · have hcell2 : LatticeVertexIncidentCell (u + I) 2 = u - 1 := by
            ext <;> simp [LatticeVertexIncidentCell, I]
          have hcell3 : LatticeVertexIncidentCell (u + I) 3 = u := by
            simp [LatticeVertexIncidentCell, I]
          rcases hu with hu | hu <;> rcases hv with hv | hv
          · exact (hd hu.1 hv.1).elim
          · refine ⟨2, Or.inr ⟨?_, ?_⟩⟩
            · simpa only [hcell2] using hv.2
            · simpa only [show (2 : Fin 4) + 1 = 3 from rfl, hcell3] using hu.1
          · refine ⟨2, Or.inl ⟨?_, ?_⟩⟩
            · simpa only [hcell2] using hu.2
            · simpa only [show (2 : Fin 4) + 1 = 3 from rfl, hcell3] using hv.1
          · exact (hd hu.2 hv.2).elim
  have hboundary : edge ∈ BoundaryFootprintEdges E ∩ BoundaryFootprintEdges F := by
    rw [← CellDisjointCommonEdgesBoundary E F hdisjoint]
    exact hedge
  obtain ⟨a, ha⟩ := common_edge_transition E F x edge hdisjoint hx hboundary
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
