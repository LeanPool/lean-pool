/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms

-- [TABLET NODE: P5478T1ExteriorPlacementIndex]

/-!
# P5478T1ExteriorPlacementIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5478T1ExteriorPlacementIndex
    (C D : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x)
    (placement : BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign bundle.routedDirection) :
    let label : SixSubtileLabel := match bundle.selectedSlot.val with
      | 0 => if bundle.selectedSign then .A else .B
      | 1 => if bundle.selectedSign then .C else .D
      | _ => if bundle.selectedSign then .E else .F
    let coord : Int × Int := match placement.rightDirectionSlot.val with
      | 0 => (1, 0)
      | 1 => (0, 1)
      | _ => (-1, -1)
    let sign : Int := if placement.rightNeighborPositive then 1 else -1
    placement.exteriorIndex = ⟨label, sign * coord.1, sign * coord.2⟩ := by
-- BODY
  classical
  let canonical : PeriodicSubtileIndex :=
    let label : SixSubtileLabel := match bundle.selectedSlot.val with
      | 0 => if bundle.selectedSign then .A else .B
      | 1 => if bundle.selectedSign then .C else .D
      | _ => if bundle.selectedSign then .E else .F
    let coord : Int × Int := match placement.rightDirectionSlot.val with
      | 0 => (1, 0) | 1 => (0, 1) | _ => (-1, -1)
    let sign : Int := if placement.rightNeighborPositive then 1 else -1
    ⟨label, sign * coord.1, sign * coord.2⟩
  change placement.exteriorIndex = canonical
  let occurrence := SubtileOccurrenceInterpretation placement.layout.P
    placement.layout.u placement.layout.v
  have hu : BandVectors.1 (bundle.normalizedPresentation 0)
      (bundle.normalizedPresentation 1) = placement.layout.u :=
    placement.layout.period_u.symm
  have hv : BandVectors.1 (bundle.normalizedPresentation 0)
      (bundle.normalizedPresentation 2) = placement.layout.v :=
    placement.layout.period_v.symm
  have hw : BandVectors.1 (bundle.normalizedPresentation 0)
      (bundle.normalizedPresentation 3) = -placement.layout.u - placement.layout.v := by
    obtain ⟨_, _, _, _, h1, h2, h3, _⟩ :=
      P3055T1ParentVectorNormalForms bundle.normalizedPresentation bundle.configuration
    rw [← hu, ← hv, h1, h2, h3]
    ring
  have same_cells : (bundle.pieces bundle.selectedSlot bundle.selectedSign).cells =
      (occurrence canonical).cells := by
    rcases placement.selected_boundary_piece with ⟨hi, hs⟩ | ⟨hi, hs⟩
    · have he := congrArg ProtoTile.cells (congrArg₂ bundle.pieces hi hs)
      refine he.trans (placement.first_boundary_cells.trans ?_)
      rcases placement.right_slots_cyclic with ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩
      all_goals rcases placement.boundary_signs with ⟨hp, hf, ht'⟩ | ⟨hp, hf, ht'⟩
      all_goals simp [canonical, occurrence, hi, hs, hr, hd, hp, hf,
        SubtileOccurrenceInterpretation, placement.right_neighbor_displacement, hu, hv, hw,
        sub_eq_add_neg, add_comm]
    · have he := congrArg ProtoTile.cells (congrArg₂ bundle.pieces hi hs)
      refine he.trans (placement.second_boundary_cells.trans ?_)
      rcases placement.right_slots_cyclic with ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩
      all_goals rcases placement.boundary_signs with ⟨hp, hf, ht'⟩ | ⟨hp, hf, ht'⟩
      all_goals simp [canonical, occurrence, hi, hs, ht, hd, hp, ht',
        SubtileOccurrenceInterpretation, placement.right_neighbor_displacement, hu, hv, hw,
        sub_eq_add_neg, add_comm]
  have canonical_exterior :
      canonical = ⟨.A, -1, -1⟩ ∨ canonical = ⟨.A, 0, -1⟩ ∨
      canonical = ⟨.C, 1, 0⟩ ∨ canonical = ⟨.C, 1, 1⟩ ∨
      canonical = ⟨.E, 0, 1⟩ ∨ canonical = ⟨.E, -1, 0⟩ ∨
      canonical = ⟨.B, 1, 1⟩ ∨ canonical = ⟨.B, 0, 1⟩ ∨
      canonical = ⟨.D, -1, 0⟩ ∨ canonical = ⟨.D, -1, -1⟩ ∨
      canonical = ⟨.F, 0, -1⟩ ∨ canonical = ⟨.F, 1, 0⟩ := by
    rcases placement.selected_boundary_piece with ⟨hi, hs⟩ | ⟨hi, hs⟩
    all_goals rcases placement.right_slots_cyclic with ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩
    all_goals rcases placement.boundary_signs with ⟨hp, hf, ht'⟩ | ⟨hp, hf, ht'⟩
    all_goals simp [canonical, hi, hs, hr, ht, hd, hp, hf, ht']
  have hOA : placement.layout.O.cells ⊆ (placement.layout.P 0 true).cells := by
    rw [placement.layout.precursor_eq]
    intro z hz
    exact (placement.layout.plus_union z).2 ⟨0, false, hz⟩
  have hOB : placement.layout.O.cells ⊆ (placement.layout.P 0 false).cells := by
    rw [placement.layout.precursor_cells]
    intro z hz
    exact (placement.layout.minus_union z).2 ⟨0, true, hz⟩
  have separation := (BandOriginalPairSeparation placement.layout.P placement.layout.O
    placement.layout.u placement.layout.v hOA hOB placement.layout.partition).2
  by_contra hne
  have nonpaired : ¬ ((placement.exteriorIndex.label = .A ∧ canonical.label = .B ∨
      placement.exteriorIndex.label = .B ∧ canonical.label = .A) ∧
      placement.exteriorIndex.first = canonical.first ∧
      placement.exteriorIndex.second = canonical.second) := by
    rcases placement.exterior_index with he | he | he | he | he | he | he | he | he | he | he | he
    all_goals rcases canonical_exterior with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
        | hc
    all_goals simp [he, hc]
  have disj := separation placement.exteriorIndex canonical hne nonpaired
  have hc := bundle.selected_piece_cell
  have he : LatticeVertexIncidentCell bundle.normalizedPoint bundle.routedDirection ∈
      (occurrence placement.exteriorIndex).cells := by
    rw [← placement.selected_exterior_cells]
    exact hc
  have hk : LatticeVertexIncidentCell bundle.normalizedPoint bundle.routedDirection ∈
      (occurrence canonical).cells := by
    rw [← same_cells]
    exact hc
  exact Finset.disjoint_left.mp disj he hk

end ApollonianSuperharmonic

end
