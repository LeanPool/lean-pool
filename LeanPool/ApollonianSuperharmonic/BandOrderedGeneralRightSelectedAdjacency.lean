/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BandGeneralCircle
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightPlacement
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.P3045T1RightBoundaryDisplacementAlgebra
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileSubodometer
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandOrderedGeneralRightSelectedAdjacency]

/-!
# BandOrderedGeneralRightSelectedAdjacency

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightSelectedGeometry

private theorem hpos :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        let i := bundle.selectedSlot
        (ProperBandQuadruple q) → (0 < (q i.succ).1) ) := by
  classical
  intro C D T N h k x bundle q i hq
  have hn := (ProperBandCurvatureStructure q hq).2.1 i
  have hne := bundle.configuration.noLine i.succ
  change (q i.succ).1 ≠ 0 at hne
  omega

private theorem hsub :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        let i := bundle.selectedSlot
        let e := bundle.selectedSign
        ∀ (hq : ProperBandQuadruple q), ∀ (hpos : 0 < (q i.succ).1),
        let C' : BandCircle := ⟨⟨q i.succ,
          ⟨Or.inl hpos, q, hq.1, i.succ, rfl⟩⟩, hpos⟩
        TileSubodometer bundle.normalizedCircle.1.1 C'.1.1 bundle.normalizedRoot (bundle.pieces i
            e) bundle.normalizedRootFunction (bundle.functions i e) ) := by
  classical
  intro C D T N h k x bundle q i e hq hpos C'
  refine ⟨?_, bundle.piece_odometer i e, bundle.piece_footprint i e,
    ?_, bundle.function_restriction i e, q, i, hq,
    bundle.normalized_circle_eq, rfl, e, bundle.piece_centroid i e,
    bundle.piece_slope i e⟩
  · rw [← bundle.normalized_circle_eq]
    exact bundle.normalized_root_odometer
  · intro y hy
    exact (bundle.function_domain_cover y).mpr ⟨i, e, hy⟩

private theorem hsize :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        let i := bundle.selectedSlot
        ∀ (hq : ProperBandQuadruple q), ∀ (hpos : 0 < (q i.succ).1),
        let C' : BandCircle := ⟨⟨q i.succ,
          ⟨Or.inl hpos, q, hq.1, i.succ, rfl⟩⟩, hpos⟩
        Int.toNat bundle.normalizedCircle.1.1.1 + Int.toNat C'.1.1.1 < Int.toNat
            bundle.normalizedCircle.1.1.1 + Int.toNat bundle.normalizedCircle.1.1.1 ) := by
  classical
  intro C D T N h k x bundle q i hq hpos C'
  have hlt := hq.2 i
  have hnat : Int.toNat (q i.succ).1 < Int.toNat (q 0).1 := by omega
  simpa only [q, bundle.normalized_circle_eq] using
    Nat.add_lt_add_left hnat (Int.toNat (q 0).1)

private theorem centralFoot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), FootprintVertices (SubtileOccurrenceInterpretation
            placement.layout.P placement.layout.u placement.layout.v placement.centralIndex) ⊆
            FootprintVertices bundle.normalizedFixed ) := by
  classical
  intro C D T N h k x bundle placement
  have zeroFoot (j : Fin 3) (s : Bool) :
      FootprintVertices (TileTranslation (placement.layout.P j s) 0) ⊆
        FootprintVertices bundle.normalizedFixed := by
    rw [(TileTranslationFormulas (placement.layout.P j s) 0).2.2.2.2.2.1]
    rintro y ⟨z, hz, rfl⟩
    simpa only [GaussianTranslation, add_zero] using
      (placement.layout.outer_occurrence j s).2.1 hz
  rcases placement.central_index with hA | hB | hC | hD | hE | hF
  · simpa [hA, SubtileOccurrenceInterpretation] using zeroFoot 0 true
  · simpa [hB, SubtileOccurrenceInterpretation] using zeroFoot 0 false
  · simpa [hC, SubtileOccurrenceInterpretation] using zeroFoot 1 true
  · simpa [hD, SubtileOccurrenceInterpretation] using zeroFoot 1 false
  · simpa [hE, SubtileOccurrenceInterpretation] using zeroFoot 2 true
  · simpa [hF, SubtileOccurrenceInterpretation] using zeroFoot 2 false

private theorem exteriorFoot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let i := bundle.selectedSlot
        let e := bundle.selectedSign
        FootprintVertices (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ⊆ FootprintVertices (bundle.pieces i e) )
            := by
  classical
  intro C D T N h k x bundle placement i e
  rw [placement.selected_exterior_footprint]

private theorem hxFixed :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt),
            (bundle.normalizedPoint ∈ selectedEdge) → ((selectedEdge ∈ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → ((FootprintVertices
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex) ⊆ FootprintVertices
            bundle.normalizedFixed) → ((TileOdometer bundle.normalizedCircle.1.1
            bundle.normalizedFixed bundle.normalizedFixedFunction) → (bundle.normalizedPoint ∈
            bundle.normalizedFixedFunction.domain)))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge hx hedge centralFoot hfixedO
  let U := SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
    placement.layout.v placement.centralIndex
  have hfoot : bundle.normalizedPoint ∈ FootprintVertices U := by
    have he : selectedEdge ∈ FootprintEdges U := hedge.2
    rcases he with ⟨z, hz, rfl | rfl | rfl | rfl⟩
    all_goals
      rw [FootprintVertices, ite_eq_left (show U.cells.Nonempty from ⟨z, hz⟩)]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      refine ⟨z, hz, ?_⟩
      rcases hx with hx | hx <;> simp [hx]
  change bundle.normalizedPoint ∈ (bundle.normalizedFixedFunction.domain : Set GaussianInt)
  rw [PositiveCurvatureTileOdometerDomain _ _ _ bundle.normalizedCircle.property hfixedO]
  exact centralFoot hfoot

private theorem hxSelected :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt),
            (bundle.normalizedPoint ∈ selectedEdge) → ((selectedEdge ∈ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → (
        let q := bundle.normalizedPresentation
        let i := bundle.selectedSlot
        let e := bundle.selectedSign
        (0 < (q i.succ).1) → ((FootprintVertices (SubtileOccurrenceInterpretation
            placement.layout.P placement.layout.u placement.layout.v placement.exteriorIndex) ⊆
            FootprintVertices (bundle.pieces i e)) → (bundle.normalizedPoint ∈ (bundle.functions
            i e).domain)))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge hx hedge q i e hpos exteriorFoot
  let U := SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
    placement.layout.v placement.exteriorIndex
  have hfoot : bundle.normalizedPoint ∈ FootprintVertices U := by
    have he : selectedEdge ∈ FootprintEdges U := hedge.1
    rcases he with ⟨z, hz, rfl | rfl | rfl | rfl⟩
    all_goals
      rw [FootprintVertices, ite_eq_left (show U.cells.Nonempty from ⟨z, hz⟩)]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      refine ⟨z, hz, ?_⟩
      rcases hx with hx | hx <;> simp [hx]
  change bundle.normalizedPoint ∈ ((bundle.functions i e).domain : Set GaussianInt)
  rw [PositiveCurvatureTileOdometerDomain _ _ _ hpos (bundle.piece_odometer i e)]
  exact exteriorFoot hfoot

private theorem hstar :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let i := bundle.selectedSlot
        let e := bundle.selectedSign
        (0 < (q i.succ).1) → ((FootprintVertices (SubtileOccurrenceInterpretation
            placement.layout.P placement.layout.u placement.layout.v placement.centralIndex) ⊆
            FootprintVertices bundle.normalizedFixed) → ((FootprintVertices
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ⊆ FootprintVertices (bundle.pieces i e))
            → ((TileOdometer bundle.normalizedCircle.1.1 bundle.normalizedFixed
            bundle.normalizedFixedFunction) → (∀ y, y = bundle.normalizedPoint ∨ y =
            bundle.normalizedPoint + 1 ∨ y = bundle.normalizedPoint - 1 ∨ y =
            bundle.normalizedPoint + ⟨0, 1⟩ ∨ y = bundle.normalizedPoint - ⟨0, 1⟩ → y ∈
            bundle.normalizedFixedFunction.domain ∨ y ∈ (bundle.functions i e).domain)))) ) := by
  classical
  intro C D T N h k x bundle placement q i e hpos centralFoot exteriorFoot hfixedO y hy
  rcases placement.selected_star y hy with hext | hcentral
  · right
    change y ∈ ((bundle.functions i e).domain : Set GaussianInt)
    rw [PositiveCurvatureTileOdometerDomain _ _ _ hpos (bundle.piece_odometer i e)]
    exact exteriorFoot hext
  · left
    change y ∈ (bundle.normalizedFixedFunction.domain : Set GaussianInt)
    rw [PositiveCurvatureTileOdometerDomain _ _ _ bundle.normalizedCircle.property hfixedO]
    exact centralFoot hcentral

private theorem rNext :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightFirstSlot + 1 = placement.rightSecondSlot )
            := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩
  all_goals simp [hr, ht]

private theorem rPrev :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightFirstSlot + 2 = placement.rightDirectionSlot
            ) := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩
  all_goals simp [hr, hk]

private theorem tNext :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightSecondSlot + 1 = placement.rightDirectionSlot
            ) := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩
  all_goals simp [ht, hk]

private theorem tPrev :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightSecondSlot + 2 = placement.rightFirstSlot )
            := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩
  all_goals simp [ht, hr]

private theorem hgeometry :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let i := bundle.selectedSlot
        let e := bundle.selectedSign
        (((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.1 (q
            placement.rightDirectionSlot.succ) (q placement.rightSecondSlot.succ) + (2 :
            GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            placement.rightDirectionSlot.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            (BandVectors.1 (q placement.rightFirstSlot.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q placement.rightFirstSlot.succ))) → ((-((1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.1 (q
            placement.rightFirstSlot.succ) (q placement.rightDirectionSlot.succ) + (2 :
            GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            placement.rightDirectionSlot.succ) = -(BandVectors.1 (q
            placement.rightSecondSlot.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4
            : ℕ))) (q placement.rightSecondSlot.succ))) → ((-((1 : GaussianInt) - (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt)) * BandVectors.1 (q placement.rightDirectionSlot.succ) (q
            placement.rightSecondSlot.succ) - (2 : GaussianInt) * BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q placement.rightDirectionSlot.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            (BandVectors.1 (q placement.rightFirstSlot.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q placement.rightFirstSlot.succ))) → ((((1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.1 (q
            placement.rightFirstSlot.succ) (q placement.rightDirectionSlot.succ) - (2 :
            GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            placement.rightDirectionSlot.succ) = BandVectors.1 (q placement.rightSecondSlot.succ)
            (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            placement.rightSecondSlot.succ)) → ((((1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) * BandVectors.2 (q placement.rightDirectionSlot.succ) (q
            placement.rightSecondSlot.succ) + (2 : GaussianInt) * BandVectors.2 (q (0 : Fin (4 :
            ℕ))) (q placement.rightDirectionSlot.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            (BandVectors.2 (q placement.rightFirstSlot.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q placement.rightFirstSlot.succ))) → ((-((1 :
            GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (q
            placement.rightFirstSlot.succ) (q placement.rightDirectionSlot.succ) + (2 :
            GaussianInt) * BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            placement.rightDirectionSlot.succ) = -(BandVectors.2 (q
            placement.rightSecondSlot.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.2 (q (0 : Fin (4
            : ℕ))) (q placement.rightSecondSlot.succ))) → ((-((1 : GaussianInt) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt)) * BandVectors.2 (q placement.rightDirectionSlot.succ) (q
            placement.rightSecondSlot.succ) - (2 : GaussianInt) * BandVectors.2 (q (0 : Fin (4 :
            ℕ))) (q placement.rightDirectionSlot.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            (BandVectors.2 (q placement.rightFirstSlot.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q placement.rightFirstSlot.succ))) → ((((1 :
            GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (q
            placement.rightFirstSlot.succ) (q placement.rightDirectionSlot.succ) - (2 :
            GaussianInt) * BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            placement.rightDirectionSlot.succ) = BandVectors.2 (q placement.rightSecondSlot.succ)
            (q (0 : Fin (4 : ℕ))) + BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            placement.rightSecondSlot.succ)) → ((∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ)
            (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ)))) → (∀ (p' :
            ℝ × ℝ), (p'.1 - placement.rightRootSlope.1 = (if e = true then (1 : ℝ) else (-1 : ℝ))
            * (1 / 2 : ℝ) * ((↑(BandVectors.2 (bundle.normalizedPresentation (i + (2 : Fin (3 :
            ℕ))).succ) (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((p'.2 -
            placement.rightRootSlope.2 = (if e = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) →
            ((placement.rightFirstSlot + 1 = placement.rightSecondSlot) →
            ((placement.rightFirstSlot + 2 = placement.rightDirectionSlot) →
            ((placement.rightSecondSlot + 1 = placement.rightDirectionSlot) →
            ((placement.rightSecondSlot + 2 = placement.rightFirstSlot) → (((TileCentroid
            (bundle.pieces i e) - TileCentroid bundle.normalizedRoot).1 = ((if e = true then (1 :
            ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ))).1))).1) →
            (((TileCentroid (bundle.pieces i e) - TileCentroid bundle.normalizedRoot).2 = ((if e
            = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (bundle.normalizedPresentation (i + (2 : Fin (3 : ℕ))).succ)
            (bundle.normalizedPresentation (i + (1 : Fin (3 : ℕ))).succ))).1))).2) →
            (((TileCentroid bundle.normalizedFixed - TileCentroid bundle.normalizedRoot).1 = ((if
            placement.rightNeighborPositive = true then (-1 : ℝ) else (1 : ℝ)) •
            GaussianRealPoint (BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation placement.rightDirectionSlot.succ))).1) →
            (((TileCentroid bundle.normalizedFixed - TileCentroid bundle.normalizedRoot).2 = ((if
            placement.rightNeighborPositive = true then (-1 : ℝ) else (1 : ℝ)) •
            GaussianRealPoint (BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation placement.rightDirectionSlot.succ))).2) →
            ((placement.rightFixedSlope.1 - placement.rightRootSlope.1 = (if
            placement.rightNeighborPositive = true then (-1 : ℝ) else (1 : ℝ)) * (↑(BandVectors.2
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightDirectionSlot.succ)).re : ℝ)) → ((placement.rightFixedSlope.2 -
            placement.rightRootSlope.2 = (if placement.rightNeighborPositive = true then (-1 : ℝ)
            else (1 : ℝ)) * (↑(BandVectors.2 (bundle.normalizedPresentation (0 : Fin (4 : ℕ)))
            (bundle.normalizedPresentation placement.rightDirectionSlot.succ)).im : ℝ)) → (∃ s :
            Fin 4, TileCentroid (bundle.pieces i e) - TileCentroid bundle.normalizedFixed = (1 /
            2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1 (q
            i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) ∧ p'.1 - placement.rightFixedSlope.1
            = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.2
            (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)))).1 ∧ p'.2 -
            placement.rightFixedSlope.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ s.val * (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q
            i.succ)))).2 ∧ (⟨0, 1⟩ : GaussianInt) ^ s.val * (if Even s.val then BandVectors.1 (q
            0) (q i.succ) else BandVectors.1 (q i.succ) (q 0)) = (if
            placement.rightNeighborPositive = true then (-1 : GaussianInt) else 1) *
            BandVectors.1 (q 0) (q i.succ)))))))))))))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement q i e vFirst vSecond vRefFirst vRefSecond aFirst aSecond
      aRefFirst aRefSecond flip p' hpieceRe hpieceIm rNext rPrev tNext tPrev hcentRe hcentIm
      hfixedRe hfixedIm hfixedSlopeRe hfixedSlopeIm
  rcases placement.boundary_signs with ⟨hpol, hfirst, hsecond⟩ | ⟨hpol, hfirst, hsecond⟩
  all_goals rcases placement.selected_boundary_piece with ⟨hslot, hsign⟩ | ⟨hslot, hsign⟩
  case' inl.inl =>
    have hslot' : i = placement.rightFirstSlot := hslot
    have hsign' : e = true := hsign.trans hfirst
    refine ⟨3, ?_⟩
    have hv := vFirst
    have ha := aFirst
  case' inl.inr =>
    have hslot' : i = placement.rightSecondSlot := hslot
    have hsign' : e = false := hsign.trans hsecond
    refine ⟨2, ?_⟩
    have hv := vSecond
    have ha := aSecond
  case' inr.inl =>
    have hslot' : i = placement.rightFirstSlot := hslot
    have hsign' : e = false := hsign.trans hfirst
    refine ⟨1, ?_⟩
    have hv := vRefFirst
    have ha := aRefFirst
  case' inr.inr =>
    have hslot' : i = placement.rightSecondSlot := hslot
    have hsign' : e = true := hsign.trans hsecond
    refine ⟨0, ?_⟩
    have hv := vRefSecond
    have ha := aRefSecond
  all_goals
    have hvRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) hv
    have hvIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) hv
    have haRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) ha
    have haIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) ha
    simp only [hslot', hsign', rNext, rPrev, tNext, tPrev] at hcentRe hcentIm
    simp only [hpol] at hfixedRe hfixedIm
    simp only [hslot', hsign', rNext, rPrev, tNext, tPrev] at hpieceRe hpieceIm
    simp only [hpol] at hfixedSlopeRe hfixedSlopeIm
    norm_num [GaussianRealPoint] at hcentRe hcentIm hfixedRe hfixedIm
    norm_num [GaussianRealPoint] at hpieceRe hpieceIm hfixedSlopeRe hfixedSlopeIm
    norm_num [GaussianRealPoint] at hvRe hvIm haRe haIm
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Prod.ext
      · norm_num [GaussianRealPoint, hslot', hsign', pow_succ]
        linarith only [hcentRe, hfixedRe, hvRe]
      · norm_num [GaussianRealPoint, hslot', hsign', pow_succ]
        linarith only [hcentIm, hfixedIm, hvIm]
    · norm_num [GaussianRealPoint, hslot', pow_succ]
      linarith only [hpieceRe, hfixedSlopeRe, haRe]
    · norm_num [GaussianRealPoint, hslot', pow_succ]
      linarith only [hpieceIm, hfixedSlopeIm, haIm]
    · have hflip := (flip i).1
      simp only [hslot'] at hflip
      ext <;> norm_num [hslot', hpol, pow_succ, hflip, even_iff_two_dvd]

private theorem hadj :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let i := bundle.selectedSlot
        let e := bundle.selectedSign
        ∀ (hq : ProperBandQuadruple q), ∀ (hpos : 0 < (q i.succ).1),
        let C' : BandCircle := ⟨⟨q i.succ,
          ⟨Or.inl hpos, q, hq.1, i.succ, rfl⟩⟩, hpos⟩
        (TileOdometer bundle.normalizedCircle.1.1 bundle.normalizedFixed
            bundle.normalizedFixedFunction) → (∀ (p' : ℝ × ℝ), (PartialOdometerSlope
            (bundle.functions i e) = some p') → (∀ (s : Fin (4 : ℕ)), (TileCentroid
            (bundle.pieces i e) - TileCentroid bundle.normalizedFixed = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))) →
            ((p'.1 - placement.rightFixedSlope.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))
            + BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)))).1) → ((p'.2 -
            placement.rightFixedSlope.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)))).2) → (SubtileLatticeAdjacent
            bundle.normalizedCircle C' bundle.normalizedFixed (bundle.pieces i e)
            bundle.normalizedFixedFunction (bundle.functions i e)))))) ) := by
  classical
  intro C D T N h k x bundle placement q i e hq hpos C' hfixedO p' hselectedSlope s hcent
      hslopeRe hslopeIm
  exact ⟨hfixedO, bundle.piece_odometer i e,
    placement.rightFixedSlope, p', placement.right_fixed_slope, hselectedSlope,
    q, i, s, hq, bundle.normalized_circle_eq, rfl, hcent, hslopeRe, hslopeIm⟩

end RightSelectedGeometry

theorem BandOrderedGeneralRightSelectedAdjacency :
    ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
        PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
        BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
        BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign
      bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt), (bundle.normalizedPoint ∈
          selectedEdge) → ((selectedEdge ∈
      FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩
        FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → ((BandOrderedGeneralSelectedContactRow
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixed placement.layout
      placement.exteriorIndex placement.centralIndex) → (
    let q := bundle.normalizedPresentation
    let i := bundle.selectedSlot
    let selectedTile := bundle.pieces i bundle.selectedSign
    let selectedFunction := bundle.functions i bundle.selectedSign
    let oldRight := TileTranslation bundle.normalizedFixed
      ((if placement.rightNeighborPositive = true then (-1 : GaussianInt)
          else 1) * BandVectors.1 (q 0) (q i.succ))
    ∃ (C' : BandCircle) (p₀ p' : ℝ × ℝ) (s : Fin 4),
      C'.1.1 = q i.succ ∧
      TileSubodometer bundle.normalizedCircle.1.1 C'.1.1
        bundle.normalizedRoot selectedTile bundle.normalizedRootFunction
        selectedFunction ∧
      PartialOdometerSlope bundle.normalizedFixedFunction = some p₀ ∧
      PartialOdometerSlope selectedFunction = some p' ∧
      ProperBandQuadruple q ∧ q 0 = bundle.normalizedCircle.1.1 ∧
      q i.succ = C'.1.1 ∧
      TileCentroid selectedTile - TileCentroid bundle.normalizedFixed =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) ∧
      p'.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
            BandVectors.2 (q 0) (q i.succ)))).1 ∧
      p'.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
            BandVectors.2 (q 0) (q i.succ)))).2 ∧
      SubtileLatticeAdjacent bundle.normalizedCircle C'
        bundle.normalizedFixed selectedTile bundle.normalizedFixedFunction
        selectedFunction ∧
      bundle.normalizedPoint ∈ bundle.normalizedFixedFunction.domain ∧
      bundle.normalizedPoint ∈ selectedFunction.domain ∧
      (∀ y, y = bundle.normalizedPoint ∨ y = bundle.normalizedPoint + 1 ∨
          y = bundle.normalizedPoint - 1 ∨
          y = bundle.normalizedPoint + ⟨0, 1⟩ ∨
          y = bundle.normalizedPoint - ⟨0, 1⟩ →
        y ∈ bundle.normalizedFixedFunction.domain ∨
          y ∈ selectedFunction.domain) ∧
      Int.toNat bundle.normalizedCircle.1.1.1 + Int.toNat C'.1.1.1 <
        Int.toNat bundle.normalizedCircle.1.1.1 +
          Int.toNat bundle.normalizedCircle.1.1.1 ∧
      TileTranslation bundle.normalizedFixed
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0))) = oldRight))) := by
  intro C D T N h k x bundle placement selectedEdge hx hedge row
-- BODY
  let q := bundle.normalizedPresentation
  let i := bundle.selectedSlot
  let e := bundle.selectedSign
  have hq : ProperBandQuadruple q := bundle.configuration.proper
  have hpos := RightSelectedGeometry.hpos C D T N h k x bundle hq
  let C' : BandCircle := ⟨⟨q i.succ,
    ⟨Or.inl hpos, q, hq.1, i.succ, rfl⟩⟩, hpos⟩
  have hsub := RightSelectedGeometry.hsub C D T N h k x bundle hq hpos
  have hsize := RightSelectedGeometry.hsize C D T N h k x bundle hq hpos
  have centralFoot := RightSelectedGeometry.centralFoot C D T N h k x bundle placement
  have exteriorFoot := RightSelectedGeometry.exteriorFoot C D T N h k x bundle placement
  have hfixedO : TileOdometer bundle.normalizedCircle.1.1
      bundle.normalizedFixed bundle.normalizedFixedFunction := placement.adjacency.2.1
  have hxFixed := RightSelectedGeometry.hxFixed C D T N h k x bundle placement selectedEdge hx
      hedge centralFoot hfixedO
  have hxSelected := RightSelectedGeometry.hxSelected C D T N h k x bundle placement selectedEdge
      hx hedge hpos exteriorFoot
  have hstar := RightSelectedGeometry.hstar C D T N h k x bundle placement hpos centralFoot
      exteriorFoot hfixedO
  obtain ⟨vFirst, vSecond, vRefFirst, vRefSecond,
    aFirst, aSecond, aRefFirst, aRefSecond, flip⟩ :=
    P3045T1RightBoundaryDisplacementAlgebra q hq placement.rightFirstSlot
      placement.rightSecondSlot placement.rightDirectionSlot placement.right_slots_cyclic
  obtain ⟨p, p', hrootSlope, hselectedSlope, hpieceRe, hpieceIm⟩ :=
    (bundle.piece_slope i e).resolve_left (ne_of_gt hpos)
  have hp : p = placement.rightRootSlope :=
    Option.some.inj (hrootSlope.symm.trans placement.right_root_slope)
  subst p
  have rNext := RightSelectedGeometry.rNext C D T N h k x bundle placement
  have rPrev := RightSelectedGeometry.rPrev C D T N h k x bundle placement
  have tNext := RightSelectedGeometry.tNext C D T N h k x bundle placement
  have tPrev := RightSelectedGeometry.tPrev C D T N h k x bundle placement
  have hcentRe := congrArg Prod.fst (bundle.piece_centroid i e)
  have hcentIm := congrArg Prod.snd (bundle.piece_centroid i e)
  have hfixedRe := congrArg Prod.fst placement.right_adjacency_centroid
  have hfixedIm := congrArg Prod.snd placement.right_adjacency_centroid
  have hfixedSlopeRe := placement.right_adjacency_slope_real
  have hfixedSlopeIm := placement.right_adjacency_slope_imag
  have hgeometry := RightSelectedGeometry.hgeometry C D T N h k x bundle placement vFirst vSecond
      vRefFirst vRefSecond aFirst aSecond aRefFirst aRefSecond flip p' hpieceRe hpieceIm rNext
      rPrev tNext tPrev hcentRe hcentIm hfixedRe hfixedIm hfixedSlopeRe hfixedSlopeIm
  obtain ⟨s, hcent, hslopeRe, hslopeIm, hcompanion⟩ := hgeometry
  have hadj := RightSelectedGeometry.hadj C D T N h k x bundle placement hq hpos hfixedO p'
      hselectedSlope s hcent hslopeRe hslopeIm
  refine ⟨C', placement.rightFixedSlope, p', s, rfl, hsub,
    placement.right_fixed_slope, hselectedSlope, hq, bundle.normalized_circle_eq,
    rfl, hcent, hslopeRe, hslopeIm, hadj, hxFixed, hxSelected, hstar, hsize, ?_⟩
  exact congrArg (TileTranslation bundle.normalizedFixed) hcompanion

end ApollonianSuperharmonic

end
