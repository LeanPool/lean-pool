/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4418T3SelectedInterfaceExists
public import LeanPool.ApollonianSuperharmonic.P4418T3OuterCompanionAlignment
public import LeanPool.ApollonianSuperharmonic.P4418T3PresentedRowAdjacency
public import LeanPool.ApollonianSuperharmonic.P4418T3RoutedBlockCriterion
public import LeanPool.ApollonianSuperharmonic.P4418T3NestedCompanionGeometry
public import LeanPool.ApollonianSuperharmonic.P4418T3NestedCompanionEndpoint
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileSubodometer
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: BandOrderedGeneralSubtileSelectedRowGeometry]

/-!
# BandOrderedGeneralSubtileSelectedRowGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralSubtileSelectedRowGeometry :
    ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
        PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
        BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
        BandOrderedGeneralSubtilePlacement
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixedCircle
      bundle.normalizedRoot bundle.normalizedFixed
      bundle.normalizedRootFunction bundle.normalizedFixedFunction
      bundle.normalizedPoint bundle.pieces bundle.functions
      bundle.selectedSlot bundle.selectedSign bundle.routedDirection), ∀ (selectedEdge : Finset
          GaussianInt), (bundle.normalizedPoint ∈ selectedEdge) → ((selectedEdge ∈
      FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩
        FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → ((BandOrderedGeneralSelectedContactRow
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedRoot placement.layout
      placement.exteriorIndex placement.centralIndex) → ((¬ ((∃ (g : BandPackingSymmetry) (P :
          FordFareyParameter),
          BandPackingSymmetryCircleAction g
            (FordCircleCoordinate P.p P.q) = bundle.normalizedCircle.1.1) ∨
        (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
          BandPackingSymmetryCircleAction g
            (DiamondRecursiveQuadruple K 0) = bundle.normalizedCircle.1.1))) → (∀ (r : Fin 4 →
                CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), (ProperBandQuadruple r) → ((r 0
                = bundle.normalizedCircle.1.1) → ((r i.succ = bundle.normalizedFixedCircle.1.1) →
                ((TileCentroid bundle.normalizedFixed -
        TileCentroid bundle.normalizedRoot =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
           BandVectors.1 (r 0) (r i.succ)))) → ((bundle.normalizedFixedSlope.1 -
        bundle.normalizedRootSlope.1 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (r i.succ) (r 0) +
           BandVectors.2 (r 0) (r i.succ)))).1) → ((bundle.normalizedFixedSlope.2 -
        bundle.normalizedRootSlope.2 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (r i.succ) (r 0) +
           BandVectors.2 (r 0) (r i.succ)))).2) → (
    let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
    let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
    let oldRight := TileTranslation bundle.normalizedRoot
      ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (r 0) (r i.succ)
          else BandVectors.1 (r i.succ) (r 0)))
    ∃ (C' : BandCircle) (selectedSlope : ℝ × ℝ),
      C'.1.1 = bundle.normalizedPresentation bundle.selectedSlot.succ ∧
      TileSubodometer bundle.normalizedCircle.1.1 C'.1.1
        bundle.normalizedRoot selectedSupport bundle.normalizedRootFunction
        selectedFunction ∧
      PartialOdometerSlope selectedFunction = some selectedSlope ∧
      bundle.normalizedPoint ∈ bundle.normalizedFixedFunction.domain ∧
      bundle.normalizedPoint ∈ selectedFunction.domain ∧
      (∀ y, y = bundle.normalizedPoint ∨ y = bundle.normalizedPoint + 1 ∨
          y = bundle.normalizedPoint - 1 ∨
          y = bundle.normalizedPoint + ⟨0, 1⟩ ∨
          y = bundle.normalizedPoint - ⟨0, 1⟩ →
        y ∈ bundle.normalizedFixedFunction.domain ∨
          y ∈ selectedFunction.domain) ∧
      Int.toNat bundle.normalizedFixedCircle.1.1.1 + Int.toNat C'.1.1.1 <
        Int.toNat bundle.normalizedCircle.1.1.1 +
          Int.toNat bundle.normalizedFixedCircle.1.1.1 ∧
      ((C' = bundle.normalizedFixedCircle ∧
          LeftLatticeAdjacent bundle.normalizedFixedCircle
            bundle.normalizedFixed selectedSupport
            bundle.normalizedFixedFunction selectedFunction ∧
          bundle.normalizedPoint ∉ FootprintVertices oldRight) ∨
        (∃ (q : Fin 4 → CircleCoordinates) (j : Fin 3) (t : Fin 4),
          ProperBandQuadruple q ∧
          q 0 = bundle.normalizedFixedCircle.1.1 ∧ q j.succ = C'.1.1 ∧
          TileCentroid selectedSupport - TileCentroid bundle.normalizedFixed =
            (1 / 2 : ℝ) • GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.1 (q j.succ) (q 0) +
                 BandVectors.1 (q 0) (q j.succ))) ∧
          selectedSlope.1 - bundle.normalizedFixedSlope.1 =
            ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (q j.succ) (q 0) +
                 BandVectors.2 (q 0) (q j.succ)))).1 ∧
          selectedSlope.2 - bundle.normalizedFixedSlope.2 =
            ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (q j.succ) (q 0) +
                 BandVectors.2 (q 0) (q j.succ)))).2 ∧
          SubtileLatticeAdjacent bundle.normalizedFixedCircle C'
            bundle.normalizedFixed selectedSupport
            bundle.normalizedFixedFunction selectedFunction ∧
          (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
            bundle.normalizedPoint ∈ FootprintVertices
              (TileTranslation bundle.normalizedFixed
                ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                  (if Even t.val then BandVectors.1 (q 0) (q j.succ)
                    else BandVectors.1 (q j.succ) (q 0)))))) ∨
        (∃ (q : Fin 4 → CircleCoordinates) (j : Fin 3) (t : Fin 4),
          ProperBandQuadruple q ∧ q 0 = C'.1.1 ∧
          q j.succ = bundle.normalizedFixedCircle.1.1 ∧
          TileCentroid bundle.normalizedFixed - TileCentroid selectedSupport =
            (1 / 2 : ℝ) • GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.1 (q j.succ) (q 0) +
                 BandVectors.1 (q 0) (q j.succ))) ∧
          bundle.normalizedFixedSlope.1 - selectedSlope.1 =
            ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (q j.succ) (q 0) +
                 BandVectors.2 (q 0) (q j.succ)))).1 ∧
          bundle.normalizedFixedSlope.2 - selectedSlope.2 =
            ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (q j.succ) (q 0) +
                 BandVectors.2 (q 0) (q j.succ)))).2 ∧
          SubtileLatticeAdjacent C' bundle.normalizedFixedCircle
            selectedSupport bundle.normalizedFixed selectedFunction
            bundle.normalizedFixedFunction ∧
          (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
            bundle.normalizedPoint ∈ FootprintVertices
              (TileTranslation selectedSupport
                ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                  (if Even t.val then BandVectors.1 (q 0) (q j.succ)
                    else BandVectors.1 (q j.succ) (q 0))))))))))))))))) := by
  intro C D T N h k x bundle placement selectedEdge hx hedge row horbit r i s hr hr0 hri
      hcentroid hslopex hslopey
-- BODY
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let cert := placement.layout
  let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
  let a := placement.exteriorIndex
  let b := placement.centralIndex
  let S := bundle.pieces bundle.selectedSlot bundle.selectedSign
  let f := bundle.functions bundle.selectedSlot bundle.selectedSign
  have hq : ProperBandQuadruple q := cfg.proper
  have hpos : 0 < (q bundle.selectedSlot.succ).1 := by
    have hn := (ProperBandCurvatureStructure q hq).2.1 bundle.selectedSlot
    have hne := cfg.noLine bundle.selectedSlot.succ
    change (q bundle.selectedSlot.succ).1 ≠ 0 at hne
    omega
  let C' : BandCircle := ⟨⟨q bundle.selectedSlot.succ,
    ⟨Or.inl hpos, q, hq.1, bundle.selectedSlot.succ, rfl⟩⟩, hpos⟩
  have hsub : TileSubodometer bundle.normalizedCircle.1.1 C'.1.1
      bundle.normalizedRoot S bundle.normalizedRootFunction f := by
    refine ⟨?_, bundle.piece_odometer _ _, bundle.piece_footprint _ _,
      ?_, bundle.function_restriction _ _, q, bundle.selectedSlot, hq,
      bundle.normalized_circle_eq, rfl, bundle.selectedSign,
      bundle.piece_centroid _ _, bundle.piece_slope _ _⟩
    · rw [← bundle.normalized_circle_eq]
      exact bundle.normalized_root_odometer
    · intro y hy
      exact (bundle.function_domain_cover y).mpr
        ⟨bundle.selectedSlot, bundle.selectedSign, hy⟩
  obtain ⟨p, hp⟩ : ∃ p, PartialOdometerSlope f = some p := by
    rcases bundle.piece_slope bundle.selectedSlot bundle.selectedSign with
      hz | ⟨p₀, p, _, hp, _, _⟩
    · change (q bundle.selectedSlot.succ).1 = 0 at hz
      omega
    · exact ⟨p, hp⟩
  have exteriorFoot : FootprintVertices (occurrence a) =
      FootprintVertices bundle.normalizedFixed :=
    (ProtoTileObservableExtensionality _ _ placement.fixed_exterior_cells
      placement.fixed_exterior_empty_anchor).1
  have centralFoot : FootprintVertices (occurrence b) = FootprintVertices S := by
    change FootprintVertices (occurrence placement.centralIndex) = FootprintVertices S
    rw [placement.selected_central_index]
    exact (placement.piece_layout_footprint _ _).symm
  have edgeVertex (U : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges U) (y : GaussianInt) (hy : y ∈ e) :
      y ∈ FootprintVertices U := by
    rcases he with ⟨c, hc, he⟩
    unfold FootprintVertices
    rw [ite_eq_left ⟨c, hc⟩]
    rcases he with he | he | he | he <;> subst e
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    all_goals rcases hy with rfl | rfl
    all_goals exact ⟨_, hc, by simp⟩
  have fixedDomain := PositiveCurvatureTileOdometerDomain
    bundle.normalizedFixedCircle.1.1 bundle.normalizedFixed
    bundle.normalizedFixedFunction bundle.normalizedFixedCircle.property
    bundle.normalized_fixed_odometer
  have selectedDomain := PositiveCurvatureTileOdometerDomain C'.1.1 S f
    C'.property hsub.2.1
  have hxFixed : bundle.normalizedPoint ∈ bundle.normalizedFixedFunction.domain := by
    apply (Set.ext_iff.mp fixedDomain _).mpr
    rw [← exteriorFoot]
    exact edgeVertex _ _ hedge.1 _ hx
  have hxSelected : bundle.normalizedPoint ∈ f.domain := by
    apply (Set.ext_iff.mp selectedDomain _).mpr
    rw [← centralFoot]
    exact edgeVertex _ _ hedge.2 _ hx
  have hstar : ∀ y, y = bundle.normalizedPoint ∨ y = bundle.normalizedPoint + 1 ∨
      y = bundle.normalizedPoint - 1 ∨ y = bundle.normalizedPoint + ⟨0, 1⟩ ∨
      y = bundle.normalizedPoint - ⟨0, 1⟩ →
      y ∈ bundle.normalizedFixedFunction.domain ∨ y ∈ f.domain := by
    intro y hy
    rcases placement.selected_star y hy with h | h
    · exact Or.inl ((Set.ext_iff.mp fixedDomain y).mpr (exteriorFoot ▸ h))
    · exact Or.inr ((Set.ext_iff.mp selectedDomain y).mpr (centralFoot ▸ h))
  have hsize :
      Int.toNat bundle.normalizedFixedCircle.1.1.1 + Int.toNat C'.1.1.1 <
        Int.toNat bundle.normalizedCircle.1.1.1 +
          Int.toNat bundle.normalizedFixedCircle.1.1.1 := by
    have hlt := hq.2 bundle.selectedSlot
    have hrootpos := (ProperBandCurvatureStructure q hq).1
    have hnat : Int.toNat (q bundle.selectedSlot.succ).1 <
        Int.toNat (q 0).1 := (Int.toNat_lt_toNat hrootpos).mpr hlt
    change Int.toNat bundle.normalizedFixedCircle.1.1.1 +
        Int.toNat (q bundle.selectedSlot.succ).1 <
      Int.toNat bundle.normalizedCircle.1.1.1 +
        Int.toNat bundle.normalizedFixedCircle.1.1.1
    have heq : q 0 = bundle.normalizedCircle.1.1 := bundle.normalized_circle_eq
    rw [heq] at hnat
    omega
  obtain ⟨data⟩ := P4418T3SelectedInterfaceExists q cfg
    bundle.normalizedCircle bundle.normalizedRoot cert a b row
  have twice : bundle.routedDirection + 2 + 2 = bundle.routedDirection := by
    generalize bundle.routedDirection = d
    fin_cases d <;> rfl
  have mark := P4418T3RoutedBlockCriterion q cfg bundle.normalizedCircle
    bundle.normalizedRoot cert a b row bundle.root_lattice data
    bundle.normalizedPoint (bundle.routedDirection + 2) selectedEdge hx hedge
    placement.exterior_routed_cell
    (by simpa only [twice] using placement.central_routed_cell)
  have align := (P4418T3OuterCompanionAlignment C D T N h k x bundle
    placement row r i s hr hr0 hri hcentroid hslopex hslopey).2.2
  dsimp only at mark
  have mark := (congrArg (fun d => bundle.normalizedPoint ∈
    FootprintVertices (TileTranslation bundle.normalizedRoot d)) align).to_iff.trans mark
  have adj := P4418T3PresentedRowAdjacency C D T N h k x bundle placement
    row r i s hr hr0 hri hcentroid hslopex hslopey C' p rfl hp hsub
  refine ⟨C', p, rfl, hsub, hp, hxFixed, hxSelected, hstar, hsize, ?_⟩
  cases ht : P3996T1SRowTable q cfg bundle.normalizedCircle
      bundle.normalizedRoot cert row with
  | none =>
      rw [ht] at adj mark
      exact Or.inl ⟨adj.1, adj.2, fun hxOld => mark.mp hxOld⟩
  | some z =>
      rw [ht] at adj mark
      obtain ⟨⟨E⟩, hcontained, hfoot⟩ := P4418T3NestedCompanionGeometry q cfg
        bundle.normalizedCircle bundle.normalizedRoot cert a b row z ht
      have endpoint := P4418T3NestedCompanionEndpoint q cfg
        bundle.normalizedCircle bundle.normalizedRoot cert a b row data z ht E hcontained
      have reducedMark :
          bundle.normalizedPoint ∈ FootprintVertices
            (TileTranslation bundle.normalizedRoot
              ((⟨0, 1⟩ : GaussianInt) ^ s.val *
                (if Even s.val then BandVectors.1 (r 0) (r i.succ)
                 else BandVectors.1 (r i.succ) (r 0)))) ↔
          bundle.normalizedPoint ∈ FootprintVertices
            (TileTranslation (occurrence z.childIndex) z.rightShift) := by
        constructor
        · intro hxOld
          have heq : bundle.normalizedPoint = E.point :=
            (mark.mp hxOld).trans endpoint.symm
          exact ((E.unique_common _).mpr heq).1.2
        · intro hxNew
          rw [align]
          have ht' : P3996T1SRowTable bundle.normalizedPresentation
              bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
              placement.layout row = some z := ht
          simpa only [ht'] using hfoot hxNew
      obtain ⟨_, _, _, _, _, _, hindices, _, hd, _, _⟩ :=
        P3996T1SRowAlignment q cfg bundle.normalizedCircle
          bundle.normalizedRoot cert a b row z ht
      have translateFoot (U V : ProtoTile)
          (hf : FootprintVertices U = FootprintVertices V) (d : GaussianInt) :
          FootprintVertices (TileTranslation U d) =
            FootprintVertices (TileTranslation V d) := by
        rw [(TileTranslationFormulas U d).2.2.2.2.2.1,
          (TileTranslationFormulas V d).2.2.2.2.2.1, hf]
      cases hflag : z.childIsExterior
      · simp only [hflag, Bool.false_eq_true, ↓reduceIte] at adj hindices
        have hcfoot : FootprintVertices (occurrence z.childIndex) =
            FootprintVertices S := by
          rw [hindices.1]
          exact centralFoot
        rw [translateFoot _ _ hcfoot, hd] at reducedMark
        rcases adj with ⟨hpr, h₀, hj, hc, hs, hadj⟩
        exact Or.inr (Or.inr ⟨z.predecessor, z.parentSlot, z.rotation,
          hpr, h₀, hj, hc, congrArg Prod.fst hs, congrArg Prod.snd hs,
          hadj, reducedMark⟩)
      · simp only [hflag, ↓reduceIte] at adj hindices
        have hcfoot : FootprintVertices (occurrence z.childIndex) =
            FootprintVertices bundle.normalizedFixed := by
          rw [hindices.1]
          exact exteriorFoot
        rw [translateFoot _ _ hcfoot, hd] at reducedMark
        rcases adj with ⟨hpr, h₀, hj, hc, hs, hadj⟩
        exact Or.inr (Or.inl ⟨z.predecessor, z.parentSlot, z.rotation,
          hpr, h₀, hj, hc, congrArg Prod.fst hs, congrArg Prod.snd hs,
          hadj, reducedMark⟩)

end ApollonianSuperharmonic

end
