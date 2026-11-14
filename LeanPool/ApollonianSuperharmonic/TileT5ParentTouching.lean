/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralChildInterfaces

-- [TABLET NODE: TileT5ParentTouching]

/-!
# TileT5ParentTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileT5ParentTouching (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T₀ Tᵢ Tⱼ : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (hcurrentT2 : QuarterTurnSymmetric T₀) (i : Fin 3)
    (hTᵢ : BandPrototile (q i.succ) Tᵢ)
    (hTⱼ : BandPrototile (q ((i + 1).succ)) Tⱼ)
    (hcentᵢ : TileCentroid Tᵢ - TileCentroid T₀ =
      (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))))
    (hcentⱼ : TileCentroid Tⱼ - TileCentroid T₀ =
      (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) :
    TouchingTriple T₀ Tᵢ Tⱼ := by
-- BODY
  have aggregate := BandOrderedGeneralMixedAggregatePatches q cfg C₀ T₀ cert hcurrentT2
  dsimp at aggregate
  have makeTouching : ∀ (A B C AB BC CA ABC : ProtoTile),
      LatticeTile A → LatticeTile B → LatticeTile C →
      LatticeTile AB → LatticeTile BC → LatticeTile CA → LatticeTile ABC →
      Disjoint A.cells B.cells → Disjoint B.cells C.cells →
      Disjoint C.cells A.cells →
      (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) →
      (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) →
      (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) →
      (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) →
      (FootprintEdges A ∩ FootprintEdges B).Nonempty →
      (FootprintEdges B ∩ FootprintEdges C).Nonempty →
      (FootprintEdges C ∩ FootprintEdges A).Nonempty →
      ExactTileInterfaceTriple A B C → TouchingTriple A B C := by
    intro A B C AB BC CA ABC hA hB hC hAB hBC hCA hABC hdAB hdBC hdCA huAB huBC huCA huABC heAB
        heBC heCA exact
    have edgeCells : ∀ (X Y : ProtoTile),
        (FootprintEdges X ∩ FootprintEdges Y).Nonempty →
        X.cells.Nonempty ∧ Y.cells.Nonempty := by
      intro X Y h
      rcases h with ⟨e, heX, heY⟩
      constructor
      · change ∃ x ∈ X.cells, _ at heX
        rcases heX with ⟨x, hx, _⟩
        exact ⟨x, hx⟩
      · change ∃ x ∈ Y.cells, _ at heY
        rcases heY with ⟨x, hx, _⟩
        exact ⟨x, hx⟩
    have nonempty : A.cells.Nonempty ∧ B.cells.Nonempty ∧ C.cells.Nonempty := by
      have hab := edgeCells A B heAB
      have hbc := edgeCells B C heBC
      exact ⟨hab.1, hab.2, hbc.2⟩
    have interfaceAB := LatticeTileDiskUnionInterface A B AB hA hB hAB hdAB huAB heAB
    have interfaceBC := LatticeTileDiskUnionInterface B C BC hB hC hBC hdBC huBC heBC
    have interfaceCA := LatticeTileDiskUnionInterface C A CA hC hA hCA hdCA huCA heCA
    obtain ⟨xAB, yAB, pathAB⟩ := interfaceAB.2.1
    obtain ⟨xBC, yBC, pathBC⟩ := interfaceBC.2.1
    obtain ⟨xCA, yCA, pathCA⟩ := interfaceCA.2.1
    rw [← interfaceAB.2.2.2, interfaceAB.2.2.1] at pathAB
    rw [← interfaceBC.2.2.2, interfaceBC.2.2.1] at pathBC
    rw [← interfaceCA.2.2.2, interfaceCA.2.2.1] at pathCA
    have simpleAB : SimpleGridPath
        (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B)
        (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B) := by
      rcases pathAB with ⟨p, hn, hl, hh, ht, hv, he⟩
      exact ⟨p, hn, hl, hv, he⟩
    have simpleBC : SimpleGridPath
        (BoundaryFootprintVertices B ∩ BoundaryFootprintVertices C)
        (BoundaryFootprintEdges B ∩ BoundaryFootprintEdges C) := by
      rcases pathBC with ⟨p, hn, hl, hh, ht, hv, he⟩
      exact ⟨p, hn, hl, hv, he⟩
    have simpleCA : SimpleGridPath
        (BoundaryFootprintVertices C ∩ BoundaryFootprintVertices A)
        (BoundaryFootprintEdges C ∩ BoundaryFootprintEdges A) := by
      rcases pathCA with ⟨p, hn, hl, hh, ht, hv, he⟩
      exact ⟨p, hn, hl, hv, he⟩
    have touchAB : TileTouching A B := by
      unfold TileTouching
      left
      exact ⟨nonempty.1, nonempty.2.1, hdAB, simpleAB⟩
    have touchBC : TileTouching B C := by
      unfold TileTouching
      left
      exact ⟨nonempty.2.1, nonempty.2.2, hdBC, simpleBC⟩
    have touchCA : TileTouching C A := by
      unfold TileTouching
      left
      exact ⟨nonempty.2.2, nonempty.1, hdCA, simpleCA⟩
    refine ⟨touchAB, touchBC, touchCA, ?_⟩
    have pointCommon : exact.point ∈ BoundaryFootprintVertices A ∧
        exact.point ∈ BoundaryFootprintVertices B ∧
        exact.point ∈ BoundaryFootprintVertices C := by
      have hab : exact.point ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B := by
        have hpoint := (exact.unique_common exact.point).mpr rfl
        have hab0 : exact.point ∈ FootprintVertices A ∩ FootprintVertices B :=
          hpoint.1
        have commonAB : exact.point ∈ CommonFootprintEdgeVertices A B := by
          rw [← interfaceAB.1]
          exact hab0
        rw [interfaceAB.2.2.2]
        exact commonAB
      have hbc : exact.point ∈ BoundaryFootprintVertices B ∩ BoundaryFootprintVertices C := by
        have hpoint := (exact.unique_common exact.point).mpr rfl
        have hbc0 : exact.point ∈ FootprintVertices B ∩ FootprintVertices C :=
          ⟨hpoint.1.2, hpoint.2⟩
        have commonBC : exact.point ∈ CommonFootprintEdgeVertices B C := by
          rw [← interfaceBC.1]
          exact hbc0
        rw [interfaceBC.2.2.2]
        exact commonBC
      change exact.point ∈ BoundaryFootprintVertices A ∧
        exact.point ∈ BoundaryFootprintVertices B at hab
      change exact.point ∈ BoundaryFootprintVertices B ∧
        exact.point ∈ BoundaryFootprintVertices C at hbc
      exact ⟨hab.1, hab.2, hbc.2⟩
    refine ⟨exact.point, pointCommon, ?_⟩
    intro x hx
    apply (exact.unique_common _).mp
    have hab : x ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B := by
      exact ⟨hx.1, hx.2.1⟩
    have hbc : x ∈ BoundaryFootprintVertices B ∩ BoundaryFootprintVertices C := by
      exact ⟨hx.2.1, hx.2.2⟩
    have commonAB : x ∈ CommonFootprintEdgeVertices A B := by
      rw [← interfaceAB.2.2.2]
      exact hab
    have commonBC : x ∈ CommonFootprintEdgeVertices B C := by
      rw [← interfaceBC.2.2.2]
      exact hbc
    have footAB : x ∈ FootprintVertices A ∩ FootprintVertices B := by
      rw [interfaceAB.1]
      exact commonAB
    have footBC : x ∈ FootprintVertices B ∩ FootprintVertices C := by
      rw [interfaceBC.1]
      exact commonBC
    exact ⟨footAB, footBC.2⟩
  have junction := aggregate.2.1 i Tᵢ Tⱼ hTᵢ hTⱼ hcentᵢ hcentⱼ
  obtain ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, huAB, huBC, huCA, huABC, heAB, heBC, heCA⟩ := junction
  exact makeTouching T₀ Tᵢ Tⱼ AB BC CA ABC hA hB hC hAB hBC hCA hABC
    hdAB hdBC hdCA huAB huBC huCA huABC heAB heBC heCA
    (Classical.choice ((BandOrderedGeneralChildInterfaces q cfg C₀ T₀ cert hcurrentT2).2.2.1
      i Tᵢ Tⱼ hTᵢ hTⱼ hcentᵢ hcentⱼ))

end ApollonianSuperharmonic

end
