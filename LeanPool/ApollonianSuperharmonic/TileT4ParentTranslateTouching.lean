/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralChildInterfaces
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: TileT4ParentTranslateTouching]

/-!
# TileT4ParentTranslateTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileT4ParentTranslateTouching (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T₀ Tᵢ : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (hcurrentT2 : QuarterTurnSymmetric T₀) (i : Fin 3)
    (hTᵢ : BandPrototile (q i.succ) Tᵢ)
    (hcent : TileCentroid Tᵢ - TileCentroid T₀ =
      (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) :
    TouchingTriple T₀
      (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) Tᵢ := by
-- BODY
  have hdata := BandOrderedGeneralMixedAggregatePatches q cfg C₀ T₀ cert hcurrentT2
  have hj := hdata.1 i Tᵢ hTᵢ hcent
  rcases hj with ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, huAB, huBC, huCA, huABC, heAB, heBC, heCA⟩
  have hex := LatticeTileThreeDiskJunction
    T₀ (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) Tᵢ
    AB BC CA ABC hA hB hC hAB hBC hCA hABC hdAB hdBC hdCA
    huAB huBC huCA huABC heAB heBC heCA
  rcases hex with ⟨hex⟩
  have path_to_simple : ∀ (V : Set GaussianInt)
      (E : Set (Finset GaussianInt)) (x y : GaussianInt),
      SimpleGridPathBetween V E x y → SimpleGridPath V E := by
    intro V E x y hp
    rcases hp with ⟨p, hn, hl, hh, ht, hv, ha, he⟩
    exact ⟨p, hn, hl, hv, ha, he⟩
  have hab := LatticeTileDiskUnionInterface
    T₀ (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) AB
    hA hB hAB hdAB huAB heAB
  have hbc := LatticeTileDiskUnionInterface
    (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) Tᵢ BC
    hB hC hBC hdBC huBC heBC
  have hca := LatticeTileDiskUnionInterface Tᵢ T₀ CA
    hC hA hCA hdCA huCA heCA
  have hpathAB : SimpleGridPath
      (BoundaryFootprintVertices T₀ ∩
        BoundaryFootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))))
      (BoundaryFootprintEdges T₀ ∩
        BoundaryFootprintEdges (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0)))) := by
    rw [hab.2.2.2, ← hab.2.2.1]
    rcases hab.2.1 with ⟨x, y, hp⟩
    exact path_to_simple _ _ x y hp
  have hpathBC : SimpleGridPath
      (BoundaryFootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) ∩
        BoundaryFootprintVertices Tᵢ)
      (BoundaryFootprintEdges (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) ∩
        BoundaryFootprintEdges Tᵢ) := by
    rw [hbc.2.2.2, ← hbc.2.2.1]
    rcases hbc.2.1 with ⟨x, y, hp⟩
    exact path_to_simple _ _ x y hp
  have hpathCA : SimpleGridPath
      (BoundaryFootprintVertices Tᵢ ∩ BoundaryFootprintVertices T₀)
      (BoundaryFootprintEdges Tᵢ ∩ BoundaryFootprintEdges T₀) := by
    rw [hca.2.2.2, ← hca.2.2.1]
    rcases hca.2.1 with ⟨x, y, hp⟩
    exact path_to_simple _ _ x y hp
  have hneA : T₀.cells.Nonempty := by
    rcases heAB with ⟨e, he⟩
    rcases he.1 with ⟨x, hx, hrest⟩
    exact ⟨x, hx⟩
  have hneB : (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))).cells.Nonempty := by
    rcases heAB with ⟨e, he⟩
    rcases he.2 with ⟨x, hx, hrest⟩
    exact ⟨x, hx⟩
  have hneC : Tᵢ.cells.Nonempty := by
    rcases heBC with ⟨e, he⟩
    rcases he.2 with ⟨x, hx, hrest⟩
    exact ⟨x, hx⟩
  have hsetAB : BoundaryFootprintVertices T₀ ∩
      BoundaryFootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) =
      FootprintVertices T₀ ∩
        FootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) :=
    hab.2.2.2.trans hab.1.symm
  have hsetBC : BoundaryFootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) ∩
      BoundaryFootprintVertices Tᵢ =
      FootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) ∩
        FootprintVertices Tᵢ :=
    hbc.2.2.2.trans hbc.1.symm
  have hsetCA : BoundaryFootprintVertices Tᵢ ∩ BoundaryFootprintVertices T₀ =
      FootprintVertices Tᵢ ∩ FootprintVertices T₀ :=
    hca.2.2.2.trans hca.1.symm
  have htriple : ∀ x : GaussianInt,
      (x ∈ BoundaryFootprintVertices T₀ ∧
        x ∈ BoundaryFootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) ∧
        x ∈ BoundaryFootprintVertices Tᵢ) ↔
      x ∈ FootprintVertices T₀ ∧
        x ∈ FootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) ∧
        x ∈ FootprintVertices Tᵢ := by
    intro x
    constructor
    · intro hx
      have habx : x ∈ BoundaryFootprintVertices T₀ ∩
          BoundaryFootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) :=
        ⟨hx.1, hx.2.1⟩
      have hbcx : x ∈ BoundaryFootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q
          0))) ∩
          BoundaryFootprintVertices Tᵢ := ⟨hx.2.1, hx.2.2⟩
      have hfAB := hsetAB ▸ habx
      have hfBC := hsetBC ▸ hbcx
      exact ⟨hfAB.1, hfAB.2, hfBC.2⟩
    · intro hx
      have habx : x ∈ FootprintVertices T₀ ∩
          FootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) :=
        ⟨hx.1, hx.2.1⟩
      have hbcx : x ∈ FootprintVertices (TileTranslation T₀ (BandVectors.1 (q i.succ) (q 0))) ∩
          FootprintVertices Tᵢ := ⟨hx.2.1, hx.2.2⟩
      have hbAB := hsetAB.symm ▸ habx
      have hbBC := hsetBC.symm ▸ hbcx
      exact ⟨hbAB.1, hbAB.2, hbBC.2⟩
  unfold TouchingTriple
  refine ⟨?_, ?_, ?_, hex.point, ?_, ?_⟩
  · exact Or.inl ⟨hneA, hneB, hdAB, hpathAB⟩
  · exact Or.inl ⟨hneB, hneC, hdBC, hpathBC⟩
  · exact Or.inl ⟨hneC, hneA, hdCA, hpathCA⟩
  · have hp := (hex.unique_common hex.point).mpr rfl
    exact htriple hex.point |>.mpr ⟨hp.1.1, hp.1.2, hp.2⟩
  · intro x hx
    have hp := htriple x |>.mp hx
    exact (hex.unique_common x).mp ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩

end ApollonianSuperharmonic

end
