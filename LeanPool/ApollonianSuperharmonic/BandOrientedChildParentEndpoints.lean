/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.FordOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.DiamondOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayout
public import LeanPool.ApollonianSuperharmonic.P4055T1PlacementNormalization
public import LeanPool.ApollonianSuperharmonic.P4055T1BandQuarterTurn
public import LeanPool.ApollonianSuperharmonic.P4055T1OrderedGeneralOppositeEndpoints
public import LeanPool.ApollonianSuperharmonic.P4055T1PackingGridEquivalence
public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage

-- [TABLET NODE: BandOrientedChildParentEndpoints]

/-!
# BandOrientedChildParentEndpoints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OrientedEndpointGeometry

private theorem hregimeNormalized :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        (Xor (∃ (P : FordFareyParameter), (1 : ℕ) < P.q ∧ BandPackingSymmetryQuadrupleAction g' p
            = FordRecursiveQuadruple P) (Xor (∃ (K : DiamondParameter), (1 : ℕ) < K.1 ∧
            BandPackingSymmetryQuadrupleAction g' p = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g' p))))) → (Xor
            (∃ P, 1 < P.q ∧ qg = FordRecursiveQuadruple P) (Xor (∃ K : DiamondParameter, 1 < K.1
            ∧ qg = DiamondRecursiveQuadruple K) (Nonempty (BandOrderedGeneralConfiguration qg))))
            ) := by
  classical
  intro r a g' p qg hregimeQ
  simpa [qg] using hregimeQ

private theorem normalized :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), ∀ (a : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let U' := BandPackingSymmetryTileAction g' U
        let W' := BandPackingSymmetryTileAction g' W
        let Z' := BandPackingSymmetryTileAction g' Z
        let ii : GaussianInt := ⟨0, 1⟩
        (ProperBandQuadruple qg) → ((BandPrototile (qg (0 : Fin (4 : ℕ))) U') → ((BandPrototile
            (qg k.succ) W') → ((BandPrototile (qg j.succ) Z') → (((0 : ℤ) < (qg (0 : Fin (4 :
            ℕ))).1) → (((0 : ℤ) < (qg k.succ).1) → (((0 : ℤ) < (qg j.succ).1) → ((TileCentroid W'
            - TileCentroid U' = (1 / 2 : ℝ) • GaussianRealPoint (ii ^ (↑t : ℕ) * (BandVectors.1
            (qg k.succ) (qg (0 : Fin (4 : ℕ))) + BandVectors.1 (qg (0 : Fin (4 : ℕ))) (qg
            k.succ)))) → ((TileCentroid Z' - TileCentroid U' = (1 / 2 : ℝ) • GaussianRealPoint
            (ii ^ (↑t : ℕ) * if Even (↑t : ℕ) then BandVectors.1 (qg (0 : Fin (4 : ℕ))) (qg
            j.succ) - BandVectors.1 (qg j.succ) (qg (0 : Fin (4 : ℕ))) else BandVectors.1 (qg
            j.succ) (qg (0 : Fin (4 : ℕ))) - BandVectors.1 (qg (0 : Fin (4 : ℕ))) (qg j.succ))) →
            ((Xor (∃ P, 1 < P.q ∧ qg = FordRecursiveQuadruple P) (Xor (∃ K : DiamondParameter, 1
            < K.1 ∧ qg = DiamondRecursiveQuadruple K) (Nonempty (BandOrderedGeneralConfiguration
            qg)))) → (
        let uR := (⟨0, 1⟩ : GaussianInt) ^ t.val *
          (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
            else BandVectors.1 (qg k.succ) (qg 0))
        let uL := (⟨0, 1⟩ : GaussianInt) ^ t.val *
          (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
            else BandVectors.1 (qg 0) (qg k.succ))
        ∃ rightData : ExactTileInterfaceTriple U' (TileTranslation U' uR) W',
          ∃ incomingData : ExactTileInterfaceTriple U' (TileTranslation U' uL) W',
            ∃ adjacentData : ExactTileInterfaceTriple U' W' Z',
              rightData.point ≠ incomingData.point ∧
              adjacentData.point = incomingData.point ∧
              rightData.otherCA = incomingData.point ∧
              incomingData.otherCA = rightData.point ∧
              adjacentData.otherAB = rightData.point)))))))))) ) := by
  classical
  intro r i s U W Z a g' p qg k t j U' W' Z' ii hproperG hU' hW' hZ' hUpos' hWpos' hZpos'
      hWcentNorm hZcentNorm hregimeNormalized
  rcases hregimeNormalized with ⟨hFord, _⟩ | ⟨hrest, _⟩
  · rcases hFord with ⟨P, hP, hqFord⟩
    have hUF : BandPrototile (FordRecursiveQuadruple P 0) U' := by
      simpa [hqFord] using hU'
    have hWF : BandPrototile (FordRecursiveQuadruple P k.succ)
        (BandPackingSymmetryTileAction g' W) := by
      simpa [hqFord] using hW'
    have hZF : BandPrototile
        (FordRecursiveQuadruple P j.succ) (BandPackingSymmetryTileAction g' Z) := by
      simpa [hqFord] using hZ'
    have hUFpos : 0 < (FordRecursiveQuadruple P 0).1 := by
      simpa [hqFord] using hUpos'
    have hWFpos : 0 < (FordRecursiveQuadruple P k.succ).1 := by
      simpa [hqFord] using hWpos'
    have hZFpos : 0 < (FordRecursiveQuadruple P j.succ).1 := by
      simpa [hqFord] using hZpos'
    have _fordData := FordOrientedChildParentEndpoints P hP k t U'
      W' Z' hUF hWF hZF hUFpos hWFpos hZFpos
      (by simpa [hqFord, ii, U', W'] using hWcentNorm)
      (by
        by_cases ht : Even t.val
        · simpa [ht, hqFord, ii, U', Z', j] using hZcentNorm
        · simpa [ht, hqFord, ii, U', Z', j] using hZcentNorm)
    rw [hqFord]
    exact _fordData
  · rcases hrest with ⟨hDiamond, _⟩ | ⟨hGeneral, _⟩
    · rcases hDiamond with ⟨K, hK, hqDiamond⟩
      have hUD : BandPrototile (DiamondRecursiveQuadruple K 0) U' := by
        simpa [hqDiamond] using hU'
      have hWD : BandPrototile (DiamondRecursiveQuadruple K k.succ)
          (BandPackingSymmetryTileAction g' W) := by
        simpa [hqDiamond] using hW'
      have hZD : BandPrototile
          (DiamondRecursiveQuadruple K j.succ) (BandPackingSymmetryTileAction g' Z) := by
        simpa [hqDiamond] using hZ'
      have hUDpos : 0 < (DiamondRecursiveQuadruple K 0).1 := by
        simpa [hqDiamond] using hUpos'
      have hWDpos : 0 < (DiamondRecursiveQuadruple K k.succ).1 := by
        simpa [hqDiamond] using hWpos'
      have hZDpos : 0 < (DiamondRecursiveQuadruple K j.succ).1 := by
        simpa [hqDiamond] using hZpos'
      have _diamondData := DiamondOrientedChildParentEndpoints K k t U'
        W' Z' hUD hWD hZD hUDpos hWDpos hZDpos
        (by simpa [hqDiamond, ii, U', W'] using hWcentNorm)
        (by
          by_cases ht : Even t.val
          · simpa [ht, hqDiamond, ii, U', Z', j] using hZcentNorm
          · simpa [ht, hqDiamond, ii, U', Z', j] using hZcentNorm)
      rw [hqDiamond]
      exact _diamondData
    · rcases hGeneral with ⟨cfg⟩
      let C₀ : BandCircle :=
        ⟨⟨qg 0, Or.inl hUpos', ⟨qg, hproperG.1, ⟨0, rfl⟩⟩⟩, hUpos'⟩
      have hUQuarter : QuarterTurnSymmetric U' :=
        (BandTileSimultaneousInduction qg hproperG U' hU').2.2.2.1
      have hcertificate := BandOrderedGeneralLayout qg cfg C₀ rfl U' hU'
        (by
          intro q₀ T₀ S₀ hq₀ hT₀ hocc hunion hsmall
          have hI := BandTileSimultaneousInduction q₀ hq₀ T₀ hT₀
          exact ⟨hI.1, hI.2.1, hI.2.2.1 S₀ hocc hunion⟩)
        (fun D V hV _ => P4055T1BandQuarterTurn D V hV)
        (by
          intro q₀ T₀ V hq₀ hT₀ hsmall hlarge m hV hcent
          exact (BandTileSimultaneousInduction q₀ hq₀ T₀ hT₀).2.2.2.2.2.1
            hlarge m V hV hcent)
        (by
          intro q₀ T₀ V W hq₀ hT₀ hsmall m hV hW hcentV hcentW
          exact (BandTileSimultaneousInduction q₀ hq₀ T₀ hT₀).2.2.2.2.2.2.1
            m V W hV hW hcentV hcentW)
      rcases hcertificate with ⟨cert⟩
      exact P4055T1OrderedGeneralOppositeEndpoints qg hproperG cfg C₀
        k t U' W' Z' hU' hW' hZ' hUpos' hWpos' hZpos' hWcentNorm
        (by
          by_cases ht : Even t.val <;>
            simpa only [j, ht, ite_true, ite_false] using hZcentNorm)
        cert hUQuarter (P4055T1BandQuarterTurn _ _ hW')
        (P4055T1BandQuarterTurn _ _ hZ')

private theorem transR :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (a
            : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let U' := BandPackingSymmetryTileAction g' U
        let ii : GaussianInt := ⟨0, 1⟩
        (BandPackingSymmetryVectorAction g' (ii ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1
            (r (0 : Fin (4 : ℕ))) (r i.succ) else BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))))
            = ii ^ (↑t : ℕ) * if Even (↑t : ℕ) then BandVectors.1 (qg (0 : Fin (4 : ℕ))) (qg
            k.succ) else BandVectors.1 (qg k.succ) (qg (0 : Fin (4 : ℕ)))) → (
        let uR := ii ^ s.val *
          (if Even s.val then BandVectors.1 (r 0) (r i.succ)
            else BandVectors.1 (r i.succ) (r 0))
        let vR := ii ^ t.val *
          (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
            else BandVectors.1 (qg k.succ) (qg 0))
        BandPackingSymmetryTileAction g' (TileTranslation U uR) = TileTranslation U' vR) ) := by
  classical
  intro r i s U a g' p qg k t U' ii hdispR uR vR
  rw [(BandPackingSymmetryTilingTransport g').2.2.2.2.2.2.1]
  exact congrArg (TileTranslation U') hdispR

private theorem transL :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (a
            : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let U' := BandPackingSymmetryTileAction g' U
        let ii : GaussianInt := ⟨0, 1⟩
        (BandPackingSymmetryVectorAction g' (ii ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1
            (r i.succ) (r (0 : Fin (4 : ℕ))) else BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ))
            = ii ^ (↑t : ℕ) * if Even (↑t : ℕ) then BandVectors.1 (qg k.succ) (qg (0 : Fin (4 :
            ℕ))) else BandVectors.1 (qg (0 : Fin (4 : ℕ))) (qg k.succ)) → (
        let uL := ii ^ s.val *
          (if Even s.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))
        let vL := ii ^ t.val *
          (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
            else BandVectors.1 (qg 0) (qg k.succ))
        BandPackingSymmetryTileAction g' (TileTranslation U uL) = TileTranslation U' vL) ) := by
  classical
  intro r i s U a g' p qg k t U' ii hdispL uL vL
  rw [(BandPackingSymmetryTilingTransport g').2.2.2.2.2.2.1]
  exact congrArg (TileTranslation U') hdispL

private theorem hv :
    (by
      classical
      exact
        ∀ (g' : BandPackingSymmetry), ∀ (f : GaussianInt ≃ GaussianInt), ((f : GaussianInt →
            GaussianInt) = BandPackingSymmetryVectorAction g') → (∀ (T : ProtoTile),
            FootprintVertices (BandPackingSymmetryTileAction g' T) = f '' FootprintVertices T) )
            := by
  classical
  intro g' f hfun T
  simpa only [hfun] using (BandPackingSymmetryTilingTransport g').2.2.2.2.2.2.2.1 T

private theorem he :
    (by
      classical
      exact
        ∀ (g' : BandPackingSymmetry), ∀ (f : GaussianInt ≃ GaussianInt), ((f : GaussianInt →
            GaussianInt) = BandPackingSymmetryVectorAction g') → (∀ (T : ProtoTile),
            FootprintEdges (BandPackingSymmetryTileAction g' T) = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges T) ) := by
  classical
  intro g' f hfun T
  simpa only [hfun] using (BandPackingSymmetryTilingTransport g').2.2.2.2.2.2.2.2.1 T

private theorem hiv :
    (by
      classical
      exact
        ∀ (g' : BandPackingSymmetry), ∀ (f : GaussianInt ≃ GaussianInt), (∀ (T : ProtoTile),
            FootprintVertices (BandPackingSymmetryTileAction g' T) = f '' FootprintVertices T) →
            (∀ (T : ProtoTile), FootprintVertices T = f.symm '' FootprintVertices
            (BandPackingSymmetryTileAction g' T)) ) := by
  classical
  intro g' f hv T
  rw [hv]
  simp [Set.image_image]

private theorem hie :
    (by
      classical
      exact
        ∀ (g' : BandPackingSymmetry), ∀ (f : GaussianInt ≃ GaussianInt), (∀ (T : ProtoTile),
            FootprintEdges (BandPackingSymmetryTileAction g' T) = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges T) → (∀ (T : ProtoTile), FootprintEdges T = (fun e :
            Finset GaussianInt => e.image f.symm) '' FootprintEdges
            (BandPackingSymmetryTileAction g' T)) ) := by
  classical
  intro g' f he T
  rw [he]
  simp [Set.image_image, Finset.image_image]

private theorem hivR :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (a
            : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let U' := BandPackingSymmetryTileAction g' U
        let ii : GaussianInt := ⟨0, 1⟩
        let uR := ii ^ s.val *
          (if Even s.val then BandVectors.1 (r 0) (r i.succ)
            else BandVectors.1 (r i.succ) (r 0))
        let vR := ii ^ t.val *
          (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
            else BandVectors.1 (qg k.succ) (qg 0))
        (BandPackingSymmetryTileAction g' (TileTranslation U uR) = TileTranslation U' vR) → (∀ (f
            : GaussianInt ≃ GaussianInt), (∀ (T : ProtoTile), FootprintVertices T = f.symm ''
            FootprintVertices (BandPackingSymmetryTileAction g' T)) → (FootprintVertices
            (TileTranslation U uR) = f.symm '' FootprintVertices (TileTranslation U' vR))) ) := by
  classical
  intro r i s U a g' p qg k t U' ii uR vR transR f hiv
  rw [← transR]
  exact hiv _

private theorem hieR :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (a
            : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let U' := BandPackingSymmetryTileAction g' U
        let ii : GaussianInt := ⟨0, 1⟩
        let uR := ii ^ s.val *
          (if Even s.val then BandVectors.1 (r 0) (r i.succ)
            else BandVectors.1 (r i.succ) (r 0))
        let vR := ii ^ t.val *
          (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
            else BandVectors.1 (qg k.succ) (qg 0))
        (BandPackingSymmetryTileAction g' (TileTranslation U uR) = TileTranslation U' vR) → (∀ (f
            : GaussianInt ≃ GaussianInt), (∀ (T : ProtoTile), FootprintEdges T = (fun e : Finset
            GaussianInt => e.image f.symm) '' FootprintEdges (BandPackingSymmetryTileAction g'
            T)) → (FootprintEdges (TileTranslation U uR) = (fun e : Finset GaussianInt => e.image
            f.symm) '' FootprintEdges (TileTranslation U' vR))) ) := by
  classical
  intro r i s U a g' p qg k t U' ii uR vR transR f hie
  rw [← transR]
  exact hie _

private theorem hivL :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (a
            : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let U' := BandPackingSymmetryTileAction g' U
        let ii : GaussianInt := ⟨0, 1⟩
        let uL := ii ^ s.val *
          (if Even s.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))
        let vL := ii ^ t.val *
          (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
            else BandVectors.1 (qg 0) (qg k.succ))
        (BandPackingSymmetryTileAction g' (TileTranslation U uL) = TileTranslation U' vL) → (∀ (f
            : GaussianInt ≃ GaussianInt), (∀ (T : ProtoTile), FootprintVertices T = f.symm ''
            FootprintVertices (BandPackingSymmetryTileAction g' T)) → (FootprintVertices
            (TileTranslation U uL) = f.symm '' FootprintVertices (TileTranslation U' vL))) ) := by
  classical
  intro r i s U a g' p qg k t U' ii uL vL transL f hiv
  rw [← transL]
  exact hiv _

private theorem hieL :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (a
            : Fin (3 : ℕ)), ∀ (g' : BandPackingSymmetry),
        let p : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        let qg := BandPackingSymmetryQuadrupleAction g' p
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let U' := BandPackingSymmetryTileAction g' U
        let ii : GaussianInt := ⟨0, 1⟩
        let uL := ii ^ s.val *
          (if Even s.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))
        let vL := ii ^ t.val *
          (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
            else BandVectors.1 (qg 0) (qg k.succ))
        (BandPackingSymmetryTileAction g' (TileTranslation U uL) = TileTranslation U' vL) → (∀ (f
            : GaussianInt ≃ GaussianInt), (∀ (T : ProtoTile), FootprintEdges T = (fun e : Finset
            GaussianInt => e.image f.symm) '' FootprintEdges (BandPackingSymmetryTileAction g'
            T)) → (FootprintEdges (TileTranslation U uL) = (fun e : Finset GaussianInt => e.image
            f.symm) '' FootprintEdges (TileTranslation U' vL))) ) := by
  classical
  intro r i s U a g' p qg k t U' ii uL vL transL f hie
  rw [← transL]
  exact hie _

end OrientedEndpointGeometry

theorem BandOrientedChildParentEndpoints
    (r : Fin 4 → CircleCoordinates) (hproper : ProperBandQuadruple r)
    (i : Fin 3) (s : Fin 4) (U W Z : ProtoTile)
    (hU : BandPrototile (r 0) U)
    (hW : BandPrototile (r i.succ) W)
    (hZ : BandPrototile
      (r ((if Even s.val then i - 1 else i + 1).succ)) Z)
    (hUpos : 0 < (r 0).1) (hWpos : 0 < (r i.succ).1)
    (hZpos : 0 < (r ((if Even s.val then i - 1 else i + 1).succ)).1)
    (hWcent : TileCentroid W - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
            BandVectors.1 (r 0) (r i.succ))))
    (hZcent : TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then
            BandVectors.1 (r 0) (r ((i - 1).succ)) -
              BandVectors.1 (r ((i - 1).succ)) (r 0)
          else
            BandVectors.1 (r ((i + 1).succ)) (r 0) -
              BandVectors.1 (r 0) (r ((i + 1).succ))))) :
    let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (r 0) (r i.succ)
        else BandVectors.1 (r i.succ) (r 0))
    let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (r i.succ) (r 0)
        else BandVectors.1 (r 0) (r i.succ))
    ∃ rightData : ExactTileInterfaceTriple U (TileTranslation U uR) W,
      ∃ incomingData : ExactTileInterfaceTriple U (TileTranslation U uL) W,
        ∃ adjacentData : ExactTileInterfaceTriple U W Z,
          rightData.point ≠ incomingData.point ∧
          adjacentData.point = incomingData.point ∧
          rightData.otherCA = incomingData.point ∧
          incomingData.otherCA = rightData.point ∧
          adjacentData.otherAB = rightData.point := by
-- BODY
  classical
  obtain ⟨a, g, hregime⟩ := BandRegimeClassification r hproper
  obtain ⟨g', hquadg, hdata⟩ := P4055T1PlacementNormalization
    r hproper i s U W Z hU hW hZ hUpos hWpos hZpos hWcent hZcent a g
  let p : Fin 4 → CircleCoordinates :=
    ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
  let qg := BandPackingSymmetryQuadrupleAction g' p
  let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
    then -(i - a) else i - a
  let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
    then -s - 1 else s
  let j : Fin 3 := if Even t.val then k - 1 else k + 1
  let U' := BandPackingSymmetryTileAction g' U
  let W' := BandPackingSymmetryTileAction g' W
  let Z' := BandPackingSymmetryTileAction g' Z
  let ii : GaussianInt := ⟨0, 1⟩
  change
      ProperBandQuadruple qg ∧
      BandPrototile (qg 0) U' ∧ BandPrototile (qg k.succ) W' ∧
      BandPrototile (qg j.succ) Z' ∧
      0 < (qg 0).1 ∧ 0 < (qg k.succ).1 ∧ 0 < (qg j.succ).1 ∧
      TileCentroid W' - TileCentroid U' = (1 / 2 : Real) •
        GaussianRealPoint (ii ^ t.val *
          (BandVectors.1 (qg k.succ) (qg 0) + BandVectors.1 (qg 0) (qg k.succ))) ∧
      TileCentroid Z' - TileCentroid U' = (1 / 2 : Real) •
        GaussianRealPoint (ii ^ t.val * (if Even t.val then
          BandVectors.1 (qg 0) (qg j.succ) - BandVectors.1 (qg j.succ) (qg 0)
        else BandVectors.1 (qg j.succ) (qg 0) - BandVectors.1 (qg 0) (qg j.succ))) ∧
      BandPackingSymmetryVectorAction g'
        (ii ^ s.val * (if Even s.val then BandVectors.1 (r 0) (r i.succ)
          else BandVectors.1 (r i.succ) (r 0))) =
        ii ^ t.val * (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
          else BandVectors.1 (qg k.succ) (qg 0)) ∧
      BandPackingSymmetryVectorAction g'
        (ii ^ s.val * (if Even s.val then BandVectors.1 (r i.succ) (r 0)
          else BandVectors.1 (r 0) (r i.succ))) =
        ii ^ t.val * (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
          else BandVectors.1 (qg 0) (qg k.succ)) at hdata
  rcases hdata with ⟨hproperG, hU', hW', hZ', hUpos', hWpos', hZpos',
    hWcentNorm, hZcentNorm, hdispR, hdispL⟩
  have hregimeQ := hregime
  change Xor
      (∃ P, 1 < P.q ∧
        BandPackingSymmetryQuadrupleAction g p = FordRecursiveQuadruple P)
      (Xor
        (∃ K : DiamondParameter, 1 < K.1 ∧
          BandPackingSymmetryQuadrupleAction g p = DiamondRecursiveQuadruple K)
        (Nonempty (BandOrderedGeneralConfiguration
          (BandPackingSymmetryQuadrupleAction g p)))) at hregimeQ
  rw [← hquadg p] at hregimeQ
  have hregimeNormalized : Xor
      (∃ P, 1 < P.q ∧ qg = FordRecursiveQuadruple P)
      (Xor
        (∃ K : DiamondParameter, 1 < K.1 ∧ qg = DiamondRecursiveQuadruple K)
        (Nonempty (BandOrderedGeneralConfiguration qg))) :=
            OrientedEndpointGeometry.hregimeNormalized r a g' hregimeQ
  have normalized :
    let uR := (⟨0, 1⟩ : GaussianInt) ^ t.val *
      (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
        else BandVectors.1 (qg k.succ) (qg 0))
    let uL := (⟨0, 1⟩ : GaussianInt) ^ t.val *
      (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
        else BandVectors.1 (qg 0) (qg k.succ))
    ∃ rightData : ExactTileInterfaceTriple U' (TileTranslation U' uR) W',
      ∃ incomingData : ExactTileInterfaceTriple U' (TileTranslation U' uL) W',
        ∃ adjacentData : ExactTileInterfaceTriple U' W' Z',
          rightData.point ≠ incomingData.point ∧
          adjacentData.point = incomingData.point ∧
          rightData.otherCA = incomingData.point ∧
          incomingData.otherCA = rightData.point ∧
          adjacentData.otherAB = rightData.point := OrientedEndpointGeometry.normalized r i s U W
              Z a g' hproperG hU' hW' hZ' hUpos' hWpos' hZpos' hWcentNorm hZcentNorm
              hregimeNormalized
  rcases normalized with ⟨R, I, A, hne, hap, hrca, hica, haab⟩
  let uR := ii ^ s.val *
    (if Even s.val then BandVectors.1 (r 0) (r i.succ)
      else BandVectors.1 (r i.succ) (r 0))
  let uL := ii ^ s.val *
    (if Even s.val then BandVectors.1 (r i.succ) (r 0)
      else BandVectors.1 (r 0) (r i.succ))
  let vR := ii ^ t.val *
    (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
      else BandVectors.1 (qg k.succ) (qg 0))
  let vL := ii ^ t.val *
    (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
      else BandVectors.1 (qg 0) (qg k.succ))
  have transR : BandPackingSymmetryTileAction g' (TileTranslation U uR) =
      TileTranslation U' vR := OrientedEndpointGeometry.transR r i s U a g' hdispR
  have transL : BandPackingSymmetryTileAction g' (TileTranslation U uL) =
      TileTranslation U' vL := OrientedEndpointGeometry.transL r i s U a g' hdispL
  obtain ⟨f, hf, _, hi⟩ := P4055T1PackingGridEquivalence g'
  have hfun : (f : GaussianInt → GaussianInt) = BandPackingSymmetryVectorAction g' :=
    funext hf
  have hv (T : ProtoTile) :
      FootprintVertices (BandPackingSymmetryTileAction g' T) = f '' FootprintVertices T :=
          OrientedEndpointGeometry.hv g' f hfun T
  have he (T : ProtoTile) :
      FootprintEdges (BandPackingSymmetryTileAction g' T) =
        (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T :=
            OrientedEndpointGeometry.he g' f hfun T
  have hiv (T : ProtoTile) :
      FootprintVertices T = f.symm '' FootprintVertices (BandPackingSymmetryTileAction g' T) :=
          OrientedEndpointGeometry.hiv g' f hv T
  have hie (T : ProtoTile) :
      FootprintEdges T = (fun e : Finset GaussianInt => e.image f.symm) ''
        FootprintEdges (BandPackingSymmetryTileAction g' T) := OrientedEndpointGeometry.hie g' f
            he T
  have hivR : FootprintVertices (TileTranslation U uR) =
      f.symm '' FootprintVertices (TileTranslation U' vR) := OrientedEndpointGeometry.hivR r i s
          U a g' transR f hiv
  have hieR : FootprintEdges (TileTranslation U uR) =
      (fun e : Finset GaussianInt => e.image f.symm) '' FootprintEdges (TileTranslation U' vR) :=
          OrientedEndpointGeometry.hieR r i s U a g' transR f hie
  have hivL : FootprintVertices (TileTranslation U uL) =
      f.symm '' FootprintVertices (TileTranslation U' vL) := OrientedEndpointGeometry.hivL r i s
          U a g' transL f hiv
  have hieL : FootprintEdges (TileTranslation U uL) =
      (fun e : Finset GaussianInt => e.image f.symm) '' FootprintEdges (TileTranslation U' vL) :=
          OrientedEndpointGeometry.hieL r i s U a g' transL f hie
  obtain ⟨R₀, hrp, _, _, hrc⟩ := P4055T1ExactTripleImage f.symm f.symm.injective hi
    _ _ _ U (TileTranslation U uR) W
    (hiv U) hivR (hiv W) (hie U) hieR (hie W) R
  obtain ⟨I₀, hip, _, _, hic⟩ := P4055T1ExactTripleImage f.symm f.symm.injective hi
    _ _ _ U (TileTranslation U uL) W
    (hiv U) hivL (hiv W) (hie U) hieL (hie W) I
  obtain ⟨A₀, hpa, hab, _, _⟩ := P4055T1ExactTripleImage f.symm f.symm.injective hi
    _ _ _ U W Z
    (hiv U) (hiv W) (hiv Z) (hie U) (hie W) (hie Z) A
  refine ⟨R₀, I₀, A₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrp, hip]
    exact fun h => hne (f.symm.injective h)
  · rw [hpa, hip, hap]
  · rw [hrc, hip, hrca]
  · rw [hic, hrp, hica]
  · rw [hab, hrp, haab]

end ApollonianSuperharmonic

end
