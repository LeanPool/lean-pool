/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentIncomingEndpoint
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryMarkedDataCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.BoundaryStringOdometerRespect
public import LeanPool.ApollonianSuperharmonic.BoundaryString
public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector
public import LeanPool.ApollonianSuperharmonic.CurvatureOneOdometer
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandPrototileSingleton
public import LeanPool.ApollonianSuperharmonic.DiamondCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.DiamondCellDomain
public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable
public import LeanPool.ApollonianSuperharmonic.DiamondOdometerExistsUnique
public import LeanPool.ApollonianSuperharmonic.DiamondOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.DiamondTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.DiamondTerminalWebStencilLedger
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceDisjointCompanionEndpoints
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.FordCellDomain
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.FordLaplacianTable
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordOdometerFamilyExistsUnique
public import LeanPool.ApollonianSuperharmonic.FordOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.FordOrientedChildParentRightEndpoint
public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse
public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.FordTileGeometry
public import LeanPool.ApollonianSuperharmonic.FordTerminalWebStencilLedger
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.LeftAdjacentOdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.MarkedOdometerAdjacencyReduction
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect
public import LeanPool.ApollonianSuperharmonic.OdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.OpposingBoundaryOdometerStrings
public import LeanPool.ApollonianSuperharmonic.OpposingStringInterfacePath
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.PartialOdometerHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionPaths
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.RightSubtileOdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileHalfTurn
public import LeanPool.ApollonianSuperharmonic.TileHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation
public import LeanPool.ApollonianSuperharmonic.VectorSquareProduct
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandCircleClassification
public import LeanPool.ApollonianSuperharmonic.P5570T1UnitNormalForm
public import LeanPool.ApollonianSuperharmonic.P5570T1UnitQuadratic
public import LeanPool.ApollonianSuperharmonic.CurvatureOnePeriodicOdometer
public import LeanPool.ApollonianSuperharmonic.BandPackingShiftPotential
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryGlobalOdometerTransport
public import LeanPool.ApollonianSuperharmonic.P3996T1AdjacentParentPlacement
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleRetargetMiddle
public import LeanPool.ApollonianSuperharmonic.P5589T1EndpointCompatibility
public import LeanPool.ApollonianSuperharmonic.P5589T1UnitInterfaceSelection
public import LeanPool.ApollonianSuperharmonic.P5589T1LinkedUnitValues
public import LeanPool.ApollonianSuperharmonic.P5596T1LeftWeb
public import LeanPool.ApollonianSuperharmonic.P5491T1ExceptionalPresentation
public import LeanPool.ApollonianSuperharmonic.P5606T1RightTerminalTransport
public import LeanPool.ApollonianSuperharmonic.P5606T1SubtileTerminalTransport

-- [TABLET NODE: OdometerWeb]

/-!
# OdometerWeb

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem OdometerWeb :
    (∀ (C : BandCircle) (T₁ T₂ : ProtoTile) (h₁ h₂ : PartialOdometer)
        (g : IntegerLatticeFunction) (x : GaussianInt),
      OdometerCompatibility h₁ h₂ →
      GlobalOdometerExtends g h₁ → GlobalOdometerExtends g h₂ →
      x ∈ h₁.domain → x ∈ h₂.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h₁.domain ∨ y ∈ h₂.domain) →
      (LeftLatticeAdjacent C T₁ T₂ h₁ h₂ →
        FourNeighborLaplacian g x = 1) ∧
      (RightLatticeAdjacent C T₁ T₂ h₁ h₂ →
        ((∀ s, s = x ∨ s = x - 1 ∨ s = x - ⟨0, 1⟩ ∨
              s = x - 1 - ⟨0, 1⟩ → s ∈ T₁.cells ∨ s ∈ T₂.cells) →
            FourNeighborLaplacian g x = 1) ∧
        (¬ (∀ s, s = x ∨ s = x - 1 ∨ s = x - ⟨0, 1⟩ ∨
              s = x - 1 - ⟨0, 1⟩ → s ∈ T₁.cells ∨ s ∈ T₂.cells) →
            FourNeighborLaplacian g x = 0))) ∧
    ∀ (C₀ Cᵢ : BandCircle) (q : Fin 4 → CircleCoordinates)
        (i : Fin 3) (s : Fin 4) (T₀ Tᵢ : ProtoTile)
        (h₀ hᵢ : PartialOdometer) (g : IntegerLatticeFunction)
        (x : GaussianInt) (p₀ pᵢ : ℝ × ℝ),
      ProperBandQuadruple q → q 0 = C₀.1.1 → q i.succ = Cᵢ.1.1 →
      PartialOdometerSlope h₀ = some p₀ →
      PartialOdometerSlope hᵢ = some pᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
             BandVectors.1 (q 0) (q i.succ))) →
      pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).1 →
      pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).2 →
      SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ →
      OdometerCompatibility h₀ hᵢ →
      GlobalOdometerExtends g h₀ → GlobalOdometerExtends g hᵢ →
      x ∈ h₀.domain → x ∈ hᵢ.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h₀.domain ∨ y ∈ hᵢ.domain) →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0))
      let UR := TileTranslation T₀ uR
      (x ∈ FootprintVertices UR → FourNeighborLaplacian g x = 0) ∧
      (x ∉ FootprintVertices UR → FourNeighborLaplacian g x = 1) := by
-- BODY
  classical
  have nonexceptional (q : Fin 4 → CircleCoordinates)
      (a : Fin 3) (w : BandPackingSymmetry)
      (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction w
        ![q 0, q a.succ, q (a+1).succ, q (a+2).succ])) :
      ¬ ((∃ (v : BandPackingSymmetry) (P : FordFareyParameter),
          BandPackingSymmetryCircleAction v (FordCircleCoordinate P.p P.q) = q 0) ∨
        (∃ (v : BandPackingSymmetry) (K : DiamondParameter),
          BandPackingSymmetryCircleAction v (DiamondRecursiveQuadruple K 0) = q 0)) := by
    have generalNotExceptional (R : Fin 4 → CircleCoordinates)
        (cfg : BandOrderedGeneralConfiguration R) :
        ¬ ((∃ (v : BandPackingSymmetry) (P : FordFareyParameter),
            BandPackingSymmetryCircleAction v (FordCircleCoordinate P.p P.q) = R 0) ∨
          (∃ (v : BandPackingSymmetry) (K : DiamondParameter),
            BandPackingSymmetryCircleAction v (DiamondRecursiveQuadruple K 0) = R 0)) := by
      intro he
      obtain ⟨v, hn⟩ := P5491T1ExceptionalPresentation R cfg.proper he
      let A := BandPackingSymmetryQuadrupleAction v R
      have hA := BandPackingSymmetryProperCovariance v R cfg.proper
      have parent (l : Fin 3) : (A l.succ).1 =
          (R (if BandPackingSymmetryReversesOrientation v then -l else l).succ).1 := by
        cases hv : BandPackingSymmetryReversesOrientation v <;> fin_cases l <;>
          simp [A, BandPackingSymmetryQuadrupleAction, hv,
            (BandPackingSymmetryCovariance v).1,
            show -(1 : Fin 3) = 2 from rfl, show -(2 : Fin 3) = 1 from rfl]
      rcases hn with ⟨P,hP,h0,_⟩ | ⟨K,hK,h0,_⟩
      · obtain ⟨b,hb,_⟩ := BandPredecessorNoCollision A (FordRecursiveQuadruple P)
          hA ((FordCoordinateConfiguration P).2 hP).1 h0
        have hz : (A ((2 : Fin 3)+b).succ).1 = 0 := by
          rw [← hb 2]
          simp [FordRecursiveQuadruple]
        rw [parent] at hz
        exact cfg.noLine _ hz
      · obtain ⟨b,hb,_⟩ := BandPredecessorNoCollision A (DiamondRecursiveQuadruple K)
          hA (DiamondCoordinateConfiguration K).2.1 h0
        have hunit (l : Fin 3) (hl : l = 0 ∨ l = 1) : (A (l+b).succ).1 = 1 := by
          rw [← hb l]
          rcases hl with rfl | rfl <;> simp [DiamondRecursiveQuadruple]
        have hu0 := hunit 0 (Or.inl rfl)
        have hu1 := hunit 1 (Or.inr rfl)
        rw [parent] at hu0 hu1
        have heq := cfg.atMostOneUnit _ _ hu0 hu1
        have heq' := Fin.succ_inj.mp heq
        cases hv : BandPackingSymmetryReversesOrientation v <;> simp [hv] at heq'
    intro he
    apply generalNotExceptional _ cfg
    rcases he with ⟨v,P,hv⟩ | ⟨v,K,hv⟩
    · exact Or.inl ⟨.comp w v,P,by
        change BandPackingSymmetryCircleAction w (BandPackingSymmetryCircleAction v _) =
          BandPackingSymmetryCircleAction w (q 0)
        rw [hv]⟩
    · exact Or.inr ⟨.comp w v,K,by
        change BandPackingSymmetryCircleAction w (BandPackingSymmetryCircleAction v _) =
          BandPackingSymmetryCircleAction w (q 0)
        rw [hv]⟩
  have restriction (C D : CircleCoordinates) (T U : ProtoTile)
      (h k : PartialOdometer) (g : IntegerLatticeFunction)
      (hsub : TileSubodometer C D T U h k) (hg : GlobalOdometerExtends g h) :
      GlobalOdometerExtends g k := by
    obtain ⟨c,hc⟩ := hg
    refine ⟨c, fun y hy => ?_⟩
    rw [hc y (hsub.2.2.2.1 hy), hsub.2.2.2.2.1 y hy]
  have compatible (g : IntegerLatticeFunction) (h k : PartialOdometer)
      (hg : GlobalOdometerExtends g h) (kg : GlobalOdometerExtends g k) :
      OdometerCompatibility h k := by
    obtain ⟨c,hc⟩ := hg
    obtain ⟨d,hd⟩ := kg
    right
    refine ⟨c-d, fun y hy ky => ?_⟩
    have hh := hc y hy
    have hk := hd y ky
    omega
  let R : ℕ → Prop := fun n =>
    ∀ (C : BandCircle) (T U : ProtoTile) (h k : PartialOdometer)
      (g : IntegerLatticeFunction) (x : GaussianInt),
    C.1.1.1.toNat + C.1.1.1.toNat = n →
    OdometerCompatibility h k →
    GlobalOdometerExtends g h → GlobalOdometerExtends g k →
    x ∈ h.domain → x ∈ k.domain →
    (∀ y, y = x ∨ y = x+1 ∨ y = x-1 ∨ y = x+⟨0,1⟩ ∨ y = x-⟨0,1⟩ →
      y ∈ h.domain ∨ y ∈ k.domain) →
    RightLatticeAdjacent C T U h k →
    ((∀ z, z = x ∨ z = x-1 ∨ z = x-⟨0,1⟩ ∨ z = x-1-⟨0,1⟩ →
      z ∈ T.cells ∨ z ∈ U.cells) → FourNeighborLaplacian g x = 1) ∧
    (¬ (∀ z, z = x ∨ z = x-1 ∨ z = x-⟨0,1⟩ ∨ z = x-1-⟨0,1⟩ →
      z ∈ T.cells ∨ z ∈ U.cells) → FourNeighborLaplacian g x = 0)
  let S : ℕ → Prop := fun n =>
    ∀ (C D : BandCircle) (q : Fin 4 → CircleCoordinates) (i : Fin 3) (s : Fin 4)
      (T U : ProtoTile) (h k : PartialOdometer) (g : IntegerLatticeFunction)
      (x : GaussianInt) (p p' : ℝ × ℝ),
    C.1.1.1.toNat + D.1.1.1.toNat = n →
    ProperBandQuadruple q → q 0 = C.1.1 → q i.succ = D.1.1 →
    PartialOdometerSlope h = some p → PartialOdometerSlope k = some p' →
    TileCentroid U - TileCentroid T = (1/2 : ℝ) • GaussianRealPoint
      ((⟨0,1⟩ : GaussianInt)^s.val *
        (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) →
    p'.1-p.1 = ((1/2 : ℝ) • GaussianRealPoint
      ((-⟨0,1⟩ : GaussianInt)^s.val *
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)))).1 →
    p'.2-p.2 = ((1/2 : ℝ) • GaussianRealPoint
      ((-⟨0,1⟩ : GaussianInt)^s.val *
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)))).2 →
    SubtileLatticeAdjacent C D T U h k → OdometerCompatibility h k →
    GlobalOdometerExtends g h → GlobalOdometerExtends g k →
    x ∈ h.domain → x ∈ k.domain →
    (∀ y, y = x ∨ y = x+1 ∨ y = x-1 ∨ y = x+⟨0,1⟩ ∨ y = x-⟨0,1⟩ →
      y ∈ h.domain ∨ y ∈ k.domain) →
    let UR := TileTranslation T ((⟨0,1⟩ : GaussianInt)^s.val *
      (if Even s.val then BandVectors.1 (q 0) (q i.succ)
        else BandVectors.1 (q i.succ) (q 0)))
    (x ∈ FootprintVertices UR → FourNeighborLaplacian g x = 0) ∧
    (x ∉ FootprintVertices UR → FourNeighborLaplacian g x = 1)
  have main : ∀ n, R n ∧ S n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      constructor
      · intro C T U h k g x hn hcompat hg kg hx kx hstar hright
        have horiginal := hright
        obtain ⟨hT,hU,p,p',hp,hp',q,i,e,hq,hq0,hc,hr,hi⟩ := hright
        obtain ⟨a,w,hregime⟩ := BandRegimeClassification q hq
        rcases hregime with ⟨hford,_⟩ | ⟨hrest,_⟩
        · exact P5606T1RightTerminalTransport q hq i e a w (Or.inl hford)
            T U h k p p' g x (by simpa only [hq0] using hT)
            (by simpa only [hq0] using hU) hp hp' hc hr hi hcompat hg kg hx kx hstar
        · rcases hrest with ⟨hdiamond,_⟩ | ⟨⟨cfg⟩,_⟩
          · exact P5606T1RightTerminalTransport q hq i e a w (Or.inr hdiamond)
              T U h k p p' g x (by simpa only [hq0] using hT)
              (by simpa only [hq0] using hU) hp hp' hc hr hi hcompat hg kg hx kx hstar
          · have hnot := nonexceptional q a w cfg
            rw [hq0] at hnot
            obtain ⟨D,V,f,b,b',r,j,t,hsub,hb,hb',hrproper,hr0,hrj,
                hcent,hsre,hsim,hadj,kx',fx,hcover,hdec,hmark⟩ :=
              MarkedOdometerAdjacencyReduction.1 C T U h k x hnot horiginal hx kx hstar
            have gf := restriction _ _ _ _ _ _ g hsub hg
            have hstep := (ih _ (by omega)).2 C D r j t U V k f g x b b' rfl
              hrproper hr0 hrj hb hb' hcent hsre hsim hadj
              (compatible g k f kg gf) kg gf kx' fx hcover
            exact ⟨fun H => hstep.2 (fun hm => (hmark.mpr hm) H),
              fun H => hstep.1 (hmark.mp H)⟩
      · intro C D q i s T U h k g x p p' hn hq hq0 hqi hp hp' hc hr hi
          hadj hcompat hg kg hx kx hstar
        obtain ⟨a,w,hregime⟩ := BandRegimeClassification q hq
        have hT : TileOdometer (q 0) T h := by simpa only [hq0] using hadj.1
        have hU : TileOdometer (q i.succ) U k := by simpa only [hqi] using hadj.2.1
        have hpos : 0 < (q i.succ).1 := by rw [hqi]; exact D.2
        rcases hregime with ⟨hford,_⟩ | ⟨hrest,_⟩
        · exact P5606T1SubtileTerminalTransport q hq i s hpos a w (Or.inl hford)
            T U h k p p' g x hT hU hp hp' hc hr hi hcompat hg kg hx kx hstar
        · rcases hrest with ⟨hdiamond,_⟩ | ⟨⟨cfg⟩,_⟩
          · exact P5606T1SubtileTerminalTransport q hq i s hpos a w (Or.inr hdiamond)
              T U h k p p' g x hT hU hp hp' hc hr hi hcompat hg kg hx kx hstar
          · have hnot := nonexceptional q a w cfg
            rw [hq0] at hnot
            obtain ⟨E,V,f,hsub,kx',fx,hcover,hdec,hcases⟩ :=
              MarkedOdometerAdjacencyReduction.2 C D q i s T U h k x p p'
                hnot hq hq0 hqi hp hp' hc hr hi hadj hx kx hstar
            have gf := restriction _ _ _ _ _ _ g hsub hg
            rcases hcases with ⟨_,hleft,hunmarked⟩ | hforward | hreverse
            · have hlap := P5596T1LeftWeb D U V k f g x
                (compatible g k f kg gf) kg gf kx' fx hcover hleft
              exact ⟨fun hm => (hunmarked hm).elim, fun _ => hlap⟩
            · obtain ⟨b,b',r,j,t,hb,hb',hrproper,hr0,hrj,hcent,hsre,hsim,
                hnew,hmark⟩ := hforward
              have hstep := (ih _ (by omega)).2 D E r j t U V k f g x b b' rfl
                hrproper hr0 hrj hb hb' hcent hsre hsim hnew
                (compatible g k f kg gf) kg gf kx' fx hcover
              exact ⟨fun hm => hstep.1 (hmark.mp hm),
                fun hm => hstep.2 (fun hnewmark => hm (hmark.mpr hnewmark))⟩
            · obtain ⟨b,b',r,j,t,hb,hb',hrproper,hr0,hrj,hcent,hsre,hsim,
                hnew,hmark⟩ := hreverse
              have hcover' : ∀ y, y = x ∨ y = x+1 ∨ y = x-1 ∨
                  y = x+⟨0,1⟩ ∨ y = x-⟨0,1⟩ → y ∈ f.domain ∨ y ∈ k.domain :=
                fun y hy => (hcover y hy).symm
              have hstep := (ih _ (by omega)).2 E D r j t V U f k g x b b' rfl
                hrproper hr0 hrj hb hb' hcent hsre hsim hnew
                (compatible g f k gf kg) gf kg fx kx' hcover'
              exact ⟨fun hm => hstep.1 (hmark.mp hm),
                fun hm => hstep.2 (fun hnewmark => hm (hmark.mpr hnewmark))⟩
  constructor
  · intro C T₁ T₂ h₁ h₂ g x hcompat hg₁ hg₂ hx₁ hx₂ hstar
    constructor
    · exact P5596T1LeftWeb C T₁ T₂ h₁ h₂ g x
        hcompat hg₁ hg₂ hx₁ hx₂ hstar
    · intro hright
      exact (main _).1 C T₁ T₂ h₁ h₂ g x rfl hcompat hg₁ hg₂ hx₁ hx₂ hstar hright
  · intro C D q i s T U h k g x p p' hq hq0 hqi hp hp' hc hr hi hadj hcompat
      hg kg hx kx hstar
    exact (main _).2 C D q i s T U h k g x p p' rfl hq hq0 hqi hp hp'
      hc hr hi hadj hcompat hg kg hx kx hstar

end ApollonianSuperharmonic

end
