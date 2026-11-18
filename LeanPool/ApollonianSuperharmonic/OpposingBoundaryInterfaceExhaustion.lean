/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.OpposingBoundaryOdometerStrings
public import LeanPool.ApollonianSuperharmonic.OpposingStringInterfacePath
public import LeanPool.ApollonianSuperharmonic.P4366T2OuterGeometry
public import LeanPool.ApollonianSuperharmonic.P4366T2WalkExhaustion
public import LeanPool.ApollonianSuperharmonic.P4366T2LocalSectors

-- [TABLET NODE: OpposingBoundaryInterfaceExhaustion]

/-!
# OpposingBoundaryInterfaceExhaustion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem OpposingBoundaryInterfaceExhaustion
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 Ci : BandCircle) (i : Fin 3)
    (hC0 : q 0 = C0.1.1) (hCi : q i.succ = Ci.1.1)
    (T0 T0' : ProtoTile) (h0 h0' : PartialOdometer)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T0)
    (hsym : QuarterTurnSymmetric T0)
    (hO0 : TileOdometer C0.1.1 T0 h0)
    (hO0' : TileOdometer C0.1.1 T0' h0')
    (hlarge : 1 < Ci.1.1.1)
    (p0 p0' : Real × Real)
    (hs0 : PartialOdometerSlope h0 = some p0)
    (hs0' : PartialOdometerSlope h0' = some p0')
    (hcentroid : TileCentroid T0' - TileCentroid T0 =
      GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (hslope : p0' - p0 =
      GaussianRealPoint (BandVectors.2 (q i.succ) (q 0))) :
    exists orientation : Bool, exists base Rminus Rplus : ProtoTile,
    exists tiles reverseTiles : List ProtoTile,
    exists hs reverseHs : List PartialOdometer,
    exists hminus hplus : PartialOdometer,
    exists pminus pplus : Real × Real,
    exists path : List GaussianInt,
      BoundaryString C0 Ci i orientation T0 base Rminus Rplus tiles /\
      TileString Ci orientation base Rplus Rminus reverseTiles /\
      OdometerStringRespect Ci orientation base Rminus Rplus tiles hs /\
      OdometerStringRespect Ci orientation base Rplus Rminus
        reverseTiles reverseHs /\
      hs.head? = some hminus /\ hs.getLast? = some hplus /\
      reverseHs.head? = some hplus /\ reverseHs.getLast? = some hminus /\
      TileOdometer Ci.1.1 Rminus hminus /\
      TileOdometer Ci.1.1 Rplus hplus /\
      PartialOdometerSlope hminus = some pminus /\
      PartialOdometerSlope hplus = some pplus /\
      pminus - p0 = (1 / 2 : Real) • GaussianRealPoint
        (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ)) /\
      pplus - p0 = (1 / 2 : Real) • GaussianRealPoint
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)) /\
      Nonempty (ExactTileInterfaceTriple T0 T0' Rminus) /\
      Nonempty (ExactTileInterfaceTriple T0 T0' Rplus) /\
      path.Nodup /\ 2 <= path.length /\
      (exists xminus,
        path.head? = some xminus /\ xminus ∈ FootprintVertices Rminus) /\
      (exists xplus,
        path.getLast? = some xplus /\ xplus ∈ FootprintVertices Rplus) /\
      FootprintVertices T0 ∩ FootprintVertices T0' =
        (path.toFinset : Set GaussianInt) /\
      (forall e, e ∈ FootprintEdges T0 ∩ FootprintEdges T0' <->
        exists x y : GaussianInt, exists l1 l2 : List GaussianInt,
          path = l1 ++ x :: y :: l2 /\ e = {x, y}) /\
      (forall x, x ∈ path ->
        (exists U g, U ∈ (tiles.drop 1).dropLast /\
          (U, g) ∈ tiles.zip hs /\
          x ∈ FootprintVertices U /\
          AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) /\
        (exists V k, V ∈ (reverseTiles.drop 1).dropLast /\
          (V, k) ∈ reverseTiles.zip reverseHs /\
          x ∈ FootprintVertices V /\
          AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0')) /\
      forall x y : GaussianInt, forall l1 l2 : List GaussianInt,
        path = l1 ++ x :: y :: l2 ->
          (exists U g, U ∈ (tiles.drop 1).dropLast /\
            (U, g) ∈ tiles.zip hs /\
            {x, y} ∈ FootprintEdges U /\
            AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) /\
          (exists V k, V ∈ (reverseTiles.drop 1).dropLast /\
            (V, k) ∈ reverseTiles.zip reverseHs /\
            {x, y} ∈ FootprintEdges V /\
            AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0') /\
      forall x, x ∈ path ->
        (forall y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ ->
          y ∈ h0.domain ∨ y ∈ h0'.domain) ->
        exists y : GaussianInt, exists U V : ProtoTile,
        exists g k : PartialOdometer,
          ((exists l1 l2 : List GaussianInt,
              path = l1 ++ x :: y :: l2) ∨
            (exists l1 l2 : List GaussianInt,
              path = l1 ++ y :: x :: l2)) /\
          U ≠ V /\
          {x, y} ∈ FootprintEdges U ∩ FootprintEdges V /\
          U ∈ (tiles.drop 1).dropLast /\
          (U, g) ∈ tiles.zip hs /\
          AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 /\
          V ∈ (reverseTiles.drop 1).dropLast /\
          (V, k) ∈ reverseTiles.zip reverseHs /\
          AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' /\
          ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨
            (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨
            (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨
            (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈ U.cells)) := by
-- BODY
  classical
  have hpositive : 0 < Ci.1.1.1 := by omega
  have hCpositive : 0 < C0.1.1.1 := by
    have hlt := cfg.proper.2 i
    rw [hC0, hCi] at hlt
    omega
  obtain ⟨orientation, centerShift, base, Rminus, Rplus, tiles, reverseTiles,
      hs, reverseHs, hminus, hplus, pminus, pplus, a, b, bminus, bplus,
      hboundary, hmc, hpc, hpairs, hreverse, hrespect, hreverseRespect,
      hheadHs, hlastHs, hheadReverseHs, hlastReverseHs, hOm, hOp,
      hsm, hsp, hpm, hpp, houterTransform, hplusTransform, hminusTransform,
      hforwardAnc, hreverseAnc⟩ :=
    OpposingBoundaryOdometerStrings q cfg.proper C0 Ci i hC0 hCi
      T0 T0' h0 h0' hO0 hO0' hpositive p0 p0' hs0 hs0' hcentroid hslope
  have hforward : TileString Ci orientation base Rminus Rplus tiles := by
    obtain ⟨q', hq', hq0', hqi', hband, ho, hf, hm, hp⟩ := hboundary
    exact hf
  obtain ⟨EM, EP, hbetween, hT, hT', hRm, hRp, hdis, hTm, hT'm,
      hTp, hT'p, hreg, hreg', hne, hnadj⟩ :=
    P4366T2OuterGeometry q cfg C0 Ci i hC0 hCi T0 T0' h0 h0'
      cert hsym hO0 hO0' hlarge hcentroid orientation base Rminus Rplus
      tiles centerShift hboundary hminus hplus hOm hOp hmc hpc
  have hnadj' : ¬ (if Ci.1.1.1 = 1 then
      ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
        TileCentroid Rplus - TileCentroid Rminus = GaussianRealPoint v
      else TileTouching Rminus Rplus) := by
    simpa only [ite_eq_right (show Ci.1.1.1 ≠ 1 by omega)] using hnadj
  obtain ⟨walk, ⟨wm, hwm, hwmR⟩, ⟨wp, hwp, hwpR⟩,
      hwalkSteps, hwalkVertices, hwalkEdges⟩ :=
    OpposingStringInterfacePath Ci orientation base Rminus Rplus hne hnadj'
      tiles reverseTiles hforward hreverse
  have vertexWitnesses : ∀ x, x ∈ walk →
      (∃ U g, U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
        x ∈ FootprintVertices U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) ∧
      (∃ V k, V ∈ (reverseTiles.drop 1).dropLast ∧
        (V, k) ∈ reverseTiles.zip reverseHs ∧ x ∈ FootprintVertices V ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0') := by
    intro x hx
    obtain ⟨⟨U, hU, hxU⟩, ⟨V, hV, hxV⟩⟩ := hwalkVertices x hx
    obtain ⟨g, hUg, hAg⟩ := hforwardAnc U hU
    obtain ⟨k, hVk, hAk⟩ := hreverseAnc V hV
    exact ⟨⟨U, g, hU, hUg, hxU, hAg⟩, ⟨V, k, hV, hVk, hxV, hAk⟩⟩
  have edgeWitnesses : ∀ x y : GaussianInt, ∀ l r : List GaussianInt,
      walk = l ++ x :: y :: r →
      (∃ U g, U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
        {x, y} ∈ FootprintEdges U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) ∧
      (∃ V k, V ∈ (reverseTiles.drop 1).dropLast ∧
        (V, k) ∈ reverseTiles.zip reverseHs ∧ {x, y} ∈ FootprintEdges V ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0') := by
    intro x y l r heq
    obtain ⟨⟨U, hU, heU⟩, ⟨V, hV, heV⟩⟩ := hwalkEdges x y l r heq
    obtain ⟨g, hUg, hAg⟩ := hforwardAnc U hU
    obtain ⟨k, hVk, hAk⟩ := hreverseAnc V hV
    exact ⟨⟨U, g, hU, hUg, heU, hAg⟩, ⟨V, k, hV, hVk, heV, hAk⟩⟩
  have ancestorVertex (U T : ProtoTile) (g h : PartialOdometer)
      (hA : AncestorOdometer Ci.1.1 C0.1.1 U T g h)
      (x : GaussianInt) (hx : x ∈ FootprintVertices U) :
      x ∈ FootprintVertices T := by
    have hg : x ∈ g.domain := by
      change x ∈ (g.domain : Set GaussianInt)
      rw [hA.2.2.1]
      exact hx
    have hh : x ∈ h.domain := hA.2.2.2.1 hg
    change x ∈ (h.domain : Set GaussianInt) at hh
    rwa [PositiveCurvatureTileOdometerDomain C0.1.1 T h hCpositive hA.1] at hh
  have ancestorEdge (U T : ProtoTile) (g h : PartialOdometer)
      (hA : AncestorOdometer Ci.1.1 C0.1.1 U T g h)
      (e : Finset GaussianInt) (he : e ∈ FootprintEdges U) :
      e ∈ FootprintEdges T := by
    obtain ⟨z, hz, hshape⟩ := he
    exact ⟨z, P4158T1AncestorCells Ci.1.1 C0.1.1 U T hA.2.1 hz, hshape⟩
  have walkContained : ∀ x, x ∈ walk →
      x ∈ FootprintVertices T0 ∩ FootprintVertices T0' := by
    intro x hx
    obtain ⟨⟨U, g, hU, hUg, hxU, hAg⟩, ⟨V, k, hV, hVk, hxV, hAk⟩⟩ :=
      vertexWitnesses x hx
    exact ⟨ancestorVertex U T0 g h0 hAg x hxU,
      ancestorVertex V T0' k h0' hAk x hxV⟩
  have wmEq : wm = EM.point :=
    (EM.unique_common wm).mp ⟨walkContained wm
      (List.mem_of_mem_head? (by simp [hwm])), hwmR⟩
  have wpEq : wp = EP.point :=
    (EP.unique_common wp).mp ⟨walkContained wp
      (List.mem_of_mem_getLast? (by simp [hwp])), hwpR⟩
  have walkEdgesContained : ∀ x y : GaussianInt, ∀ l r : List GaussianInt,
      walk = l ++ x :: y :: r →
      {x, y} ∈ FootprintEdges T0 ∩ FootprintEdges T0' := by
    intro x y l r heq
    obtain ⟨⟨U, g, hU, hUg, heU, hAg⟩, ⟨V, k, hV, hVk, heV, hAk⟩⟩ :=
      edgeWitnesses x y l r heq
    exact ⟨ancestorEdge U T0 g h0 hAg _ heU,
      ancestorEdge V T0' k h0' hAk _ heV⟩
  have exhausted := P4366T2WalkExhaustion hbetween walk
    (by simpa only [wmEq] using hwm) (by simpa only [wpEq] using hwp)
    walkEdgesContained
  obtain ⟨path, hp, hlen, hhead, hlast, hvertices, hsteps, hedges⟩ := hbetween
  have pathVertexWitnesses : ∀ x, x ∈ path →
      (∃ U g, U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
        x ∈ FootprintVertices U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) ∧
      (∃ V k, V ∈ (reverseTiles.drop 1).dropLast ∧
        (V, k) ∈ reverseTiles.zip reverseHs ∧ x ∈ FootprintVertices V ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0') := by
    intro x hx
    apply vertexWitnesses x
    apply exhausted.1 x
    rw [hvertices]
    simpa using hx
  have pathEdgeWitnesses : ∀ x y : GaussianInt, ∀ l r : List GaussianInt,
      path = l ++ x :: y :: r →
      (∃ U g, U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
        {x, y} ∈ FootprintEdges U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) ∧
      (∃ V k, V ∈ (reverseTiles.drop 1).dropLast ∧
        (V, k) ∈ reverseTiles.zip reverseHs ∧ {x, y} ∈ FootprintEdges V ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0') := by
    intro x y l r heq
    have he := (hedges {x, y}).mpr ⟨x, y, l, r, heq, rfl⟩
    obtain ⟨a, b, pre, post, hw, hedgeEq⟩ := exhausted.2 {x, y} he
    simpa only [← hedgeEq] using edgeWitnesses a b pre post hw
  have localSectors := P4366T2LocalSectors C0 Ci hlarge T0 T0' h0 h0'
    orientation base Rminus Rplus tiles reverseTiles hs reverseHs
    hforward hreverse EM EP hT hT' hRm hRp hdis hTm hT'm hTp hT'p
    hreg hreg' path ⟨hp, hlen, hhead, hlast, hvertices, hsteps, hedges⟩
    pathEdgeWitnesses
  refine ⟨orientation, base, Rminus, Rplus, tiles, reverseTiles, hs, reverseHs,
    hminus, hplus, pminus, pplus, path, hboundary, hreverse, hrespect,
    hreverseRespect, hheadHs, hlastHs, hheadReverseHs, hlastReverseHs,
    hOm, hOp, hsm, hsp, hpm, hpp, ⟨EM⟩, ⟨EP⟩, hp, hlen,
    ⟨EM.point, hhead, ((EM.unique_common EM.point).mpr rfl).2⟩,
    ⟨EP.point, hlast, ((EP.unique_common EP.point).mpr rfl).2⟩,
    hvertices, hedges, pathVertexWitnesses, ?_⟩
  intro x y l r heq
  refine ⟨(pathEdgeWitnesses x y l r heq).1,
    (pathEdgeWitnesses x y l r heq).2, ?_⟩
  intro z hz hstar
  apply localSectors z hz
  intro w hw
  have hcovered := hstar w hw
  change w ∈ (h0.domain : Set GaussianInt) ∨ w ∈ (h0'.domain : Set GaussianInt)
    at hcovered
  rwa [PositiveCurvatureTileOdometerDomain C0.1.1 T0 h0 hCpositive hO0,
    PositiveCurvatureTileOdometerDomain C0.1.1 T0' h0' hCpositive hO0'] at hcovered

end ApollonianSuperharmonic

end
