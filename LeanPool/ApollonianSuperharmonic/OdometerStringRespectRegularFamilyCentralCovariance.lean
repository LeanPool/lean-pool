/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespectCentralCovariance
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure

-- [TABLET NODE: OdometerStringRespectRegularFamilyCentralCovariance]

/-!
# OdometerStringRespectRegularFamilyCentralCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem OdometerStringRespectRegularFamilyCentralCovariance
    (C : BandCircle) (orientation : Bool)
    (base R S : ProtoTile) (tiles reverseTiles : List ProtoTile)
    (hs gs : List PartialOdometer) (u a : GaussianInt)
    (hrespect : OdometerStringRespect C orientation base R S tiles hs)
    (hreverse : TileString C orientation base S R reverseTiles)
    (hcells : List.Forall₂
      (fun T U => (TileTranslation (TileHalfTurn T) u).cells = U.cells)
      tiles reverseTiles)
    (htransform : List.Forall₂ (fun h g => exists b : Int,
      g = PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b)
      hs gs) :
    OdometerStringRespect C orientation base S R reverseTiles gs := by
-- BODY
  classical
  have desiredString := hreverse
  rcases hreverse with ⟨hbase, hhead, hlast, hpair, hmem, hchain, hheight⟩
  have positive_cells : ∀ (D : CircleCoordinates) (W : ProtoTile),
      0 < D.1 → BandPrototile D W → W.cells.Nonempty := by
    intro D W hD hW
    induction hW with
    | line w x hw => simp at hD
    | unit z x => simp
    | @decompose q hq S W hS hcells' hfoot hcentroid ih =>
        have facts := ProperBandCurvatureStructure q hq
        have hp : ∃ i : Fin 3, 0 < (q i.succ).1 := by
          by_cases h0 : 0 < (q (0 : Fin 3).succ).1
          · exact ⟨0, h0⟩
          by_cases h1 : 0 < (q (1 : Fin 3).succ).1
          · exact ⟨1, h1⟩
          by_cases h2 : 0 < (q (2 : Fin 3).succ).1
          · exact ⟨2, h2⟩
          have n0 := facts.2.1 (0 : Fin 3)
          have n1 := facts.2.1 (1 : Fin 3)
          have z0 : (q (0 : Fin 3).succ).1 = 0 := by omega
          have z1 : (q (1 : Fin 3).succ).1 = 0 := by omega
          exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim
        rcases hp with ⟨i, hi⟩
        rcases ih i false hi with ⟨x, hx⟩
        exact ⟨x, (hcells' x).mpr ⟨i, false, hx⟩⟩
  have band_of_member : ∀ {W : ProtoTile},
      W ∈ RegularTileFamily base (TilingLattice C) → BandPrototile C.1.1 W := by
    intro W hW
    rcases hW with ⟨v, hv, rfl⟩
    exact BandPrototileTranslation C.1.1 base v hbase
  have centroid_cells : ∀ {V W : ProtoTile},
      V.cells.Nonempty → BandPrototile C.1.1 W →
      V.cells = W.cells → TileCentroid V = TileCentroid W := by
    intro V W hpV hW heq
    have hpW := positive_cells C.1.1 W (by exact C.property) hW
    simp only [TileCentroid, ite_eq_left hpV, ite_eq_left hpW]
    rw [heq]
  have raw := OdometerStringRespectCentralCovariance C orientation base R S
    tiles hs gs u a hrespect htransform
  rcases raw with ⟨rawString, rawTiles, rawChain⟩
  rcases hrespect with ⟨originalString, originalTiles, originalChain⟩
  rcases originalString with ⟨hbase0, hhead0, hlast0, hpair0, hmem0, hchain0, hheight0⟩
  have source_band : ∀ {T : ProtoTile}, T ∈ tiles → BandPrototile C.1.1 T := by
    intro T hT
    exact band_of_member (hmem0 T hT)
  have transportAdjacent : ∀ {T T' U U' : ProtoTile} {g g' : PartialOdometer},
      (TileTranslation (TileHalfTurn T) u).cells = U.cells →
      (TileTranslation (TileHalfTurn T') u).cells = U'.cells →
      T ∈ tiles → T' ∈ tiles →
      U ∈ reverseTiles → U' ∈ reverseTiles →
      LeftLatticeAdjacent C
        (TileTranslation (TileHalfTurn T) u)
        (TileTranslation (TileHalfTurn T') u) g g' →
      LeftLatticeAdjacent C U U' g g' := by
    intro T T' U U' g g' heq heq' hT hT' hUmem hU'mem hadj
    rcases hadj with ⟨hodo, hodo', ⟨p, p', hp, hp', hshape⟩⟩
    have hU := band_of_member (hmem U hUmem)
    have hU' := band_of_member (hmem U' hU'mem)
    have hnew := PositiveCurvatureTileOdometerSupportTransport C.1.1 _ U _
      C.property hodo hU heq
    have hnew' := PositiveCurvatureTileOdometerSupportTransport C.1.1 _ U' _
      C.property hodo' hU' heq'
    have hc := centroid_cells (V := TileTranslation (TileHalfTurn T) u)
      (by rw [heq]; exact positive_cells C.1.1 U C.property hU) hU heq
    have hc' := centroid_cells (V := TileTranslation (TileHalfTurn T') u)
      (by rw [heq']; exact positive_cells C.1.1 U' C.property hU') hU' heq'
    refine ⟨hnew, hnew', ⟨p, p', hp, hp', ?_⟩⟩
    rcases hshape with hunit | hnon
    · left
      rcases hunit with ⟨hor, orig, v, hv, hct, hx, hy⟩
      refine ⟨hor, orig, v, hv, ?_, hx, hy⟩
      simpa [hc, hc'] using hct
    · right
      rcases hnon with ⟨q, i, e, hq, hq0, hct, hx, hy⟩
      refine ⟨q, i, e, hq, hq0, ?_, hx, hy⟩
      simpa [hc, hc'] using hct
  have tileTransport : ∀ {ts us : List ProtoTile} {fs : List PartialOdometer},
      List.Forall₂ (fun T U =>
        (TileTranslation (TileHalfTurn T) u).cells = U.cells) ts us →
      List.Forall₂ (fun T h => TileOdometer C.1.1 T h)
        (ts.map (fun T => TileTranslation (TileHalfTurn T) u)) fs →
      (∀ U, U ∈ us → U ∈ RegularTileFamily base (TilingLattice C)) →
      List.Forall₂ (fun T h => TileOdometer C.1.1 T h) us fs := by
    intro ts us fs hc ho hm
    induction hc generalizing fs with
    | nil => cases ho; exact .nil
    | @cons T U ts us heq rest ih =>
        cases ho with
        | cons hodo hrest =>
            exact .cons
              (PositiveCurvatureTileOdometerSupportTransport C.1.1 _ U _
                C.property hodo (band_of_member (hm U (by simp))) heq)
              (ih hrest (fun V hV => hm V (by simp [hV])))
  have targetTiles := tileTransport hcells rawTiles (by
    intro U hU
    exact hmem U hU)
  have chainTransport : ∀ {ts us : List ProtoTile} {fs : List PartialOdometer},
      List.Forall₂ (fun T U =>
        (TileTranslation (TileHalfTurn T) u).cells = U.cells) ts us →
      (∀ T ∈ ts, T ∈ tiles) →
      (∀ U ∈ us, U ∈ reverseTiles) →
      List.Forall₂ (fun T h => TileOdometer C.1.1 T h)
        (ts.map (fun T => TileTranslation (TileHalfTurn T) u)) fs →
      List.Forall₂ (fun T h => TileOdometer C.1.1 T h) us fs →
      List.IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
        ((ts.map (fun T => TileTranslation (TileHalfTurn T) u)).zip fs) →
      List.IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)
        (us.zip fs) := by
    intro ts us fs hc hms hmu hraw htar hchain
    induction hc generalizing fs with
    | nil => cases hraw; cases htar; exact .nil
    | @cons T U ts us heq rest ih =>
        cases hraw with
        | cons hrawT hrawRest =>
          cases htar with
          | cons htarU htarRest =>
            cases ts with
            | nil =>
              cases hrawRest
              cases htarRest
              cases hchain
              exact .singleton _
            | cons T' ts' =>
              cases us with
                | nil => cases rest
                | cons U' us' =>
                cases rest with
                | cons heq' rest' =>
                  cases hrawRest with
                  | cons hrawNext hrawTail =>
                    cases htarRest with
                    | cons htarNext htarTail =>
                      cases hchain with
                      | cons_cons hadj htail =>
                        exact .cons_cons
                          (transportAdjacent heq heq'
                            (hms T (by simp)) (hms T' (by simp))
                            (hmu U (by simp)) (hmu U' (by simp)) hadj)
                          (ih (fs := _)
                            (fun V hV => hms V (by simp [hV]))
                            (fun V hV => hmu V (by simp [hV]))
                            (List.Forall₂.cons hrawNext hrawTail)
                            (List.Forall₂.cons htarNext htarTail) htail)
  have finalChain := chainTransport hcells
    (by intro T hT; exact hT) (by intro U hU; exact hU)
    rawTiles targetTiles rawChain
  exact ⟨desiredString, targetTiles, finalChain⟩

end ApollonianSuperharmonic

end
