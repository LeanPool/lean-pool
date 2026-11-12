/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileSubodometer
public import LeanPool.ApollonianSuperharmonic.BandCircle

-- [TABLET NODE: TileSubodometerLiteralDecompositionPiece]

/-!
# TileSubodometerLiteralDecompositionPiece

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileSubodometerLiteralDecompositionPiece
    (C C' : BandCircle) (T T' : ProtoTile) (h h' : PartialOdometer)
    (hC : 1 < C.1.1.1)
    (hsub : TileSubodometer C.1.1 C'.1.1 T T' h h') :
    ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
    ∃ S : Fin 3 → Bool → ProtoTile,
    ∃ hs : Fin 3 → Bool → PartialOdometer,
      ProperBandQuadruple q ∧ q 0 = C.1.1 ∧ q i.succ = C'.1.1 ∧
      BandPrototile (q 0) T ∧
      (∀ j t, TileOdometer (q j.succ) (S j t) (hs j t)) ∧
      (∀ x, x ∈ T.cells ↔ ∃ j t, x ∈ (S j t).cells) ∧
      (∀ j t, FootprintVertices (S j t) ⊆ FootprintVertices T) ∧
      (∀ j t,
        TileCentroid (S j t) - TileCentroid T =
          (if t = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (q ((j + 2).succ)) (q ((j + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((j + 2).succ))
                      (q ((j + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((j + 2).succ))
                      (q ((j + 1).succ)))).1)))) ∧
      (∀ x, x ∈ h.domain ↔ ∃ j t, x ∈ (hs j t).domain) ∧
      (∀ j t x, x ∈ (hs j t).domain → h.value x = (hs j t).value x) ∧
      (∀ j t k u, OdometerCompatibility (hs j t) (hs k u)) ∧
      (∀ j t, (q j.succ).1 = 0 ∨
        ∃ p p_j : Real × Real,
          PartialOdometerSlope h = some p ∧
          PartialOdometerSlope (hs j t) = some p_j ∧
          p_j.1 - p.1 =
            (if t = true then (1 : Real) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((j + 2).succ))
                (q ((j + 1).succ))).re : Int) -
               ((BandVectors.2 (q ((j + 2).succ))
                (q ((j + 1).succ))).im : Int)) ∧
          p_j.2 - p.2 =
            (if t = true then (1 : Real) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((j + 2).succ))
                (q ((j + 1).succ))).im : Int) +
               ((BandVectors.2 (q ((j + 2).succ))
                (q ((j + 1).succ))).re : Int))) ∧
      T'.cells = (S i s).cells ∧
      (h'.domain : Set GaussianInt) = (hs i s).domain ∧
      ∀ x, x ∈ h'.domain → h'.value x = (hs i s).value x := by
-- BODY
  rcases hsub with ⟨hO, hO', hfootSub, hdomSub, hvalSub,
    ⟨q, i, hq, hq0, hqi, s, hcentSub, hslopeSub⟩⟩
  have root : 1 < (q 0).1 := by simpa [hq0] using hC
  have hOq : TileOdometer (q 0) T h := by simpa [hq0] using hO
  obtain ⟨S, hs, hT, hOchild, hcells, hfoot, hcent, hdom, hvalue,
    hcompat, hslope⟩ :=
    TileOdometerReindexedDecomposition q hq T h root hOq
  have band_of_odo : ∀ (d : CircleCoordinates) (u : ProtoTile)
      k, TileOdometer d u k → BandPrototile d u := by
    intro d u k ho
    induction ho with
    | line w x hw k hdom => exact BandPrototile.line w x hw
    | unit z x u k hu hdom htrans =>
        cases u with
        | mk cells anchor =>
            simp_all only []
            exact BandPrototile.unit z x anchor
    | decompose hq hT hsub hcells hfoot hcent hdom hvalue hcompat hslope ih =>
        exact hT
  have nonempty_of_odo : ∀ (d : CircleCoordinates) (u : ProtoTile)
      k, 0 < d.1 → TileOdometer d u k → u.cells.Nonempty := by
    intro d u k hd ho
    induction ho with
    | line w x hw k hdom => simp at hd
    | unit z x u k hu hdom htrans => simp [hu]
    | @decompose r hr V U hV hsub hT hsubTiles hcells hfoot hcent hdom hvalue hcompat hslope ih =>
        have curvature_data := ProperBandCurvatureStructure r hr
        rcases curvature_data with ⟨hrootpos, hnonneg, hunique⟩
        have some_positive : ∃ j : Fin 3, 0 < (r j.succ).1 := by
          by_contra none
          have zeros : ∀ j : Fin 3, (r j.succ).1 = 0 := by
            intro j
            have non := hnonneg j
            have notpos : ¬ 0 < (r j.succ).1 := fun hp => none ⟨j, hp⟩
            omega
          have bad := hunique 0 1 (zeros 0) (zeros 1)
          omega
        rcases some_positive with ⟨j, hj⟩
        obtain ⟨x, hx⟩ := ih j false hj
        exact ⟨x, (hcells x).mpr ⟨j, false, hx⟩⟩
  have hbandT' : BandPrototile C'.1.1 T' := band_of_odo _ _ _ hO'
  have hbandS : BandPrototile C'.1.1 (S i s) := by
    rw [← hqi]
    exact band_of_odo _ _ _ (hOchild i s)
  have hcentEq : TileCentroid T' = TileCentroid (S i s) := by
    calc
      TileCentroid T' = (TileCentroid T' - TileCentroid T) + TileCentroid T := by abel
      _ = (TileCentroid (S i s) - TileCentroid T) + TileCentroid T := by
        rw [hcentSub, hcent i s]
      _ = TileCentroid (S i s) := by abel
  have hcellsEq : T'.cells = (S i s).cells :=
    (BandPrototileCentroidUnique C'.1.1 T' (S i s) hbandT' hbandS hcentEq).1
  have hOis : TileOdometer C'.1.1 (S i s) (hs i s) := by
    simpa [hqi] using hOchild i s
  have hdomT' := PositiveCurvatureTileOdometerDomain C'.1.1 T' h' C'.property hO'
  have hdomS := PositiveCurvatureTileOdometerDomain C'.1.1 (S i s) (hs i s)
    C'.property hOis
  have hneT' : T'.cells.Nonempty := nonempty_of_odo _ _ _ C'.property hO'
  have hneS : (S i s).cells.Nonempty := by rw [← hcellsEq]; exact hneT'
  have hfootEq : FootprintVertices T' = FootprintVertices (S i s) := by
    simp only [FootprintVertices, ite_eq_left hneT', ite_eq_left hneS]
    rw [hcellsEq]
  have hdomEq : (h'.domain : Set GaussianInt) = (hs i s).domain := by
    rw [hdomT', hdomS, hfootEq]
  refine ⟨q, i, s, S, hs, hq, hq0, hqi, hT, hOchild, hcells, hfoot,
    hcent, hdom, hvalue, hcompat, hslope, hcellsEq, hdomEq, ?_⟩
  intro x hx
  have hxhs : x ∈ (hs i s).domain := (Set.ext_iff.mp hdomEq x).mp hx
  exact (hvalSub x ((Set.ext_iff.mp hdomEq x).mpr hxhs)).symm.trans
    (hvalue i s x hxhs)

end ApollonianSuperharmonic

end
