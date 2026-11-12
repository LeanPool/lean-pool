/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandPrototileSingleton
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: PositiveCurvatureTileOdometerSupportTransport]

/-!
# PositiveCurvatureTileOdometerSupportTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PositiveCurvatureTileOdometerSupportTransport
    (C : CircleCoordinates) (T U : ProtoTile) (h : PartialOdometer)
    (hC : 0 < C.1) (hT : TileOdometer C T h)
    (hU : BandPrototile C U) (hcellsTU : T.cells = U.cells) :
    TileOdometer C U h := by
-- BODY
  classical
  have positive_cells : ∀ (D : CircleCoordinates) (V : ProtoTile),
      0 < D.1 → BandPrototile D V → V.cells.Nonempty := by
    intro D V hD hV
    induction hV with
    | line w x hw => simp at hD
    | unit z x anchor => simp
    | @decompose q hq S V hS hcells hfoot hcentroid ih =>
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
        exact ⟨x, (hcells x).mpr ⟨i, false, hx⟩⟩
  induction hT with
  | line w x hw h hdom =>
      simp at hC
  | unit z x V h hV hdom htrans =>
      have hUcells : U.cells = {x} := hcellsTU.symm.trans hV
      have hVne : V.cells.Nonempty := by rw [hV]; simp
      have hUne : U.cells.Nonempty := by rw [hUcells]; simp
      have hfoot : FootprintVertices V = FootprintVertices U := by
        simp only [FootprintVertices, ite_eq_left hVne, ite_eq_left hUne]
        rw [hcellsTU]
      exact TileOdometer.unit z x U h hUcells (hdom.trans hfoot) htrans
  | @decompose q hq S V hs h hV hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
      have hVne : V.cells.Nonempty := positive_cells (q 0) V hC hV
      have hUne : U.cells.Nonempty := by
        rw [← hcellsTU]
        exact hVne
      have hfoot_eq : FootprintVertices V = FootprintVertices U := by
        simp only [FootprintVertices, ite_eq_left hVne, ite_eq_left hUne]
        rw [hcellsTU]
      have hcent_eq : TileCentroid V = TileCentroid U := by
        simp only [TileCentroid, ite_eq_left hVne, ite_eq_left hUne]
        rw [hcellsTU]
      refine @TileOdometer.decompose q hq S U hs h hU hsub
        ?_ ?_ ?_ hdom hvalue hcompat hslope
      · intro x
        rw [← hcellsTU]
        exact hcells x
      · intro i s
        rw [← hfoot_eq]
        exact hfoot i s
      · intro i s
        rw [← hcent_eq]
        exact hcentroid i s

end ApollonianSuperharmonic

end
