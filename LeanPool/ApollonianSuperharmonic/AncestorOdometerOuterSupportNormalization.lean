/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport

-- [TABLET NODE: AncestorOdometerOuterSupportNormalization]

/-!
# AncestorOdometerOuterSupportNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem AncestorOdometerOuterSupportNormalization
    (C C' : CircleCoordinates) (T V U : ProtoTile)
    (h g : PartialOdometer)
    (hpositive : 0 < C'.1) (hstrict : C.1 < C'.1)
    (hancestor : AncestorOdometer C C' T V h g)
    (hU : BandPrototile C' U) (hcells : V.cells = U.cells) :
    AncestorOdometer C C' T U h g := by
-- BODY
  classical
  rcases hancestor with ⟨hodo, hAT, hdom, hsub, hval⟩
  have hnewodo := PositiveCurvatureTileOdometerSupportTransport C' V U g
    hpositive hodo hU hcells
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
  have hVne : V.cells.Nonempty := by
    have hu : U.cells.Nonempty := positive_cells C' U hpositive hU
    rw [hcells]
    exact hu
  have hfoot_eq : FootprintVertices V = FootprintVertices U := by
    simp only [FootprintVertices, ite_eq_left hVne, ite_eq_left (positive_cells C' U hpositive hU)]
    rw [hcells]
  have hcent_eq : TileCentroid V = TileCentroid U := by
    simp only [TileCentroid, ite_eq_left hVne, ite_eq_left (positive_cells C' U hpositive hU)]
    rw [hcells]
  have hATU : AncestorTile C C' T U := by
    unfold AncestorTile at hAT ⊢
    rcases Relation.ReflTransGen.cases_tail hAT with heq | ⟨D, hchain, hedge⟩
    · have hc : C' = C := congrArg (fun z : CircleCoordinates × ProtoTile => z.1) heq
      have hc1 : C'.1 = C.1 := congrArg (fun z : CircleCoordinates => z.1) hc
      exact (lt_irrefl _ (hc1 ▸ hstrict)).elim
    · rcases hedge with ⟨q, i, s, hq, hq0, hqi, hDV, hD, hfoot, hcent⟩
      apply Relation.ReflTransGen.tail hchain
      refine ⟨q, i, s, hq, hq0, hqi, hU, hD, ?_, ?_⟩
      · rw [← hfoot_eq]
        exact hfoot
      · rw [← hcent_eq]
        exact hcent
  exact ⟨hnewodo, hATU, hdom, hsub, hval⟩

end ApollonianSuperharmonic

end
