/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer

-- [TABLET NODE: AncestorOdometerInnerSupportNormalization]

/-!
# AncestorOdometerInnerSupportNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem AncestorOdometerInnerSupportNormalization
    (C C' : CircleCoordinates) (V U T : ProtoTile)
    (h g : PartialOdometer)
    (hpositive : 0 < C.1) (hstrict : C.1 < C'.1)
    (hancestor : AncestorOdometer C C' V T h g)
    (hU : BandPrototile C U) (hcells : V.cells = U.cells) :
    AncestorOdometer C C' U T h g := by
-- BODY
  classical
  rcases hancestor with ⟨hO, hAT, hfoot, hsub, hval⟩
  have positive_cells := BandPrototileNonempty.positive
  have hUne : U.cells.Nonempty := positive_cells C U hpositive hU
  have hVne : V.cells.Nonempty := by rw [hcells]; exact hUne
  have hfoot_eq : FootprintVertices V = FootprintVertices U := by
    simp only [FootprintVertices, ite_eq_left hVne, ite_eq_left hUne]
    rw [hcells]
  have hcent_eq : TileCentroid V = TileCentroid U := by
    simp only [TileCentroid, ite_eq_left hVne, ite_eq_left hUne]
    rw [hcells]
  change Relation.ReflTransGen
      (fun X Y : CircleCoordinates × ProtoTile =>
        ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
          ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
          BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
          FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
          TileCentroid X.2 - TileCentroid Y.2 =
            (if s = true then (1 : Real) else -1) •
              ((1 / 2 : Real) •
                (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                  (-((GaussianRealPoint
                      (BandVectors.1 (q ((i + 2).succ))
                        (q ((i + 1).succ)))).2),
                    (GaussianRealPoint
                      (BandVectors.1 (q ((i + 2).succ))
                        (q ((i + 1).succ)))).1))))
      (C, V) (C', T) at hAT
  rcases Relation.ReflTransGen.cases_head hAT with same | ⟨M, first, rest⟩
  · have coordinates : C = C' := congrArg (fun z : CircleCoordinates × ProtoTile => z.1) same
    exact ((lt_irrefl C'.1) (coordinates ▸ hstrict)).elim
  · rcases first with ⟨q, i, s, hq, hq0, hqi, hY, hX, hinc, hcent⟩
    refine ⟨hO, ?_, ?_, hsub, hval⟩
    · exact rest.head ⟨q, i, s, hq, hq0, hqi, hY, hU, hfoot_eq ▸ hinc,
        hcent_eq ▸ hcent⟩
    exact hfoot_eq ▸ hfoot

end ApollonianSuperharmonic

end
