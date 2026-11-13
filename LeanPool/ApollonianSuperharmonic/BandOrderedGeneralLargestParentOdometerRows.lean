/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.BandOdometerParentCentroids

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorWebRow
public import LeanPool.ApollonianSuperharmonic.OdometerWeb

-- [TABLET NODE: BandOrderedGeneralLargestParentOdometerRows]

/-!
# BandOrderedGeneralLargestParentOdometerRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LargestParentOdometerGeometry

private theorem firstRotateV :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) - I * BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) ) := by
  classical
  intro q cfg I
  simpa [I] using
    (VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.1

private theorem firstRotateA :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) + I * BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) ) := by
  classical
  intro q cfg I
  simpa [I] using
    (VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.2.1

private theorem v21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) - I * BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2)) → (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) ) := by
  classical
  intro q cfg I U W firstRotateV
  rw [cfg.firstParentThree] at firstRotateV
  rw [cfg.firstParentTwo, cfg.firstChild] at firstRotateV
  rw [cfg.firstParentTwo]
  dsimp [U, W] at firstRotateV ⊢
  linear_combination -firstRotateV

private theorem a21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) + I * BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2)) → (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) ) := by
  classical
  intro q cfg I A B firstRotateA
  rw [cfg.firstParentTwo, cfg.firstChild] at firstRotateA
  rw [cfg.firstParentThree] at firstRotateA
  rw [cfg.firstParentTwo]
  dsimp [A, B] at firstRotateA ⊢
  linear_combination -firstRotateA

private theorem v13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) →
            (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -U - (1 + I) * W)
            ) := by
  classical
  intro q cfg I U W v21
  have hsum := (VectorRecursionLaws cfg.firstPredecessor
    cfg.firstProper.1).1
  rw [cfg.firstParentThree, cfg.firstParentTwo] at hsum
  have v21q := v21
  rw [cfg.firstParentTwo] at v21q
  rw [v21q] at hsum
  rw [cfg.firstParentThree]
  dsimp [U, W, I]
  linear_combination hsum

private theorem a13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) →
            (BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -A - (1 - I) * B)
            ) := by
  classical
  intro q cfg I A B a21
  have hsum := (VectorRecursionLaws cfg.firstPredecessor
    cfg.firstProper.1).2.1
  rw [cfg.firstParentThree, cfg.firstParentTwo] at hsum
  have a21q := a21
  rw [cfg.firstParentTwo] at a21q
  rw [a21q] at hsum
  rw [cfg.firstParentThree]
  dsimp [A, B, I]
  linear_combination hsum

private theorem centroidAlgebra :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (-cOff W - cOff (U + I * W)) - (cOff W + cOff (-U - (1 + I) * W)) = (1 / 2 : Real) •
            GaussianRealPoint (I * (W + I * W)) ∧ (cOff W + cOff (U + I * W)) - (-cOff W - cOff
            (-U - (1 + I) * W)) = (1 / 2 : Real) • GaussianRealPoint ((I : GaussianInt) ^ (3 :
            Nat) * (W + I * W)) ∧ cOff W + cOff (-U - (1 + I) * W) + GaussianRealPoint (I * W) =
            cOff (-U - W) ∧ -cOff W - cOff (-U - (1 + I) * W) + GaussianRealPoint ((I :
            GaussianInt) ^ (3 : Nat) * W) = -cOff (-U - W) ) := by
  classical
  intro q cOff I U W
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Prod.ext <;>
    norm_num [cOff, GaussianRealPoint, I, Prod.smul_mk,
      Prod.add_def, Prod.sub_def, pow_succ] <;> ring

private theorem slopeAlgebra :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (-sOff B - sOff (A - I * B)) - (sOff B + sOff (-A - (1 - I) * B)) = (1 / 2 : Real) •
            GaussianRealPoint (-I * (B - I * B)) ∧ (sOff B + sOff (A - I * B)) - (-sOff B - sOff
            (-A - (1 - I) * B)) = (1 / 2 : Real) • GaussianRealPoint ((-I : GaussianInt) ^ (3 :
            Nat) * (B - I * B)) ) := by
  classical
  intro q sOff I A B
  refine ⟨?_, ?_⟩ <;> apply Prod.ext <;>
    norm_num [sOff, GaussianRealPoint, I, Prod.smul_mk,
      Prod.add_def, Prod.sub_def, pow_succ] <;> ring

private theorem hpos2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 2).1) )
            := by
  classical
  intro q cfg
  have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 1
  have hnonneg' : 0 ≤ (q 2).1 := by simpa using hnonneg
  have hne : (q 2).1 ≠ 0 := cfg.noLine 2
  omega

private theorem hpos3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 3).1) )
            := by
  classical
  intro q cfg
  have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 2
  have hnonneg' : 0 ≤ (q 3).1 := by simpa using hnonneg
  have hne : (q 3).1 ≠ 0 := cfg.noLine 3
  omega

private theorem hQleafAt284 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (TileCentroid (Q 1 true) - TileCentroid (P 0 true)
            = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3)) - (-((GaussianRealPoint (BandVectors.1
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))).2), (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))).1))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  simpa [Fin.add_def] using data.hQcent 1 true

private theorem hSleafAt293 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (TileCentroid (S 2 false) - TileCentroid (P 0
            false) = -((1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor
            2) (cfg.firstPredecessor 1)) - (-((GaussianRealPoint (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))).2), (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))).1)))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  simpa [Fin.add_def] using data.hScent 2 false

private theorem hQleafOffAt302 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (P :
            Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (Q 1 true) - TileCentroid (P 0 true) = (1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)) -
            (-((GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor
            3))).2), (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3))).1))) → (TileCentroid (Q 1 true) - TileCentroid (P 0 true)
            = cOff (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) ) := by
  classical
  intro q cfg P Q cOff hQleaf
  simpa [cOff] using hQleaf

private theorem hSleafOffAt305 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (P :
            Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (S 2 false) - TileCentroid (P 0 false) = -((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))
            - (-((GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor
            1))).2), (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1))).1)))) → (TileCentroid (S 2 false) - TileCentroid (P 0
            false) = -cOff (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))) )
            := by
  classical
  intro q cfg P S cOff hSleaf
  simpa [cOff] using hSleaf

private theorem hcentdiffAt312 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀
            (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) →
            ((BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -U - (1 + I) * W)
            → (((-cOff W - cOff (U + I * W)) - (cOff W + cOff (-U - (1 + I) * W)) = (1 / 2 :
            Real) • GaussianRealPoint (I * (W + I * W)) ∧ (cOff W + cOff (U + I * W)) - (-cOff W
            - cOff (-U - (1 + I) * W)) = (1 / 2 : Real) • GaussianRealPoint ((I : GaussianInt) ^
            (3 : Nat) * (W + I * W)) ∧ cOff W + cOff (-U - (1 + I) * W) + GaussianRealPoint (I *
            W) = cOff (-U - W) ∧ -cOff W - cOff (-U - (1 + I) * W) + GaussianRealPoint ((I :
            GaussianInt) ^ (3 : Nat) * W) = -cOff (-U - W)) → ((TileCentroid (Q 1 true) -
            TileCentroid (P 0 true) = cOff (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3))) → ((TileCentroid (S 2 false) - TileCentroid (P 0 false) =
            -cOff (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))) →
            ((TileCentroid (P 0 true) - TileCentroid T = cOff W) → ((TileCentroid (P 0 false) -
            TileCentroid T = -cOff W) → (TileCentroid (S 2 false) - TileCentroid (Q 1 true) = (1
            / 2 : Real) • GaussianRealPoint (I * (W + I * W))))))))) ) := by
  classical
  intro q cfg T P Q S cOff I U W v21 v13 centroidAlgebra hQleafOff hSleafOff hPplus hPminus
  calc
    _ = (TileCentroid (S 2 false) - TileCentroid (P 0 false)) +
          (TileCentroid (P 0 false) - TileCentroid T) -
          (TileCentroid (Q 1 true) - TileCentroid (P 0 true)) -
          (TileCentroid (P 0 true) - TileCentroid T) := by
      ext <;> dsimp <;> ring
    _ = (-cOff W - cOff (U + I * W)) -
          (cOff W + cOff (-U - (1 + I) * W)) := by
      rw [hSleafOff, hPminus, hQleafOff, hPplus, v21, v13]
      ext <;> dsimp [cOff] <;> ring
    _ = (1 / 2 : Real) • GaussianRealPoint (I * (W + I * W)) :=
      centroidAlgebra.1

private theorem hQpackAt326 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∃ p pQ : Real × Real, PartialOdometerSlope (r 0
            true) = some p ∧ PartialOdometerSlope (u 1 true) = some pQ ∧ pQ.1 - p.1 = (1 / 2) *
            (((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)).re : Int) -
            ((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)).im : Int)) ∧ pQ.2
            - p.2 = (1 / 2) * (((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor
            3)).im : Int) + ((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)).re
            : Int))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  rcases data.hQslope 1 true with hzero | hgood
  · have hbad : (q 2).1 = 0 := by
      rw [← cfg.firstParentTwo]
      exact hzero
    exact False.elim ((cfg.noLine 2) hbad)
  · simpa [Fin.add_def] using hgood

private theorem hSpackAt345 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∃ p pS : Real × Real, PartialOdometerSlope (r 0
            false) = some p ∧ PartialOdometerSlope (v 2 false) = some pS ∧ pS.1 - p.1 = -(1 / 2)
            * (((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)).re : Int) -
            ((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)).im : Int)) ∧ pS.2
            - p.2 = -(1 / 2) * (((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor
            1)).im : Int) + ((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)).re
            : Int))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  rcases data.hSslope 2 false with hzero | hgood
  · have hbad : (q 3).1 = 0 := by
      rw [← cfg.firstParentThree]
      exact hzero
    exact False.elim ((cfg.noLine 3) hbad)
  · simpa [Fin.add_def] using hgood

private theorem hPplusPackAt364 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∃ p pP : Real × Real, PartialOdometerSlope h = some p ∧ PartialOdometerSlope (r 0 true) =
            some pP ∧ pP.1 - p.1 = (1 / 2) * (((B.re : Int) : Real) - ((B.im : Int) : Real)) ∧
            pP.2 - p.2 = (1 / 2) * (((B.im : Int) : Real) + ((B.re : Int) : Real))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data B
  rcases data.hPslope 0 true with hzero | hgood
  · have hbad : (q 1).1 = 0 := by simpa using hzero
    exact False.elim ((cfg.noLine 1) hbad)
  · simpa [Fin.add_def, B] using hgood

private theorem hPminusPackAt375 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∃ p pP : Real × Real, PartialOdometerSlope h = some p ∧ PartialOdometerSlope (r 0 false)
            = some pP ∧ pP.1 - p.1 = -(1 / 2) * (((B.re : Int) : Real) - ((B.im : Int) : Real)) ∧
            pP.2 - p.2 = -(1 / 2) * (((B.im : Int) : Real) + ((B.re : Int) : Real))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data B
  rcases data.hPslope 0 false with hzero | hgood
  · have hbad : (q 1).1 = 0 := by simpa using hzero
    exact False.elim ((cfg.noLine 1) hbad)
  · simpa [Fin.add_def, B] using hgood

private theorem hQdeltaAt398 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (pQroot : ℝ × ℝ), ∀ (pQ : ℝ × ℝ), (pQ.1 - pQroot.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))).re
            : ℝ) - (↑(BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ)))).im : ℝ))) → ((pQ.2 - pQroot.2 = (1 / 2 : ℝ)
            * ((↑(BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3
            : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ)))).re : ℝ))) → (pQ - pQroot = sOff
            (BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)))) ) := by
  classical
  intro q cfg sOff pQroot pQ hQre hQim
  apply Prod.ext
  · change pQ.1 - pQroot.1 = _
    simpa [sOff, Prod.smul_mk] using hQre
  · change pQ.2 - pQroot.2 = _
    simpa [sOff, Prod.smul_mk] using hQim

private theorem hSdeltaAt405 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (pSroot : ℝ × ℝ), ∀ (pS : ℝ × ℝ), (pS.1 - pSroot.1 = -(1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)))).re
            : ℝ) - (↑(BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ)))).im : ℝ))) → ((pS.2 - pSroot.2 = -(1 / 2 :
            ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (1 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 :
            ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)))).re : ℝ))) → (pS - pSroot = -sOff
            (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)))) ) := by
  classical
  intro q cfg sOff pSroot pS hSre hSim
  apply Prod.ext
  · change pS.1 - pSroot.1 = _
    simpa [sOff, Prod.smul_mk] using hSre
  · change pS.2 - pSroot.2 = _
    simpa [sOff, Prod.smul_mk] using hSim

private theorem hPplusDeltaAt412 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∀ (pRoot : ℝ × ℝ), ∀ (pPplus : ℝ × ℝ), (pPplus.1 - pRoot.1 = (1 / 2 : ℝ) * ((↑B.re : ℝ) -
            (↑B.im : ℝ))) → ((pPplus.2 - pRoot.2 = (1 / 2 : ℝ) * ((↑B.im : ℝ) + (↑B.re : ℝ))) →
            (pPplus - pRoot = sOff B)) ) := by
  classical
  intro q sOff B pRoot pPplus hPplusRe hPplusIm
  apply Prod.ext
  · change pPplus.1 - pRoot.1 = _
    simpa [sOff, Prod.smul_mk] using hPplusRe
  · change pPplus.2 - pRoot.2 = _
    simpa [sOff, Prod.smul_mk] using hPplusIm

private theorem hPminusDeltaAt418 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∀ (pRoot' : ℝ × ℝ), ∀ (pPminus : ℝ × ℝ), (pPminus.1 - pRoot'.1 = -(1 / 2 : ℝ) * ((↑B.re :
            ℝ) - (↑B.im : ℝ))) → ((pPminus.2 - pRoot'.2 = -(1 / 2 : ℝ) * ((↑B.im : ℝ) + (↑B.re :
            ℝ))) → (pPminus - pRoot' = -sOff B)) ) := by
  classical
  intro q sOff B pRoot' pPminus hPminusRe hPminusIm
  apply Prod.ext
  · change pPminus.1 - pRoot'.1 = _
    simpa [sOff, Prod.smul_mk] using hPminusRe
  · change pPminus.2 - pRoot'.2 = _
    simpa [sOff, Prod.smul_mk] using hPminusIm

private theorem hPplusDelta' :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∀ (pRoot : ℝ × ℝ), ∀ (pPplus : ℝ × ℝ), ∀ (pRoot' : ℝ × ℝ), (pRoot = pRoot') → ((pPplus -
            pRoot = sOff B) → (pPplus - pRoot' = sOff B)) ) := by
  classical
  intro q sOff B pRoot pPplus pRoot' hrootAlign hPplusDelta
  rw [← hrootAlign]
  exact hPplusDelta

private theorem hslopeDiffAt427 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) →
            ((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -A - (1 - I) * B)
            → (((-sOff B - sOff (A - I * B)) - (sOff B + sOff (-A - (1 - I) * B)) = (1 / 2 :
            Real) • GaussianRealPoint (-I * (B - I * B)) ∧ (sOff B + sOff (A - I * B)) - (-sOff B
            - sOff (-A - (1 - I) * B)) = (1 / 2 : Real) • GaussianRealPoint ((-I : GaussianInt) ^
            (3 : Nat) * (B - I * B))) → (∀ (pQroot : ℝ × ℝ), ∀ (pQ : ℝ × ℝ), ∀ (pSroot : ℝ × ℝ),
            ∀ (pS : ℝ × ℝ), ∀ (pPplus : ℝ × ℝ), ∀ (pRoot' : ℝ × ℝ), ∀ (pPminus : ℝ × ℝ), (pQroot
            = pPplus) → ((pSroot = pPminus) → ((pQ - pQroot = sOff (BandVectors.2
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) → ((pS - pSroot = -sOff
            (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))) → ((pPminus -
            pRoot' = -sOff B) → ((pPplus - pRoot' = sOff B) → (pS - pQ = (1 / 2 : Real) •
            GaussianRealPoint (-I * (B - I * B))))))))))) ) := by
  classical
  intro q cfg sOff I A B a21 a13 slopeAlgebra pQroot pQ pSroot pS pPplus pRoot' pPminus hQalign
      hSalign hQdelta hSdelta hPminusDelta hPplusDelta'
  calc
    pS - pQ = (pS - pSroot) + (pSroot - pRoot') -
        (pQ - pQroot) - (pQroot - pRoot') := by
      ext <;> dsimp <;> ring
    _ = (-sOff B - sOff (A - I * B)) -
        (sOff B + sOff (-A - (1 - I) * B)) := by
      rw [hSdelta, hQdelta, hSalign, hQalign]
      rw [hPminusDelta, hPplusDelta']
      rw [a21, a13]
      ext <;> dsimp [sOff] <;> ring
    _ = (1 / 2 : Real) • GaussianRealPoint (-I * (B - I * B)) :=
      slopeAlgebra.1

private theorem hq13At444 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        BandVectors.1 (q 1) (q 3) = -U - W) ) := by
  classical
  intro q cfg U W
  have hsum := (VectorRecursionLaws q cfg.proper.1).1
  dsimp [U, W]
  linear_combination hsum

private theorem htranslateCentAt448 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -U - (1 + I) * W) →
            (((-cOff W - cOff (U + I * W)) - (cOff W + cOff (-U - (1 + I) * W)) = (1 / 2 : Real)
            • GaussianRealPoint (I * (W + I * W)) ∧ (cOff W + cOff (U + I * W)) - (-cOff W - cOff
            (-U - (1 + I) * W)) = (1 / 2 : Real) • GaussianRealPoint ((I : GaussianInt) ^ (3 :
            Nat) * (W + I * W)) ∧ cOff W + cOff (-U - (1 + I) * W) + GaussianRealPoint (I * W) =
            cOff (-U - W) ∧ -cOff W - cOff (-U - (1 + I) * W) + GaussianRealPoint ((I :
            GaussianInt) ^ (3 : Nat) * W) = -cOff (-U - W)) → ((TileCentroid (Q 1 true) -
            TileCentroid (P 0 true) = cOff (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3))) → ((TileCentroid (P 0 true) - TileCentroid T = cOff W) →
            ((TileCentroid (P 1 true) - TileCentroid T = cOff (BandVectors.1 (q 1) (q 3))) →
            ((BandVectors.1 (q 1) (q 3) = -U - W) → (TileCentroid (TileTranslation (Q 1 true) (I
            * W)) = TileCentroid (P 1 true))))))) ) := by
  classical
  intro q cfg T P Q cOff I U W v13 centroidAlgebra hQleafOff hPplus hP1 hq13
  have hform := (TileTranslationFormulas (Q 1 true) (I * W)).2.2.2.2.1
  have hform' : TileCentroid (TileTranslation (Q 1 true) (I * W)) =
      TileCentroid (Q 1 true) + GaussianRealPoint (I * W) := by
    simpa [GaussianRealPoint, Prod.add_def] using hform
  have hQcentre : TileCentroid (Q 1 true) =
      TileCentroid T + cOff W +
        cOff (BandVectors.1 (cfg.firstPredecessor 1)
          (cfg.firstPredecessor 3)) := by
    calc
      _ = TileCentroid (P 0 true) +
            cOff (BandVectors.1 (cfg.firstPredecessor 1)
              (cfg.firstPredecessor 3)) := by
        have heq := hQleafOff
        apply Prod.ext
        · have hf := congrArg Prod.fst heq
          dsimp [cOff] at hf ⊢
          linarith
        · have hf := congrArg Prod.snd heq
          dsimp [cOff] at hf ⊢
          linarith
      _ = TileCentroid T + cOff W +
            cOff (BandVectors.1 (cfg.firstPredecessor 1)
              (cfg.firstPredecessor 3)) := by
        have heq := hPplus
        apply Prod.ext
        · have hf := congrArg Prod.fst heq
          dsimp [cOff] at hf ⊢
          linarith
        · have hf := congrArg Prod.snd heq
          dsimp [cOff] at hf ⊢
          linarith
  have hP1centre : TileCentroid (P 1 true) =
      TileCentroid T + cOff (-U - W) := by
    calc
      _ = TileCentroid T + cOff (BandVectors.1 (q 1) (q 3)) := by
        have heq := hP1
        apply Prod.ext
        · have hf := congrArg Prod.fst heq
          dsimp [cOff] at hf ⊢
          linarith
        · have hf := congrArg Prod.snd heq
          dsimp [cOff] at hf ⊢
          linarith
      _ = TileCentroid T + cOff (-U - W) := by rw [hq13]
  calc
    _ = TileCentroid (Q 1 true) + GaussianRealPoint (I * W) := hform'
    _ = TileCentroid T + cOff W +
          cOff (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3)) + GaussianRealPoint (I * W) := by
      rw [hQcentre]
    _ = TileCentroid T + cOff (-U - W) := by
      rw [v13]
      have h := centroidAlgebra.2.2.1
      apply Prod.ext
      · have hf := congrArg Prod.fst h
        dsimp [cOff] at hf ⊢
        linear_combination hf
      · have hf := congrArg Prod.snd h
        dsimp [cOff] at hf ⊢
        linear_combination hf
    _ = TileCentroid (P 1 true) := hP1centre.symm

private theorem hsumVAt525 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = I * BandVectors.1 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → (BandVectors.1 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = W + I * W) ) := by
  classical
  intro q cfg I W hflipV0
  rw [cfg.secondVectorOne, cfg.secondChild, cfg.secondParentOne, hflipV0]

private theorem hsumAAt529 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -I * BandVectors.2 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = B - I * B) ) := by
  classical
  intro q cfg I B hflipA
  rw [cfg.secondParentOne, cfg.secondChild, hflipA]
  dsimp [B]
  ring

private theorem hcentTargetAt535 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (Q :
            Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (TileCentroid (S 2 false) - TileCentroid (Q 1 true) = (1 / 2 : Real) • GaussianRealPoint
            (I * (W + I * W))) → ((BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor
            0) + BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = W + I * W) →
            (TileCentroid (S 2 false) - TileCentroid (Q 1 true) = (1 / 2 : Real) •
            GaussianRealPoint ((I : GaussianInt) ^ (1 : Nat) * (BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))) ) := by
  classical
  intro q cfg Q S I W hcentdiff hsumV
  rw [hcentdiff, hsumV]
  simp [I]

private theorem hslopePairAt543 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∀ (pQ : ℝ × ℝ), ∀ (pS : ℝ × ℝ), (pS - pQ = (1 / 2 : Real) • GaussianRealPoint (-I * (B -
            I * B))) → ((BandVectors.2 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
            BandVectors.2 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = B - I * B) → (pS
            - pQ = (1 / 2 : Real) • GaussianRealPoint (((-I : GaussianInt) ^ (1 : Nat)) *
            (BandVectors.2 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))) ) := by
  classical
  intro q cfg I B pQ pS hslopeDiff hsumA
  rw [hslopeDiff, hsumA]
  simp [I]

private theorem hadjAt550 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (hpos2 : 0 < (q 2).1), ∀ (hpos3 : 0 < (q 3).1),
        let C₂ : BandCircle := ⟨⟨q 2,
          ⟨Or.inl hpos2, q, cfg.proper.1, ⟨2, rfl⟩⟩⟩, hpos2⟩
        let C₃ : BandCircle := ⟨⟨q 3,
          ⟨Or.inl hpos3, q, cfg.proper.1, ⟨3, rfl⟩⟩⟩, hpos3⟩
        ∀ (pQ : ℝ × ℝ), (PartialOdometerSlope (u (1 : Fin (3 : ℕ)) true) = some pQ) → (∀ (pS : ℝ
            × ℝ), (PartialOdometerSlope (v (2 : Fin (3 : ℕ)) false) = some pS) → ((TileCentroid
            (S 2 false) - TileCentroid (Q 1 true) = (1 / 2 : Real) • GaussianRealPoint ((I :
            GaussianInt) ^ (1 : Nat) * (BandVectors.1 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1)))) → ((pS - pQ = (1 / 2 : Real) • GaussianRealPoint (((-I :
            GaussianInt) ^ (1 : Nat)) * (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1)))) → (SubtileLatticeAdjacent C₂ C₃ (Q 1 true) (S 2 false)
            (u 1 true) (v 2 false)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data I hpos2 hpos3 C₂ C₃ pQ hQleafSlope pS hSleafSlope
      hcentTarget hslopePair
  refine ⟨?_, ?_, ⟨pQ, pS, hQleafSlope, hSleafSlope, ?_⟩⟩
  · simpa [C₂, cfg.firstParentTwo] using data.hQ 1 true
  · simpa [C₃, cfg.firstParentThree] using data.hS 2 false
  refine ⟨cfg.secondPredecessor, 0, 1, cfg.secondProper, ?_, ?_,
    hcentTarget, ?_, ?_⟩
  · simpa [C₂] using cfg.secondChild
  · simpa [C₃] using cfg.secondParentOne
  · exact congrArg Prod.fst hslopePair
  · exact congrArg Prod.snd hslopePair

private theorem hxQAt573 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → ((x ∈
            FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true)) → (x ∈ FootprintVertices (Q 1
            true))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data left_mem
  rw [(data.hobsQ 1 true).2.1]
  exact left_mem

private theorem hxSAt576 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → ((x ∈
            FootprintVertices (cert.S (2 : Fin (3 : ℕ)) false)) → (x ∈ FootprintVertices (S 2
            false))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data right_mem
  rw [(data.hobsS 2 false).2.1]
  exact right_mem

private theorem hxUAt579 :
    (by
      classical
      exact
        ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (x :
            GaussianInt), ((↑(u (1 : Fin (3 : ℕ)) true).domain : Set GaussianInt) =
            FootprintVertices (Q (1 : Fin (3 : ℕ)) true)) → ((x ∈ FootprintVertices (Q 1 true)) →
            (x ∈ (u 1 true).domain)) ) := by
  classical
  intro Q u x hQdom hxQ
  change x ∈ ((u 1 true).domain : Set GaussianInt)
  rw [hQdom]
  exact hxQ

private theorem hxVAt583 :
    (by
      classical
      exact
        ∀ (S : Fin 3 -> Bool -> ProtoTile), ∀ (v : Fin 3 -> Bool -> PartialOdometer), ∀ (x :
            GaussianInt), ((↑(v (2 : Fin (3 : ℕ)) false).domain : Set GaussianInt) =
            FootprintVertices (S (2 : Fin (3 : ℕ)) false)) → ((x ∈ FootprintVertices (S 2 false))
            → (x ∈ (v 2 false).domain)) ) := by
  classical
  intro S v x hSdom hxS
  change x ∈ ((v 2 false).domain : Set GaussianInt)
  rw [hSdom]
  exact hxS

private theorem hstarAt587 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → ((∀ (y :
            GaussianInt), y = x ∨ y = x + (1 : GaussianInt) ∨ y = x - (1 : GaussianInt) ∨ y = x +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈
            FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.S (2
            : Fin (3 : ℕ)) false)) → (((↑(u (1 : Fin (3 : ℕ)) true).domain : Set GaussianInt) =
            FootprintVertices (Q (1 : Fin (3 : ℕ)) true)) → (((↑(v (2 : Fin (3 : ℕ))
            false).domain : Set GaussianInt) = FootprintVertices (S (2 : Fin (3 : ℕ)) false)) →
            (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ (u 1
            true).domain ∨ y ∈ (v 2 false).domain)))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star hQdom hSdom y hy
  rcases star y hy with hq | hs
  · left
    change y ∈ ((u 1 true).domain : Set GaussianInt)
    rw [hQdom]
    rw [(data.hobsQ 1 true).2.1]
    exact hq
  · right
    change y ∈ ((v 2 false).domain : Set GaussianInt)
    rw [hSdom]
    rw [(data.hobsS 2 false).2.1]
    exact hs

private theorem hcompFootAt618 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (FootprintVertices (TileTranslation (Q (1 : Fin (3 : ℕ)) true) (I * W)) =
            FootprintVertices (P (1 : Fin (3 : ℕ)) true) ∧ BoundaryFootprintVertices
            (TileTranslation (Q (1 : Fin (3 : ℕ)) true) (I * W)) = BoundaryFootprintVertices (P
            (1 : Fin (3 : ℕ)) true) ∧ BoundaryFootprintEdges (TileTranslation (Q (1 : Fin (3 :
            ℕ)) true) (I * W)) = BoundaryFootprintEdges (P (1 : Fin (3 : ℕ)) true) ∧
            TileRealization (TileTranslation (Q (1 : Fin (3 : ℕ)) true) (I * W)) =
            TileRealization (P (1 : Fin (3 : ℕ)) true) ∧ TileCentroid (TileTranslation (Q (1 :
            Fin (3 : ℕ)) true) (I * W)) = TileCentroid (P (1 : Fin (3 : ℕ)) true)) →
            (FootprintVertices (TileTranslation (Q 1 true) (I * W)) = FootprintVertices (cert.P 1
            true))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data I W hcompObs
  calc
    _ = FootprintVertices (P 1 true) := hcompObs.1
    _ = FootprintVertices (cert.P 1 true) := (data.hobsP 1 true).2.1

private theorem hmarkAt623 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (x ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) ↔ marked = true) →
            ((FootprintVertices (TileTranslation (Q 1 true) (I * W)) = FootprintVertices (cert.P
            1 true)) → (x ∈ FootprintVertices (TileTranslation (Q 1 true) (I * W)) ↔ marked =
            true)) ) := by
  classical
  intro q cfg C0 T cert Q x marked I W companion hcompFoot
  rw [hcompFoot]
  exact companion

private theorem hQleafAt647 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (TileCentroid (Q 2 true) - TileCentroid (P 0 true)
            = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1)) - (-((GaussianRealPoint (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))).2), (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))).1))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  simpa [Fin.add_def] using data.hQcent 2 true

private theorem hSleafAt656 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (TileCentroid (S 1 false) - TileCentroid (P 0
            false) = -((1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor
            1) (cfg.firstPredecessor 3)) - (-((GaussianRealPoint (BandVectors.1
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))).2), (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))).1)))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  simpa [Fin.add_def] using data.hScent 1 false

private theorem hQleafOffAt665 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (P :
            Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (Q 2 true) - TileCentroid (P 0 true) = (1 / 2 : Real) • (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)) -
            (-((GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor
            1))).2), (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1))).1))) → (TileCentroid (Q 2 true) - TileCentroid (P 0 true)
            = cOff (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))) ) := by
  classical
  intro q cfg P Q cOff hQleaf
  simpa [cOff] using hQleaf

private theorem hSleafOffAt669 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (P :
            Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (S 1 false) - TileCentroid (P 0 false) = -((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))
            - (-((GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor
            3))).2), (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3))).1)))) → (TileCentroid (S 1 false) - TileCentroid (P 0
            false) = -cOff (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) )
            := by
  classical
  intro q cfg P S cOff hSleaf
  simpa [cOff] using hSleaf

private theorem hcentdiffAt677 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀
            (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) →
            ((BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -U - (1 + I) * W)
            → (((-cOff W - cOff (U + I * W)) - (cOff W + cOff (-U - (1 + I) * W)) = (1 / 2 :
            Real) • GaussianRealPoint (I * (W + I * W)) ∧ (cOff W + cOff (U + I * W)) - (-cOff W
            - cOff (-U - (1 + I) * W)) = (1 / 2 : Real) • GaussianRealPoint ((I : GaussianInt) ^
            (3 : Nat) * (W + I * W)) ∧ cOff W + cOff (-U - (1 + I) * W) + GaussianRealPoint (I *
            W) = cOff (-U - W) ∧ -cOff W - cOff (-U - (1 + I) * W) + GaussianRealPoint ((I :
            GaussianInt) ^ (3 : Nat) * W) = -cOff (-U - W)) → ((TileCentroid (Q 2 true) -
            TileCentroid (P 0 true) = cOff (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1))) → ((TileCentroid (S 1 false) - TileCentroid (P 0 false) =
            -cOff (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) →
            ((TileCentroid (P 0 true) - TileCentroid T = cOff W) → ((TileCentroid (P 0 false) -
            TileCentroid T = -cOff W) → (TileCentroid (Q 2 true) - TileCentroid (S 1 false) = (1
            / 2 : Real) • GaussianRealPoint ((I : GaussianInt) ^ (3 : Nat) * (W + I * W)))))))))
            ) := by
  classical
  intro q cfg T P Q S cOff I U W v21 v13 centroidAlgebra hQleafOff hSleafOff hPplus hPminus
  calc
    _ = (TileCentroid (Q 2 true) - TileCentroid (P 0 true)) +
          (TileCentroid (P 0 true) - TileCentroid T) -
          (TileCentroid (S 1 false) - TileCentroid (P 0 false)) -
          (TileCentroid (P 0 false) - TileCentroid T) := by
      ext <;> dsimp <;> ring
    _ = (cOff W + cOff (U + I * W)) -
          (-cOff W - cOff (-U - (1 + I) * W)) := by
      rw [hQleafOff, hPplus, hSleafOff, hPminus, v21, v13]
      ext <;> dsimp [cOff] <;> ring
    _ = (1 / 2 : Real) • GaussianRealPoint
          ((I : GaussianInt) ^ (3 : Nat) * (W + I * W)) :=
      centroidAlgebra.2.1

private theorem hQpackAt693 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∃ p pQ : Real × Real, PartialOdometerSlope (r 0
            true) = some p ∧ PartialOdometerSlope (u 2 true) = some pQ ∧ pQ.1 - p.1 = (1 / 2) *
            (((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)).re : Int) -
            ((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)).im : Int)) ∧ pQ.2
            - p.2 = (1 / 2) * (((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor
            1)).im : Int) + ((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)).re
            : Int))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  rcases data.hQslope 2 true with hzero | hgood
  · have hbad : (q 3).1 = 0 := by
      rw [← cfg.firstParentThree]
      exact hzero
    exact False.elim ((cfg.noLine 3) hbad)
  · simpa [Fin.add_def] using hgood

private theorem hSpackAt712 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∃ p pS : Real × Real, PartialOdometerSlope (r 0
            false) = some p ∧ PartialOdometerSlope (v 1 false) = some pS ∧ pS.1 - p.1 = -(1 / 2)
            * (((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)).re : Int) -
            ((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)).im : Int)) ∧ pS.2
            - p.2 = -(1 / 2) * (((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor
            3)).im : Int) + ((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)).re
            : Int))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data
  rcases data.hSslope 1 false with hzero | hgood
  · have hbad : (q 2).1 = 0 := by
      rw [← cfg.firstParentTwo]
      exact hzero
    exact False.elim ((cfg.noLine 2) hbad)
  · simpa [Fin.add_def] using hgood

private theorem hQdeltaAt765 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (pQroot : ℝ × ℝ), ∀ (pQ : ℝ × ℝ), (pQ.1 - pQroot.1 = (1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ)))).re
            : ℝ) - (↑(BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ)))).im : ℝ))) → ((pQ.2 - pQroot.2 = (1 / 2 : ℝ)
            * ((↑(BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1
            : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ)))).re : ℝ))) → (pQ - pQroot = sOff
            (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)))) ) := by
  classical
  intro q cfg sOff pQroot pQ hQre hQim
  apply Prod.ext
  · change pQ.1 - pQroot.1 = _
    simpa [sOff, Prod.smul_mk] using hQre
  · change pQ.2 - pQroot.2 = _
    simpa [sOff, Prod.smul_mk] using hQim

private theorem hSdeltaAt772 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (pSroot : ℝ × ℝ), ∀ (pS : ℝ × ℝ), (pS.1 - pSroot.1 = -(1 / 2 : ℝ) * ((↑(BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))).re
            : ℝ) - (↑(BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ)))).im : ℝ))) → ((pS.2 - pSroot.2 = -(1 / 2 :
            ℝ) * ((↑(BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 :
            ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))).re : ℝ))) → (pS - pSroot = -sOff
            (BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)))) ) := by
  classical
  intro q cfg sOff pSroot pS hSre hSim
  apply Prod.ext
  · change pS.1 - pSroot.1 = _
    simpa [sOff, Prod.smul_mk] using hSre
  · change pS.2 - pSroot.2 = _
    simpa [sOff, Prod.smul_mk] using hSim

private theorem hPminusDelta' :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∀ (pRoot : ℝ × ℝ), ∀ (pRoot' : ℝ × ℝ), ∀ (pPminus : ℝ × ℝ), (pRoot = pRoot') → ((pPminus
            - pRoot' = -sOff B) → (pPminus - pRoot = -sOff B)) ) := by
  classical
  intro q sOff B pRoot pRoot' pPminus hrootAlign hPminusDelta
  rw [hrootAlign]
  exact hPminusDelta

private theorem hslopeDiffAt794 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) →
            ((BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -A - (1 - I) * B)
            → (((-sOff B - sOff (A - I * B)) - (sOff B + sOff (-A - (1 - I) * B)) = (1 / 2 :
            Real) • GaussianRealPoint (-I * (B - I * B)) ∧ (sOff B + sOff (A - I * B)) - (-sOff B
            - sOff (-A - (1 - I) * B)) = (1 / 2 : Real) • GaussianRealPoint ((-I : GaussianInt) ^
            (3 : Nat) * (B - I * B))) → (∀ (pQroot : ℝ × ℝ), ∀ (pQ : ℝ × ℝ), ∀ (pSroot : ℝ × ℝ),
            ∀ (pS : ℝ × ℝ), ∀ (pRoot : ℝ × ℝ), ∀ (pPplus : ℝ × ℝ), ∀ (pPminus : ℝ × ℝ), (pQroot =
            pPplus) → ((pSroot = pPminus) → ((pQ - pQroot = sOff (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))) → ((pS - pSroot = -sOff
            (BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) → ((pPplus - pRoot
            = sOff B) → ((pPminus - pRoot = -sOff B) → (pQ - pS = (1 / 2 : Real) •
            GaussianRealPoint (((-I : GaussianInt) ^ (3 : Nat)) * (B - I * B))))))))))) ) := by
  classical
  intro q cfg sOff I A B a21 a13 slopeAlgebra pQroot pQ pSroot pS pRoot pPplus pPminus hQalign
      hSalign hQdelta hSdelta hPplusDelta hPminusDelta'
  calc
    pQ - pS = (pQ - pQroot) + (pQroot - pRoot) -
        (pS - pSroot) - (pSroot - pRoot) := by
      ext <;> dsimp <;> ring
    _ = (sOff B + sOff (A - I * B)) -
        (-sOff B - sOff (-A - (1 - I) * B)) := by
      rw [hQdelta, hSdelta, hQalign, hSalign]
      rw [hPplusDelta, hPminusDelta']
      rw [a21, a13]
      ext <;> dsimp [sOff] <;> ring
    _ = (1 / 2 : Real) • GaussianRealPoint
        (((-I : GaussianInt) ^ (3 : Nat)) * (B - I * B)) :=
      slopeAlgebra.2

private theorem hform'At819 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (TileCentroid (TileTranslation (S (1 : Fin (3 : ℕ)) false) (I ^ (3 : ℕ) * W)) =
            ((TileCentroid (S (1 : Fin (3 : ℕ)) false)).1 + (↑(I ^ (3 : ℕ) * W).re : ℝ),
            (TileCentroid (S (1 : Fin (3 : ℕ)) false)).2 + (↑(I ^ (3 : ℕ) * W).im : ℝ))) →
            (TileCentroid (TileTranslation (S 1 false) (I ^ (3 : Nat) * W)) = TileCentroid (S 1
            false) + GaussianRealPoint (I ^ (3 : Nat) * W)) ) := by
  classical
  intro q S I W hform
  simpa [GaussianRealPoint, Prod.add_def] using hform

private theorem hScentre :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (TileCentroid (S 1 false) - TileCentroid (P 0 false) = -cOff (BandVectors.1
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) → ((TileCentroid (P 0 false) -
            TileCentroid T = -cOff W) → (TileCentroid (S 1 false) = TileCentroid T - cOff W -
            cOff (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)))) ) := by
  classical
  intro q cfg T P S cOff W hSleafOff hPminus
  calc
    _ = TileCentroid (P 0 false) -
          cOff (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3)) := by
      have heq := hSleafOff
      apply Prod.ext
      · have hf := congrArg Prod.fst heq
        dsimp [cOff] at hf ⊢
        linear_combination hf
      · have hf := congrArg Prod.snd heq
        dsimp [cOff] at hf ⊢
        linear_combination hf
    _ = TileCentroid T - cOff W -
          cOff (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3)) := by
      have heq := hPminus
      apply Prod.ext
      · have hf := congrArg Prod.fst heq
        dsimp [cOff] at hf ⊢
        linarith
      · have hf := congrArg Prod.snd heq
        dsimp [cOff] at hf ⊢
        linarith

private theorem hP1centreAt851 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (T : ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (TileCentroid (P 1 false) - TileCentroid T = -cOff (BandVectors.1 (q 1) (q 3))) →
            ((BandVectors.1 (q 1) (q 3) = -U - W) → (TileCentroid (P 1 false) = TileCentroid T -
            cOff (-U - W))) ) := by
  classical
  intro q T P cOff U W hP1 hq13
  calc
    _ = TileCentroid T - cOff (BandVectors.1 (q 1) (q 3)) := by
      have heq := hP1
      apply Prod.ext
      · have hf := congrArg Prod.fst heq
        dsimp [cOff] at hf ⊢
        linear_combination hf
      · have hf := congrArg Prod.snd heq
        dsimp [cOff] at hf ⊢
        linear_combination hf
    _ = TileCentroid T - cOff (-U - W) := by rw [hq13]

private theorem htranslateCentAt864 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -U - (1 + I) * W) →
            (((-cOff W - cOff (U + I * W)) - (cOff W + cOff (-U - (1 + I) * W)) = (1 / 2 : Real)
            • GaussianRealPoint (I * (W + I * W)) ∧ (cOff W + cOff (U + I * W)) - (-cOff W - cOff
            (-U - (1 + I) * W)) = (1 / 2 : Real) • GaussianRealPoint ((I : GaussianInt) ^ (3 :
            Nat) * (W + I * W)) ∧ cOff W + cOff (-U - (1 + I) * W) + GaussianRealPoint (I * W) =
            cOff (-U - W) ∧ -cOff W - cOff (-U - (1 + I) * W) + GaussianRealPoint ((I :
            GaussianInt) ^ (3 : Nat) * W) = -cOff (-U - W)) → ((TileCentroid (TileTranslation (S
            1 false) (I ^ (3 : Nat) * W)) = TileCentroid (S 1 false) + GaussianRealPoint (I ^ (3
            : Nat) * W)) → ((TileCentroid (S 1 false) = TileCentroid T - cOff W - cOff
            (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) → ((TileCentroid
            (P 1 false) = TileCentroid T - cOff (-U - W)) → (TileCentroid (TileTranslation (S 1
            false) (I ^ (3 : Nat) * W)) = TileCentroid (P 1 false)))))) ) := by
  classical
  intro q cfg T P S cOff I U W v13 centroidAlgebra hform' hScentre hP1centre
  calc
    _ = TileCentroid (S 1 false) +
          GaussianRealPoint (I ^ (3 : Nat) * W) := hform'
    _ = TileCentroid T - cOff W -
          cOff (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3)) +
          GaussianRealPoint (I ^ (3 : Nat) * W) := by rw [hScentre]
    _ = TileCentroid T - cOff (-U - W) := by
      rw [v13]
      have h := centroidAlgebra.2.2.2
      apply Prod.ext
      · have hf := congrArg Prod.fst h
        dsimp [cOff] at hf ⊢
        linear_combination hf
      · have hf := congrArg Prod.snd h
        dsimp [cOff] at hf ⊢
        linear_combination hf
    _ = TileCentroid (P 1 false) := hP1centre.symm

private theorem hcentTargetAt909 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (Q :
            Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (TileCentroid (Q 2 true) - TileCentroid (S 1 false) = (1 / 2 : Real) • GaussianRealPoint
            ((I : GaussianInt) ^ (3 : Nat) * (W + I * W))) → ((BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = W + I * W) → (TileCentroid (Q 2
            true) - TileCentroid (S 1 false) = (1 / 2 : Real) • GaussianRealPoint ((I :
            GaussianInt) ^ (3 : Nat) * (BandVectors.1 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1))))) ) := by
  classical
  intro q cfg Q S I W hcentdiff hsumV
  rw [hcentdiff, hsumV]

private theorem hslopePairAt916 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        ∀ (pQ : ℝ × ℝ), ∀ (pS : ℝ × ℝ), (pQ - pS = (1 / 2 : Real) • GaussianRealPoint (((-I :
            GaussianInt) ^ (3 : Nat)) * (B - I * B))) → ((BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = B - I * B) → (pQ - pS = (1 / 2 : Real) •
            GaussianRealPoint (((-I : GaussianInt) ^ (3 : Nat)) * (BandVectors.2
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))) ) := by
  classical
  intro q cfg I B pQ pS hslopeDiff hsumA
  rw [hslopeDiff, hsumA]

private theorem hadjAt922 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (hpos2 : 0 < (q 2).1), ∀ (hpos3 : 0 < (q 3).1),
        let C₂ : BandCircle := ⟨⟨q 2,
          ⟨Or.inl hpos2, q, cfg.proper.1, ⟨2, rfl⟩⟩⟩, hpos2⟩
        let C₃ : BandCircle := ⟨⟨q 3,
          ⟨Or.inl hpos3, q, cfg.proper.1, ⟨3, rfl⟩⟩⟩, hpos3⟩
        ∀ (pQ : ℝ × ℝ), (PartialOdometerSlope (u (2 : Fin (3 : ℕ)) true) = some pQ) → (∀ (pS : ℝ
            × ℝ), (PartialOdometerSlope (v (1 : Fin (3 : ℕ)) false) = some pS) → ((TileCentroid
            (Q 2 true) - TileCentroid (S 1 false) = (1 / 2 : Real) • GaussianRealPoint ((I :
            GaussianInt) ^ (3 : Nat) * (BandVectors.1 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1)))) → ((pQ - pS = (1 / 2 : Real) • GaussianRealPoint (((-I :
            GaussianInt) ^ (3 : Nat)) * (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1)))) → (SubtileLatticeAdjacent C₂ C₃ (S 1 false) (Q 2 true)
            (v 1 false) (u 2 true)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data I hpos2 hpos3 C₂ C₃ pQ hQleafSlope pS hSleafSlope
      hcentTarget hslopePair
  refine ⟨?_, ?_, ⟨pS, pQ, hSleafSlope, hQleafSlope, ?_⟩⟩
  · simpa [C₂, cfg.firstParentTwo] using data.hS 1 false
  · simpa [C₃, cfg.firstParentThree] using data.hQ 2 true
  refine ⟨cfg.secondPredecessor, 0, 3, cfg.secondProper, ?_, ?_,
    hcentTarget, ?_, ?_⟩
  · simpa [C₂] using cfg.secondChild
  · simpa [C₃] using cfg.secondParentOne
  · exact congrArg Prod.fst hslopePair
  · exact congrArg Prod.snd hslopePair

private theorem hxSAt945 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → ((x ∈
            FootprintVertices (cert.S (1 : Fin (3 : ℕ)) false)) → (x ∈ FootprintVertices (S 1
            false))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data right_mem
  rw [(data.hobsS 1 false).2.1]
  exact right_mem

private theorem hxQAt948 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → ((x ∈
            FootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true)) → (x ∈ FootprintVertices (Q 2
            true))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data left_mem
  rw [(data.hobsQ 2 true).2.1]
  exact left_mem

private theorem hxVAt951 :
    (by
      classical
      exact
        ∀ (S : Fin 3 -> Bool -> ProtoTile), ∀ (v : Fin 3 -> Bool -> PartialOdometer), ∀ (x :
            GaussianInt), ((↑(v (1 : Fin (3 : ℕ)) false).domain : Set GaussianInt) =
            FootprintVertices (S (1 : Fin (3 : ℕ)) false)) → ((x ∈ FootprintVertices (S 1 false))
            → (x ∈ (v 1 false).domain)) ) := by
  classical
  intro S v x hSdom hxS
  change x ∈ ((v 1 false).domain : Set GaussianInt)
  rw [hSdom]
  exact hxS

private theorem hxUAt955 :
    (by
      classical
      exact
        ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (x :
            GaussianInt), ((↑(u (2 : Fin (3 : ℕ)) true).domain : Set GaussianInt) =
            FootprintVertices (Q (2 : Fin (3 : ℕ)) true)) → ((x ∈ FootprintVertices (Q 2 true)) →
            (x ∈ (u 2 true).domain)) ) := by
  classical
  intro Q u x hQdom hxQ
  change x ∈ ((u 2 true).domain : Set GaussianInt)
  rw [hQdom]
  exact hxQ

private theorem hstarAt959 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → ((∀ (y :
            GaussianInt), y = x ∨ y = x + (1 : GaussianInt) ∨ y = x - (1 : GaussianInt) ∨ y = x +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈
            FootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.S (1
            : Fin (3 : ℕ)) false)) → (((↑(v (1 : Fin (3 : ℕ)) false).domain : Set GaussianInt) =
            FootprintVertices (S (1 : Fin (3 : ℕ)) false)) → (((↑(u (2 : Fin (3 : ℕ))
            true).domain : Set GaussianInt) = FootprintVertices (Q (2 : Fin (3 : ℕ)) true)) → (∀
            y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ (v 1
            false).domain ∨ y ∈ (u 2 true).domain)))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star hSdom hQdom y hy
  rcases star y hy with hq | hs
  · right
    change y ∈ ((u 2 true).domain : Set GaussianInt)
    rw [hQdom]
    rw [(data.hobsQ 2 true).2.1]
    exact hq
  · left
    change y ∈ ((v 1 false).domain : Set GaussianInt)
    rw [hSdom]
    rw [(data.hobsS 1 false).2.1]
    exact hs

private theorem hcompFootAt990 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (FootprintVertices (TileTranslation (S (1 : Fin (3 : ℕ)) false) (I ^ (3 : ℕ) * W)) =
            FootprintVertices (P (1 : Fin (3 : ℕ)) false) ∧ BoundaryFootprintVertices
            (TileTranslation (S (1 : Fin (3 : ℕ)) false) (I ^ (3 : ℕ) * W)) =
            BoundaryFootprintVertices (P (1 : Fin (3 : ℕ)) false) ∧ BoundaryFootprintEdges
            (TileTranslation (S (1 : Fin (3 : ℕ)) false) (I ^ (3 : ℕ) * W)) =
            BoundaryFootprintEdges (P (1 : Fin (3 : ℕ)) false) ∧ TileRealization (TileTranslation
            (S (1 : Fin (3 : ℕ)) false) (I ^ (3 : ℕ) * W)) = TileRealization (P (1 : Fin (3 : ℕ))
            false) ∧ TileCentroid (TileTranslation (S (1 : Fin (3 : ℕ)) false) (I ^ (3 : ℕ) * W))
            = TileCentroid (P (1 : Fin (3 : ℕ)) false)) → (FootprintVertices (TileTranslation (S
            1 false) (I ^ (3 : Nat) * W)) = FootprintVertices (cert.P 1 false))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data I W hcompObs
  calc
    _ = FootprintVertices (P 1 false) := hcompObs.1
    _ = FootprintVertices (cert.P 1 false) := (data.hobsP 1 false).2.1

private theorem hmarkAt996 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (S : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (x ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) false) ↔ marked = true) →
            ((FootprintVertices (TileTranslation (S 1 false) (I ^ (3 : Nat) * W)) =
            FootprintVertices (cert.P 1 false)) → (x ∈ FootprintVertices (TileTranslation (S 1
            false) (I ^ (3 : Nat) * W)) ↔ marked = true)) ) := by
  classical
  intro q cfg C0 T cert S x marked I W companion hcompFoot
  rw [hcompFoot]
  exact companion

end LargestParentOdometerGeometry

namespace LargestOdometerConclusions

private theorem positiveLargestCase :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), ∀ (marked :
                Bool), (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → (∀
                (row : BandOrderedGeneralInteriorWebRow cert x marked), (∀ (c :
                CircleCoordinates), ∀ (U : ProtoTile), ∀ (k : PartialOdometer), TileOdometer c U
                k → BandPrototile c U) → (
        (BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4
            : ℕ))) = BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) →
            ((BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) = BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 :
            ℕ)))) → ((BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))) = -BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1
            : Fin (4 : ℕ))) - ((1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → ((BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) =
            -BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - ((1 : GaussianInt) -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin
            (4 : ℕ)))) → ((
        let cOff := fun (z : GaussianInt) => (1 / 2 : ℝ) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1));
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let U := BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let W := BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); -cOff W - cOff (U + I
            * W) - (cOff W + cOff (-U - ((1 : GaussianInt) + I) * W)) = (1 / 2 : ℝ) •
            GaussianRealPoint (I * (W + I * W)) ∧ cOff W + cOff (U + I * W) - (-cOff W - cOff (-U
            - ((1 : GaussianInt) + I) * W)) = (1 / 2 : ℝ) • GaussianRealPoint (I ^ (3 : ℕ) * (W +
            I * W)) ∧ cOff W + cOff (-U - ((1 : GaussianInt) + I) * W) + GaussianRealPoint (I *
            W) = cOff (-U - W) ∧ -cOff W - cOff (-U - ((1 : GaussianInt) + I) * W) +
            GaussianRealPoint (I ^ (3 : ℕ) * W) = -cOff (-U - W)) → ((
        let sOff := fun (z : GaussianInt) => (1 / 2 : ℝ) • ((↑z.re : ℝ) - (↑z.im : ℝ), (↑z.im :
            ℝ) + (↑z.re : ℝ));
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let A := BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let B := BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); -sOff B - sOff (A - I
            * B) - (sOff B + sOff (-A - ((1 : GaussianInt) - I) * B)) = (1 / 2 : ℝ) •
            GaussianRealPoint (-I * (B - I * B)) ∧ sOff B + sOff (A - I * B) - (-sOff B - sOff
            (-A - ((1 : GaussianInt) - I) * B)) = (1 / 2 : ℝ) • GaussianRealPoint ((-I) ^ (3 : ℕ)
            * (B - I * B))) → (((0 : ℤ) < (q (2 : Fin (4 : ℕ))).1) → (((0 : ℤ)
            < (q (3 : Fin (4 : ℕ))).1) → (((exists (left_mem : x ∈ FootprintVertices (cert.Q 1
                true)) (right_mem : x ∈
            FootprintVertices (cert.S 2 false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1
            \/ y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.Q 1 true) \/ y ∈
            FootprintVertices (cert.S 2 false)) (companion : x ∈ FootprintVertices (cert.P 1
            true) <-> marked = true), row = .largestPositive left_mem right_mem star companion))
            → (((exists (left_mem : x ∈ FootprintVertices (cert.Q 1 true)) (right_mem : x ∈
            FootprintVertices (cert.S 2 false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1
            \/ y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.Q 1 true) \/ y ∈
            FootprintVertices (cert.S 2 false)) (companion : x ∈ FootprintVertices (cert.P 1
            true) <-> marked = true), row = .largestPositive left_mem right_mem star companion))
            → ((marked = true -> FourNeighborLaplacian g x = 0) /\ (marked = false ->
            FourNeighborLaplacian g x = 1)))))))))))))) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x marked data row band_of_odo v21 a21 v13 a13
      centroidAlgebra slopeAlgebra hpos2 hpos3 leftCase positiveRow
  let cOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint z -
      (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  let sOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) •
      (((z.re : Int) : Real) - ((z.im : Int) : Real),
        ((z.im : Int) : Real) + ((z.re : Int) : Real))
  let I : GaussianInt := ⟨0, 1⟩
  let U : GaussianInt := BandVectors.1 (q 2) (q 1)
  let W : GaussianInt := BandVectors.1 (q 3) (q 2)
  let A : GaussianInt := BandVectors.2 (q 2) (q 1)
  let B : GaussianInt := BandVectors.2 (q 3) (q 2)
  let C₂ : BandCircle := ⟨⟨q 2,
    ⟨Or.inl hpos2, q, cfg.proper.1, ⟨2, rfl⟩⟩⟩, hpos2⟩
  let C₃ : BandCircle := ⟨⟨q 3,
    ⟨Or.inl hpos3, q, cfg.proper.1, ⟨3, rfl⟩⟩⟩, hpos3⟩
  rcases positiveRow with ⟨left_mem, right_mem, star, companion, rfl⟩
  have bq : BandPrototile (cfg.firstPredecessor 2) (Q 1 true) :=
    band_of_odo _ _ _ (data.hQ 1 true)
  have bs : BandPrototile (cfg.firstPredecessor 3) (S 2 false) :=
    band_of_odo _ _ _ (data.hS 2 false)
  have bp : BandPrototile (q 2) (P 1 true) := by
    simpa [cfg.firstParentTwo] using band_of_odo _ _ _ (data.hP 1 true)
  have hc := data.hQcent 1 true
  have hs := data.hScent 2 false
  have hQleaf := LargestParentOdometerGeometry.hQleafAt284 q cfg C0 T cert h P r Q S u v g data
  have hSleaf := LargestParentOdometerGeometry.hSleafAt293 q cfg C0 T cert h P r Q S u v g data
  have hQleafOff := LargestParentOdometerGeometry.hQleafOffAt302 q cfg P Q hQleaf
  have hSleafOff := LargestParentOdometerGeometry.hSleafOffAt305 q cfg P S hSleaf
  have hPplus : TileCentroid (P 0 true) - TileCentroid T = cOff W := by
    simpa [cOff, Fin.add_def, W] using data.hPcent 0 true
  have hPminus : TileCentroid (P 0 false) - TileCentroid T = -cOff W := by
    simpa [cOff, Fin.add_def, W] using data.hPcent 0 false
  have hcentdiff := LargestParentOdometerGeometry.hcentdiffAt312 q cfg T P Q S v21 v13
      centroidAlgebra hQleafOff hSleafOff hPplus hPminus
  have hQpack := LargestParentOdometerGeometry.hQpackAt326 q cfg C0 T cert h P r Q S u v g data
  have hSpack := LargestParentOdometerGeometry.hSpackAt345 q cfg C0 T cert h P r Q S u v g data
  have hPplusPack := LargestParentOdometerGeometry.hPplusPackAt364 q cfg C0 T cert h P r Q S u
      v g data
  have hPminusPack := LargestParentOdometerGeometry.hPminusPackAt375 q cfg C0 T cert h P r Q S
      u v g data
  obtain ⟨pQroot, pQ, hQroot, hQleafSlope, hQre, hQim⟩ := hQpack
  obtain ⟨pSroot, pS, hSroot, hSleafSlope, hSre, hSim⟩ := hSpack
  obtain ⟨pRoot, pPplus, hRoot, hPplusSlope, hPplusRe, hPplusIm⟩ :=
    hPplusPack
  obtain ⟨pRoot', pPminus, hRoot', hPminusSlope,
    hPminusRe, hPminusIm⟩ := hPminusPack
  have hQalign : pQroot = pPplus :=
    Option.some.inj (hQroot.symm.trans hPplusSlope)
  have hSalign : pSroot = pPminus :=
    Option.some.inj (hSroot.symm.trans hPminusSlope)
  have hrootAlign : pRoot = pRoot' :=
    Option.some.inj (hRoot.symm.trans hRoot')
  have hQdelta := LargestParentOdometerGeometry.hQdeltaAt398 q cfg pQroot pQ hQre hQim
  have hSdelta := LargestParentOdometerGeometry.hSdeltaAt405 q cfg pSroot pS hSre hSim
  have hPplusDelta := LargestParentOdometerGeometry.hPplusDeltaAt412 q pRoot pPplus hPplusRe
      hPplusIm
  have hPminusDelta := LargestParentOdometerGeometry.hPminusDeltaAt418 q pRoot' pPminus
      hPminusRe hPminusIm
  have hslopeDiff := LargestParentOdometerGeometry.hslopeDiffAt427 q cfg a21 a13 slopeAlgebra
      pQroot pQ pSroot pS pPplus pRoot' pPminus hQalign hSalign hQdelta hSdelta hPminusDelta
      (LargestParentOdometerGeometry.hPplusDelta' q pRoot pPplus pRoot' hrootAlign hPplusDelta)
  have hP1 := BandOdometerParentCentroids.positive q cfg C0 T cert h P r Q S u v g data
  have hq13 := LargestParentOdometerGeometry.hq13At444 q cfg
  have htranslateCent := LargestParentOdometerGeometry.htranslateCentAt448 q cfg T P Q v13
      centroidAlgebra hQleafOff hPplus hP1 hq13
  have hflipV :=
    (VectorRecursionLaws cfg.secondPredecessor cfg.secondProper.1).2.2.2.2
      cfg.secondProper
  have hflipA := (hflipV 0).2
  have hflipV0 := (hflipV 0).1
  change BandVectors.1 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = I *
        BandVectors.1 (cfg.secondPredecessor 1)
          (cfg.secondPredecessor 0) at hflipV0
  change BandVectors.2 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = -I *
        BandVectors.2 (cfg.secondPredecessor 1)
          (cfg.secondPredecessor 0) at hflipA
  rw [cfg.secondChild, cfg.secondParentOne] at hflipV0 hflipA
  have hsumV := LargestParentOdometerGeometry.hsumVAt525 q cfg hflipV0
  have hsumA := LargestParentOdometerGeometry.hsumAAt529 q cfg hflipA
  have hcentTarget := LargestParentOdometerGeometry.hcentTargetAt535 q cfg Q S hcentdiff hsumV
  have hslopePair := LargestParentOdometerGeometry.hslopePairAt543 q cfg pQ pS hslopeDiff hsumA
  have hadj := LargestParentOdometerGeometry.hadjAt550 q cfg C0 T cert h P r Q S u v g data
      hpos2 hpos3 pQ hQleafSlope pS hSleafSlope hcentTarget hslopePair
  have hcompat : OdometerCompatibility (u 1 true) (v 2 false) :=
    data.hcompat (u 1 true) (v 2 false)
      ⟨1, true, Or.inr (Or.inl rfl)⟩
      ⟨2, false, Or.inr (Or.inr rfl)⟩
  have hQodo : TileOdometer (q 2) (Q 1 true) (u 1 true) := by
    simpa [cfg.firstParentTwo] using data.hQ 1 true
  have hSodo : TileOdometer (q 3) (S 2 false) (v 2 false) := by
    simpa [cfg.firstParentThree] using data.hS 2 false
  have hQdom := PositiveCurvatureTileOdometerDomain
    (q 2) (Q 1 true) (u 1 true) hpos2 hQodo
  have hSdom := PositiveCurvatureTileOdometerDomain
    (q 3) (S 2 false) (v 2 false) hpos3 hSodo
  have hxQ := LargestParentOdometerGeometry.hxQAt573 q cfg C0 T cert h P r Q S u v g x data
      left_mem
  have hxS := LargestParentOdometerGeometry.hxSAt576 q cfg C0 T cert h P r Q S u v g x data
      right_mem
  have hxU := LargestParentOdometerGeometry.hxUAt579 Q u x hQdom hxQ
  have hxV := LargestParentOdometerGeometry.hxVAt583 S v x hSdom hxS
  have hstar := LargestParentOdometerGeometry.hstarAt587 q cfg C0 T cert h P r Q S u v g x data
      star hQdom hSdom
  have hweb := (OdometerWeb).2 C₂ C₃ cfg.secondPredecessor 0 1
    (Q 1 true) (S 2 false) (u 1 true) (v 2 false) g x pQ pS
    cfg.secondProper (by simpa [C₂] using cfg.secondChild)
    (by simpa [C₃] using cfg.secondParentOne)
    hQleafSlope hSleafSlope hcentTarget
    (congrArg Prod.fst hslopePair) (congrArg Prod.snd hslopePair)
    hadj hcompat (data.hextQ 1 true) (data.hextS 2 false) hxU hxV hstar
  have bq2 : BandPrototile (q 2) (Q 1 true) := by
    simpa [cfg.firstParentTwo] using bq
  have hcompUnique := BandPrototileCentroidUnique (q 2)
    (TileTranslation (Q 1 true) (I * W)) (P 1 true)
    (BandPrototileTranslation (q 2) (Q 1 true) (I * W) bq2) bp
    htranslateCent
  have hcompObs := ProtoTileObservableExtensionality
    (TileTranslation (Q 1 true) (I * W)) (P 1 true)
    hcompUnique.1 hcompUnique.2
  have hcompFoot := LargestParentOdometerGeometry.hcompFootAt618 q cfg C0 T cert h P r Q S u v
      g data hcompObs
  have hmark := LargestParentOdometerGeometry.hmarkAt623 q cfg C0 T cert Q x marked companion
      hcompFoot
  constructor
  · intro hm
    apply (by simpa [I, W, cfg.secondVectorOne] using hweb.1)
    exact hmark.mpr hm
  · intro hm
    apply (by simpa [I, W, cfg.secondVectorOne] using hweb.2)
    intro ht
    have htrue := hmark.mp ht
    cases marked with
    | false => cases htrue
    | true => cases hm

private theorem reflectedLargestCase :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), ∀ (marked :
                Bool), (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → (∀
                (row : BandOrderedGeneralInteriorWebRow cert x marked), (∀ (c :
                CircleCoordinates), ∀ (U : ProtoTile), ∀ (k : PartialOdometer), TileOdometer c U
                k → BandPrototile c U) → (
        (BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4
            : ℕ))) = BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) →
            ((BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) = BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 :
            ℕ)))) → ((BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))) = -BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1
            : Fin (4 : ℕ))) - ((1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → ((BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) =
            -BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - ((1 : GaussianInt) -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin
            (4 : ℕ)))) → ((
        let cOff := fun (z : GaussianInt) => (1 / 2 : ℝ) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1));
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let U := BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let W := BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); -cOff W - cOff (U + I
            * W) - (cOff W + cOff (-U - ((1 : GaussianInt) + I) * W)) = (1 / 2 : ℝ) •
            GaussianRealPoint (I * (W + I * W)) ∧ cOff W + cOff (U + I * W) - (-cOff W - cOff (-U
            - ((1 : GaussianInt) + I) * W)) = (1 / 2 : ℝ) • GaussianRealPoint (I ^ (3 : ℕ) * (W +
            I * W)) ∧ cOff W + cOff (-U - ((1 : GaussianInt) + I) * W) + GaussianRealPoint (I *
            W) = cOff (-U - W) ∧ -cOff W - cOff (-U - ((1 : GaussianInt) + I) * W) +
            GaussianRealPoint (I ^ (3 : ℕ) * W) = -cOff (-U - W)) → ((
        let sOff := fun (z : GaussianInt) => (1 / 2 : ℝ) • ((↑z.re : ℝ) - (↑z.im : ℝ), (↑z.im :
            ℝ) + (↑z.re : ℝ));
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let A := BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let B := BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); -sOff B - sOff (A - I
            * B) - (sOff B + sOff (-A - ((1 : GaussianInt) - I) * B)) = (1 / 2 : ℝ) •
            GaussianRealPoint (-I * (B - I * B)) ∧ sOff B + sOff (A - I * B) - (-sOff B - sOff
            (-A - ((1 : GaussianInt) - I) * B)) = (1 / 2 : ℝ) • GaussianRealPoint ((-I) ^ (3 : ℕ)
            * (B - I * B))) → (((0 : ℤ) < (q (2 : Fin (4 : ℕ))).1) → (((0 : ℤ)
            < (q (3 : Fin (4 : ℕ))).1) → (((exists (left_mem : x ∈ FootprintVertices (cert.Q 2
                true)) (right_mem : x ∈
            FootprintVertices (cert.S 1 false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1
            \/ y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.Q 2 true) \/ y ∈
            FootprintVertices (cert.S 1 false)) (companion : x ∈ FootprintVertices (cert.P 1
            false) <-> marked = true), row = .largestReflected left_mem right_mem star
            companion)) → (((exists (left_mem : x ∈ FootprintVertices (cert.Q 2 true)) (right_mem
            : x ∈ FootprintVertices (cert.S 1 false)) (star : forall y, y = x \/ y = x + 1 \/ y =
            x - 1 \/ y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.Q 2 true) \/
            y ∈ FootprintVertices (cert.S 1 false)) (companion : x ∈ FootprintVertices (cert.P 1
            false) <-> marked = true), row = .largestReflected left_mem right_mem star
            companion)) → ((marked = true -> FourNeighborLaplacian g x = 0) /\ (marked = false ->
            FourNeighborLaplacian g x = 1)))))))))))))) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x marked data row band_of_odo v21 a21 v13 a13
      centroidAlgebra slopeAlgebra hpos2 hpos3 rightCase reflectedRow
  let cOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint z -
      (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  let sOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) •
      (((z.re : Int) : Real) - ((z.im : Int) : Real),
        ((z.im : Int) : Real) + ((z.re : Int) : Real))
  let I : GaussianInt := ⟨0, 1⟩
  let U : GaussianInt := BandVectors.1 (q 2) (q 1)
  let W : GaussianInt := BandVectors.1 (q 3) (q 2)
  let A : GaussianInt := BandVectors.2 (q 2) (q 1)
  let B : GaussianInt := BandVectors.2 (q 3) (q 2)
  let C₂ : BandCircle := ⟨⟨q 2,
    ⟨Or.inl hpos2, q, cfg.proper.1, ⟨2, rfl⟩⟩⟩, hpos2⟩
  let C₃ : BandCircle := ⟨⟨q 3,
    ⟨Or.inl hpos3, q, cfg.proper.1, ⟨3, rfl⟩⟩⟩, hpos3⟩
  rcases reflectedRow with ⟨left_mem, right_mem, star, companion, rfl⟩
  have bq : BandPrototile (cfg.firstPredecessor 3) (Q 2 true) :=
    band_of_odo _ _ _ (data.hQ 2 true)
  have bs : BandPrototile (cfg.firstPredecessor 2) (S 1 false) :=
    band_of_odo _ _ _ (data.hS 1 false)
  have bp : BandPrototile (q 2) (P 1 false) := by
    simpa [cfg.firstParentTwo] using band_of_odo _ _ _ (data.hP 1 false)
  have hc := data.hQcent 2 true
  have hs := data.hScent 1 false
  have hQleaf := LargestParentOdometerGeometry.hQleafAt647 q cfg C0 T cert h P r Q S u v g data
  have hSleaf := LargestParentOdometerGeometry.hSleafAt656 q cfg C0 T cert h P r Q S u v g data
  have hQleafOff := LargestParentOdometerGeometry.hQleafOffAt665 q cfg P Q hQleaf
  have hSleafOff := LargestParentOdometerGeometry.hSleafOffAt669 q cfg P S hSleaf
  have hPplus : TileCentroid (P 0 true) - TileCentroid T = cOff W := by
    simpa [cOff, Fin.add_def, W] using data.hPcent 0 true
  have hPminus : TileCentroid (P 0 false) - TileCentroid T = -cOff W := by
    simpa [cOff, Fin.add_def, W] using data.hPcent 0 false
  have hcentdiff := LargestParentOdometerGeometry.hcentdiffAt677 q cfg T P Q S v21 v13
      centroidAlgebra hQleafOff hSleafOff hPplus hPminus
  have hQpack := LargestParentOdometerGeometry.hQpackAt693 q cfg C0 T cert h P r Q S u v g data
  have hSpack := LargestParentOdometerGeometry.hSpackAt712 q cfg C0 T cert h P r Q S u v g data
  have hPplusPack := LargestParentOdometerGeometry.hPplusPackAt364 q cfg C0 T cert h P r Q S u
      v g data
  have hPminusPack := LargestParentOdometerGeometry.hPminusPackAt375 q cfg C0 T cert h P r Q S
      u v g data
  obtain ⟨pQroot, pQ, hQroot, hQleafSlope, hQre, hQim⟩ := hQpack
  obtain ⟨pSroot, pS, hSroot, hSleafSlope, hSre, hSim⟩ := hSpack
  obtain ⟨pRoot, pPplus, hRoot, hPplusSlope, hPplusRe, hPplusIm⟩ :=
    hPplusPack
  obtain ⟨pRoot', pPminus, hRoot', hPminusSlope,
    hPminusRe, hPminusIm⟩ := hPminusPack
  have hQalign : pQroot = pPplus :=
    Option.some.inj (hQroot.symm.trans hPplusSlope)
  have hSalign : pSroot = pPminus :=
    Option.some.inj (hSroot.symm.trans hPminusSlope)
  have hrootAlign : pRoot = pRoot' :=
    Option.some.inj (hRoot.symm.trans hRoot')
  have hQdelta := LargestParentOdometerGeometry.hQdeltaAt765 q cfg pQroot pQ hQre hQim
  have hSdelta := LargestParentOdometerGeometry.hSdeltaAt772 q cfg pSroot pS hSre hSim
  have hPplusDelta := LargestParentOdometerGeometry.hPplusDeltaAt412 q pRoot pPplus hPplusRe
      hPplusIm
  have hPminusDelta := LargestParentOdometerGeometry.hPminusDeltaAt418 q pRoot' pPminus
      hPminusRe hPminusIm
  have hslopeDiff := LargestParentOdometerGeometry.hslopeDiffAt794 q cfg a21 a13 slopeAlgebra
      pQroot pQ pSroot pS pRoot pPplus pPminus hQalign hSalign hQdelta hSdelta hPplusDelta
      (LargestParentOdometerGeometry.hPminusDelta' q pRoot pRoot' pPminus hrootAlign
          hPminusDelta)
  have hP1 := BandOdometerParentCentroids.negative q cfg C0 T cert h P r Q S u v g data
  have hq13 := LargestParentOdometerGeometry.hq13At444 q cfg
  have hform := (TileTranslationFormulas (S 1 false)
    (((I : GaussianInt) ^ (3 : Nat)) * W)).2.2.2.2.1
  have htranslateCent := LargestParentOdometerGeometry.htranslateCentAt864 q cfg T P S v13
      centroidAlgebra (LargestParentOdometerGeometry.hform'At819 q S hform)
      (LargestParentOdometerGeometry.hScentre q cfg T P S hSleafOff hPminus)
      (LargestParentOdometerGeometry.hP1centreAt851 q T P hP1 hq13)
  have hflipV :=
    (VectorRecursionLaws cfg.secondPredecessor cfg.secondProper.1).2.2.2.2
      cfg.secondProper
  have hflipV0 := (hflipV 0).1
  have hflipA := (hflipV 0).2
  change BandVectors.1 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = I *
        BandVectors.1 (cfg.secondPredecessor 1)
          (cfg.secondPredecessor 0) at hflipV0
  change BandVectors.2 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = -I *
        BandVectors.2 (cfg.secondPredecessor 1)
          (cfg.secondPredecessor 0) at hflipA
  rw [cfg.secondChild, cfg.secondParentOne] at hflipV0 hflipA
  have hsumV := LargestParentOdometerGeometry.hsumVAt525 q cfg hflipV0
  have hsumA := LargestParentOdometerGeometry.hsumAAt529 q cfg hflipA
  have hcentTarget := LargestParentOdometerGeometry.hcentTargetAt909 q cfg Q S hcentdiff hsumV
  have hslopePair := LargestParentOdometerGeometry.hslopePairAt916 q cfg pQ pS hslopeDiff hsumA
  have hadj := LargestParentOdometerGeometry.hadjAt922 q cfg C0 T cert h P r Q S u v g data
      hpos2 hpos3 pQ hQleafSlope pS hSleafSlope hcentTarget hslopePair
  have hcompat : OdometerCompatibility (v 1 false) (u 2 true) :=
    data.hcompat (v 1 false) (u 2 true)
      ⟨1, false, Or.inr (Or.inr rfl)⟩
      ⟨2, true, Or.inr (Or.inl rfl)⟩
  have hSodo : TileOdometer (q 2) (S 1 false) (v 1 false) := by
    simpa [cfg.firstParentTwo] using data.hS 1 false
  have hQodo : TileOdometer (q 3) (Q 2 true) (u 2 true) := by
    simpa [cfg.firstParentThree] using data.hQ 2 true
  have hSdom := PositiveCurvatureTileOdometerDomain
    (q 2) (S 1 false) (v 1 false) hpos2 hSodo
  have hQdom := PositiveCurvatureTileOdometerDomain
    (q 3) (Q 2 true) (u 2 true) hpos3 hQodo
  have hxS := LargestParentOdometerGeometry.hxSAt945 q cfg C0 T cert h P r Q S u v g x data
      right_mem
  have hxQ := LargestParentOdometerGeometry.hxQAt948 q cfg C0 T cert h P r Q S u v g x data
      left_mem
  have hxV := LargestParentOdometerGeometry.hxVAt951 S v x hSdom hxS
  have hxU := LargestParentOdometerGeometry.hxUAt955 Q u x hQdom hxQ
  have hstar := LargestParentOdometerGeometry.hstarAt959 q cfg C0 T cert h P r Q S u v g x data
      star hSdom hQdom
  have hweb := (OdometerWeb).2 C₂ C₃ cfg.secondPredecessor 0 3
    (S 1 false) (Q 2 true) (v 1 false) (u 2 true) g x pS pQ
    cfg.secondProper (by simpa [C₂] using cfg.secondChild)
    (by simpa [C₃] using cfg.secondParentOne)
    hSleafSlope hQleafSlope hcentTarget
    (congrArg Prod.fst hslopePair) (congrArg Prod.snd hslopePair)
    hadj hcompat (data.hextS 1 false) (data.hextQ 2 true) hxV hxU hstar
  have bs2 : BandPrototile (q 2) (S 1 false) := by
    simpa [cfg.firstParentTwo] using bs
  have hcompUnique := BandPrototileCentroidUnique (q 2)
    (TileTranslation (S 1 false) (I ^ (3 : Nat) * W)) (P 1 false)
    (BandPrototileTranslation (q 2) (S 1 false) (I ^ (3 : Nat) * W) bs2)
    bp htranslateCent
  have hcompObs := ProtoTileObservableExtensionality
    (TileTranslation (S 1 false) (I ^ (3 : Nat) * W)) (P 1 false)
    hcompUnique.1 hcompUnique.2
  have hcompFoot := LargestParentOdometerGeometry.hcompFootAt990 q cfg C0 T cert h P r Q S u v
      g data hcompObs
  have hmark := LargestParentOdometerGeometry.hmarkAt996 q cfg C0 T cert S x marked companion
      hcompFoot
  constructor
  · intro hm
    apply (by simpa [I, W, cfg.secondVectorOne] using hweb.1)
    exact hmark.mpr hm
  · intro hm
    apply (by simpa [I, W, cfg.secondVectorOne] using hweb.2)
    intro ht
    have htrue := hmark.mp ht
    cases marked with
    | false => cases htrue
    | true => cases hm

end LargestOdometerConclusions

theorem BandOrderedGeneralLargestParentOdometerRows
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (h : PartialOdometer)
    (P : Fin 3 -> Bool -> ProtoTile)
    (r : Fin 3 -> Bool -> PartialOdometer)
    (Q S : Fin 3 -> Bool -> ProtoTile)
    (u v : Fin 3 -> Bool -> PartialOdometer)
    (g : IntegerLatticeFunction) (x : GaussianInt) (marked : Bool)
    (data : BandOrderedGeneralOdometerRowData
      q cfg C0 T cert h P r Q S u v g)
    (row : BandOrderedGeneralInteriorWebRow cert x marked)
    (largest :
      (exists
        (left_mem : x ∈ FootprintVertices (cert.Q 1 true))
        (right_mem : x ∈ FootprintVertices (cert.S 2 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.Q 1 true) \/
            y ∈ FootprintVertices (cert.S 2 false))
        (companion : x ∈ FootprintVertices (cert.P 1 true) <->
          marked = true),
        row = .largestPositive left_mem right_mem star companion) \/
      (exists
        (left_mem : x ∈ FootprintVertices (cert.Q 2 true))
        (right_mem : x ∈ FootprintVertices (cert.S 1 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.Q 2 true) \/
            y ∈ FootprintVertices (cert.S 1 false))
        (companion : x ∈ FootprintVertices (cert.P 1 false) <->
          marked = true),
        row = .largestReflected left_mem right_mem star companion)) :
    (marked = true -> FourNeighborLaplacian g x = 0) /\
    (marked = false -> FourNeighborLaplacian g x = 1) := by
-- BODY
  classical
  have band_of_odo := TileOdometerBandPrototile
  let cOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint z -
      (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  let sOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) •
      (((z.re : Int) : Real) - ((z.im : Int) : Real),
        ((z.im : Int) : Real) + ((z.re : Int) : Real))
  let I : GaussianInt := ⟨0, 1⟩
  let U : GaussianInt := BandVectors.1 (q 2) (q 1)
  let W : GaussianInt := BandVectors.1 (q 3) (q 2)
  let A : GaussianInt := BandVectors.2 (q 2) (q 1)
  let B : GaussianInt := BandVectors.2 (q 3) (q 2)
  have v21 := LargestParentOdometerGeometry.v21 q cfg (LargestParentOdometerGeometry.firstRotateV
      q cfg)
  have a21 := LargestParentOdometerGeometry.a21 q cfg (LargestParentOdometerGeometry.firstRotateA
      q cfg)
  have v13 := LargestParentOdometerGeometry.v13 q cfg v21
  have a13 := LargestParentOdometerGeometry.a13 q cfg a21
  have centroidAlgebra := LargestParentOdometerGeometry.centroidAlgebra q
  have slopeAlgebra := LargestParentOdometerGeometry.slopeAlgebra q
  have hpos2 := LargestParentOdometerGeometry.hpos2 q cfg
  have hpos3 := LargestParentOdometerGeometry.hpos3 q cfg
  let C₂ : BandCircle := ⟨⟨q 2,
    ⟨Or.inl hpos2, q, cfg.proper.1, ⟨2, rfl⟩⟩⟩, hpos2⟩
  let C₃ : BandCircle := ⟨⟨q 3,
    ⟨Or.inl hpos3, q, cfg.proper.1, ⟨3, rfl⟩⟩⟩, hpos3⟩
  rcases largest with leftCase | rightCase
  · have positiveRow :
      (exists
              (left_mem : x ∈ FootprintVertices (cert.Q 1 true))
              (right_mem : x ∈ FootprintVertices (cert.S 2 false))
              (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
                y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
                y ∈ FootprintVertices (cert.Q 1 true) \/
                  y ∈ FootprintVertices (cert.S 2 false))
              (companion : x ∈ FootprintVertices (cert.P 1 true) <->
                marked = true),
              row = .largestPositive left_mem right_mem star companion) := leftCase
    exact (LargestOdometerConclusions.positiveLargestCase q cfg C0 T cert h P r Q S u v g x
        marked data row band_of_odo v21 a21 v13 a13 centroidAlgebra slopeAlgebra hpos2 hpos3
        leftCase positiveRow)
  · have reflectedRow :
      (exists
              (left_mem : x ∈ FootprintVertices (cert.Q 2 true))
              (right_mem : x ∈ FootprintVertices (cert.S 1 false))
              (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
                y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
                y ∈ FootprintVertices (cert.Q 2 true) \/
                  y ∈ FootprintVertices (cert.S 1 false))
              (companion : x ∈ FootprintVertices (cert.P 1 false) <->
                marked = true),
              row = .largestReflected left_mem right_mem star companion) := rightCase
    exact (LargestOdometerConclusions.reflectedLargestCase q cfg C0 T cert h P r Q S u v g x
        marked data row band_of_odo v21 a21 v13 a13 centroidAlgebra slopeAlgebra hpos2 hpos3
        rightCase reflectedRow)

end ApollonianSuperharmonic

end
