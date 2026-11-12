/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.OdometerWeb
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.PositiveCutCompanionRow
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandOrderedGeneralPositiveCutOdometerRows]

/-!
# BandOrderedGeneralPositiveCutOdometerRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PositiveCutOdometerGeometry

private theorem positive_of_nonempty :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → U.cells.Nonempty → 0 <
            c.1 ) := by
  classical
  intro c U hU
  induction hU with
  | line w z hw => intro hn; simp at hn
  | unit z x a => intro _; norm_num
  | @decompose p hp S U hs hc hf hcent ih =>
      intro _
      exact (ProperBandCurvatureStructure p hp).1

private theorem pos3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 3).1) )
            := by
  classical
  intro q cfg
  have hn : 0 ≤ (q 3).1 := (ProperBandCurvatureStructure q cfg.proper).2.1 2
  have := cfg.noLine 3
  omega

private theorem posO :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (x : GaussianInt), (PositiveCutCompanionRow cert x) → ((∀ (c :
            CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → U.cells.Nonempty → 0 <
            c.1) → (0 < (cfg.firstPredecessor 1).1)) ) := by
  classical
  intro q cfg C0 T cert x geometry positive_of_nonempty
  apply positive_of_nonempty _ cert.O _ geometry.precursorNonempty
  simpa [cert.precursor_eq] using (cert.plus_occurrence 0 false).1

private theorem nestedPositive :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), (0 < (q
            2).1) → ((0 < (q 3).1) → ((0 < (cfg.firstPredecessor 1).1) → (∀ (j : Fin 3), 0 <
            (cfg.firstPredecessor j.succ).1))) ) := by
  classical
  intro q cfg pos2 pos3 posO j
  fin_cases j
  · exact posO
  · simpa [cfg.firstParentTwo] using pos2
  · simpa [cfg.firstParentThree] using pos3

private theorem sumV :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let W := BandVectors.1 (q 3) (q 2)
        let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        W + Z + X = 0 ) := by
  classical
  intro q cfg W Z X
  simpa [W, Z, X, cfg.firstParentTwo, cfg.firstParentThree] using
    (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).1

private theorem sumA :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let A := BandVectors.2 (q 3) (q 2)
        let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
        A + B + D = 0 ) := by
  classical
  intro q cfg A B D
  simpa [A, B, D, cfg.firstParentTwo, cfg.firstParentThree] using
    (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.1

private theorem sumC :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W := BandVectors.1 (q 3) (q 2)
        let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), cOff (a + b) = cOff a + cOff b) → ((W + Z + X
            = 0) → (cOff W + cOff Z + cOff X = 0)) ) := by
  classical
  intro q cfg cOff W Z X cadd sumV
  rw [← cadd, ← cadd, sumV]
  simp [cOff, GaussianRealPoint]

private theorem sumS :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let A := BandVectors.2 (q 3) (q 2)
        let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), sOff (a + b) = sOff a + sOff b) → ((A + B + D
            = 0) → (sOff A + sOff B + sOff D = 0)) ) := by
  classical
  intro q cfg sOff A B D sadd sumA
  rw [← sadd, ← sadd, sumA]
  simp [sOff]

private theorem pcent :
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
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W := BandVectors.1 (q 3) (q 2)
        ∀ (b : Bool), TileCentroid (P 0 b) - TileCentroid T = (if b then (1 : Real) else -1) •
            cOff W) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data cOff W b
  simpa [cOff, W, Fin.add_def] using data.hPcent 0 b

private theorem centO :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W := BandVectors.1 (q 3) (q 2)
        (∀ (j : Fin 3), ∀ (b : Bool), TileCentroid (Q j b) - TileCentroid (P 0 true) = (if b then
            (1 : Real) else -1) • cOff (BandVectors.1 (cfg.firstPredecessor ((j + 2).succ))
            (cfg.firstPredecessor ((j + 1).succ)))) → ((TileCentroid (P 0 true) - TileCentroid T
            = cOff W) → (TileCentroid (Q 0 false) - TileCentroid T = 0)) ) := by
  classical
  intro q cfg T P Q cOff W qcent centPp
  have hc : TileCentroid (Q 0 false) - TileCentroid (P 0 true) = -cOff W := by
    simpa [Fin.add_def, cfg.firstParentTwo, cfg.firstParentThree, W] using qcent 0 false
  rw [← sub_add_sub_cancel (TileCentroid (Q 0 false))
    (TileCentroid (P 0 true)) (TileCentroid T), hc, centPp]
  abel

private theorem centQ1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W := BandVectors.1 (q 3) (q 2)
        let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (cOff W + cOff Z + cOff X = 0) → ((∀ (j : Fin 3), ∀ (b : Bool), TileCentroid (Q j b) -
            TileCentroid (P 0 true) = (if b then (1 : Real) else -1) • cOff (BandVectors.1
            (cfg.firstPredecessor ((j + 2).succ)) (cfg.firstPredecessor ((j + 1).succ)))) →
            ((TileCentroid (P 0 true) - TileCentroid T = cOff W) → (TileCentroid (Q 1 true) -
            TileCentroid T = -cOff X))) ) := by
  classical
  intro q cfg T P Q cOff W Z X sumC qcent centPp
  have hc : TileCentroid (Q 1 true) - TileCentroid (P 0 true) = cOff Z := by
    simpa [Fin.add_def, cfg.firstParentThree, Z] using qcent 1 true
  rw [← sub_add_sub_cancel (TileCentroid (Q 1 true))
    (TileCentroid (P 0 true)) (TileCentroid T), hc, centPp]
  linear_combination sumC

private theorem centQ2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W := BandVectors.1 (q 3) (q 2)
        let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (cOff W + cOff Z + cOff X = 0) → ((∀ (j : Fin 3), ∀ (b : Bool), TileCentroid (Q j b) -
            TileCentroid (P 0 true) = (if b then (1 : Real) else -1) • cOff (BandVectors.1
            (cfg.firstPredecessor ((j + 2).succ)) (cfg.firstPredecessor ((j + 1).succ)))) →
            ((TileCentroid (P 0 true) - TileCentroid T = cOff W) → (TileCentroid (Q 2 true) -
            TileCentroid T = -cOff Z))) ) := by
  classical
  intro q cfg T P Q cOff W Z X sumC qcent centPp
  have hc : TileCentroid (Q 2 true) - TileCentroid (P 0 true) = cOff X := by
    simpa [Fin.add_def, cfg.firstParentTwo, X] using qcent 2 true
  rw [← sub_add_sub_cancel (TileCentroid (Q 2 true))
    (TileCentroid (P 0 true)) (TileCentroid T), hc, centPp]
  linear_combination sumC

private theorem centS1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W := BandVectors.1 (q 3) (q 2)
        let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (cOff W + cOff Z + cOff X = 0) → ((∀ (j : Fin 3), ∀ (b : Bool), TileCentroid (S j b) -
            TileCentroid (P 0 false) = (if b then (1 : Real) else -1) • cOff (BandVectors.1
            (cfg.firstPredecessor ((j + 2).succ)) (cfg.firstPredecessor ((j + 1).succ)))) →
            ((TileCentroid (P 0 false) - TileCentroid T = -cOff W) → (TileCentroid (S 1 false) -
            TileCentroid T = cOff X))) ) := by
  classical
  intro q cfg T P S cOff W Z X sumC scent centPm
  have hc : TileCentroid (S 1 false) - TileCentroid (P 0 false) = -cOff Z := by
    simpa [Fin.add_def, cfg.firstParentThree, Z] using scent 1 false
  rw [← sub_add_sub_cancel (TileCentroid (S 1 false))
    (TileCentroid (P 0 false)) (TileCentroid T), hc, centPm]
  linear_combination -sumC

private theorem centS2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let W := BandVectors.1 (q 3) (q 2)
        let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        (cOff W + cOff Z + cOff X = 0) → ((∀ (j : Fin 3), ∀ (b : Bool), TileCentroid (S j b) -
            TileCentroid (P 0 false) = (if b then (1 : Real) else -1) • cOff (BandVectors.1
            (cfg.firstPredecessor ((j + 2).succ)) (cfg.firstPredecessor ((j + 1).succ)))) →
            ((TileCentroid (P 0 false) - TileCentroid T = -cOff W) → (TileCentroid (S 2 false) -
            TileCentroid T = cOff Z))) ) := by
  classical
  intro q cfg T P S cOff W Z X sumC scent centPm
  have hc : TileCentroid (S 2 false) - TileCentroid (P 0 false) = -cOff X := by
    simpa [Fin.add_def, cfg.firstParentTwo, X] using scent 2 false
  rw [← sub_add_sub_cancel (TileCentroid (S 2 false))
    (TileCentroid (P 0 false)) (TileCentroid T), hc, centPm]
  linear_combination -sumC

private theorem pslope :
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
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let A := BandVectors.2 (q 3) (q 2)
        ∀ (b : Bool), ∃ a c : Real × Real, PartialOdometerSlope h = some a ∧ PartialOdometerSlope
            (r 0 b) = some c ∧ c - a = (if b then (1 : Real) else -1) • sOff A) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data sOff A b
  obtain ⟨a, c, ha, hc, hx, hy⟩ :=
    (data.hPslope 0 b).resolve_left (cfg.noLine 1)
  refine ⟨a, c, ha, hc, ?_⟩
  apply Prod.ext
  · cases b <;> simpa [sOff, A, Fin.add_def] using hx
  · cases b <;> simpa [sOff, A, Fin.add_def] using hy

private theorem qslope :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → ((∀ (j : Fin 3), 0 < (cfg.firstPredecessor
            j.succ).1) → (
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        ∀ (j : Fin 3), ∀ (b : Bool), ∃ a c : Real × Real, PartialOdometerSlope (r 0 true) = some
            a ∧ PartialOdometerSlope (u j b) = some c ∧ c - a = (if b then (1 : Real) else -1) •
            sOff (BandVectors.2 (cfg.firstPredecessor ((j + 2).succ)) (cfg.firstPredecessor ((j +
            1).succ))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data nestedPositive sOff j b
  obtain ⟨a, c, ha, hc, hx, hy⟩ :=
    (data.hQslope j b).resolve_left (ne_of_gt (nestedPositive j))
  refine ⟨a, c, ha, hc, ?_⟩
  apply Prod.ext
  · cases b <;> simpa [sOff] using hx
  · cases b <;> simpa [sOff] using hy

private theorem sslope :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → ((∀ (j : Fin 3), 0 < (cfg.firstPredecessor
            j.succ).1) → (
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        ∀ (j : Fin 3), ∀ (b : Bool), ∃ a c : Real × Real, PartialOdometerSlope (r 0 false) = some
            a ∧ PartialOdometerSlope (v j b) = some c ∧ c - a = (if b then (1 : Real) else -1) •
            sOff (BandVectors.2 (cfg.firstPredecessor ((j + 2).succ)) (cfg.firstPredecessor ((j +
            1).succ))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data nestedPositive sOff j b
  obtain ⟨a, c, ha, hc, hx, hy⟩ :=
    (data.hSslope j b).resolve_left (ne_of_gt (nestedPositive j))
  refine ⟨a, c, ha, hc, ?_⟩
  apply Prod.ext
  · cases b <;> simpa [sOff] using hx
  · cases b <;> simpa [sOff] using hy

private theorem slopeO :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let A := BandVectors.2 (q 3) (q 2)
        ∀ (z : ℝ × ℝ), ∀ (zp : ℝ × ℝ), ∀ (zO : ℝ × ℝ), (zO - zp = (if false = true then (1 : ℝ)
            else (-1 : ℝ)) • sOff (BandVectors.2 (cfg.firstPredecessor ((0 : Fin (3 : ℕ)) + (2 :
            Fin (3 : ℕ))).succ) (cfg.firstPredecessor ((0 : Fin (3 : ℕ)) + (1 : Fin (3 :
            ℕ))).succ))) → ((zp - z = sOff A) → (zO - z = 0)) ) := by
  classical
  intro q cfg sOff A z zp zO dzO slopePp
  have hh : zO - zp = -sOff A := by
    simpa [Fin.add_def, cfg.firstParentTwo, cfg.firstParentThree, A] using dzO
  linear_combination hh + slopePp

private theorem slopeQ1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let A := BandVectors.2 (q 3) (q 2)
        let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
        (sOff A + sOff B + sOff D = 0) → (∀ (z : ℝ × ℝ), ∀ (zp : ℝ × ℝ), ∀ (zQ1 : ℝ × ℝ), (zQ1 -
            zp = (if true = true then (1 : ℝ) else (-1 : ℝ)) • sOff (BandVectors.2
            (cfg.firstPredecessor ((1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ))) → ((zp - z =
            sOff A) → (zQ1 - z = -sOff D))) ) := by
  classical
  intro q cfg sOff A B D sumS z zp zQ1 dzQ1 slopePp
  have hh : zQ1 - zp = sOff B := by
    simpa [Fin.add_def, cfg.firstParentThree, B] using dzQ1
  linear_combination hh + slopePp + sumS

private theorem slopeQ2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let A := BandVectors.2 (q 3) (q 2)
        let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
        (sOff A + sOff B + sOff D = 0) → (∀ (z : ℝ × ℝ), ∀ (zp : ℝ × ℝ), ∀ (zQ2 : ℝ × ℝ), (zQ2 -
            zp = (if true = true then (1 : ℝ) else (-1 : ℝ)) • sOff (BandVectors.2
            (cfg.firstPredecessor ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ))) → ((zp - z =
            sOff A) → (zQ2 - z = -sOff B))) ) := by
  classical
  intro q cfg sOff A B D sumS z zp zQ2 dzQ2 slopePp
  have hh : zQ2 - zp = sOff D := by
    simpa [Fin.add_def, cfg.firstParentTwo, D] using dzQ2
  linear_combination hh + slopePp + sumS

private theorem slopeS1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let A := BandVectors.2 (q 3) (q 2)
        let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
        (sOff A + sOff B + sOff D = 0) → (∀ (z : ℝ × ℝ), ∀ (zm : ℝ × ℝ), ∀ (zS1 : ℝ × ℝ), (zS1 -
            zm = (if false = true then (1 : ℝ) else (-1 : ℝ)) • sOff (BandVectors.2
            (cfg.firstPredecessor ((1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ))) → ((zm - z =
            -sOff A) → (zS1 - z = sOff D))) ) := by
  classical
  intro q cfg sOff A B D sumS z zm zS1 dzS1 slopePm
  have hh : zS1 - zm = -sOff B := by
    simpa [Fin.add_def, cfg.firstParentThree, B] using dzS1
  linear_combination hh + slopePm - sumS

private theorem slopeS2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let A := BandVectors.2 (q 3) (q 2)
        let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
        (sOff A + sOff B + sOff D = 0) → (∀ (z : ℝ × ℝ), ∀ (zm : ℝ × ℝ), ∀ (zS2 : ℝ × ℝ), (zS2 -
            zm = (if false = true then (1 : ℝ) else (-1 : ℝ)) • sOff (BandVectors.2
            (cfg.firstPredecessor ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ)
            (cfg.firstPredecessor ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ))) → ((zm - z =
            -sOff A) → (zS2 - z = sOff B))) ) := by
  classical
  intro q cfg sOff A B D sumS z zm zS2 dzS2 slopePm
  have hh : zS2 - zm = -sOff D := by
    simpa [Fin.add_def, cfg.firstParentTwo, D] using dzS2
  linear_combination hh + slopePm - sumS

private theorem cforms :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (x : GaussianInt), ∀ (geometry : PositiveCutCompanionRow cert x),
        let I : GaussianInt := ⟨0, 1⟩
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let cTarget (s : Fin 4) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint
            (I ^ s.val *
              (BandVectors.1 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
                BandVectors.1 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
        (BandVectors.1 (geometry.birth (0 : Fin (4 : ℕ))) (geometry.birth
            geometry.parentIndex.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (geometry.birth geometry.parentIndex.succ) (geometry.birth (0 : Fin (4 : ℕ))) ∧
            BandVectors.2 (geometry.birth (0 : Fin (4 : ℕ))) (geometry.birth
            geometry.parentIndex.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (geometry.birth geometry.parentIndex.succ) (geometry.birth (0 : Fin (4 : ℕ)))) →
            (cTarget 1 = -cOff (BandVectors.1 (geometry.birth geometry.parentIndex.succ)
            (geometry.birth 0)) ∧ cTarget 3 = cOff (BandVectors.1 (geometry.birth
            geometry.parentIndex.succ) (geometry.birth 0)) ∧ cTarget 0 = cOff (BandVectors.1
            (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)) ∧ cTarget 2 = -cOff
            (BandVectors.1 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ))) ) := by
  classical
  intro q cfg C0 T cert x geometry I cOff cTarget flip
  dsimp only [cTarget]
  rw [flip.1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Prod.ext <;>
    norm_num [cOff, I, GaussianRealPoint, Prod.smul_mk, pow_succ] <;> ring

private theorem sforms :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (x : GaussianInt), ∀ (geometry : PositiveCutCompanionRow cert x),
        let I : GaussianInt := ⟨0, 1⟩
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let sTarget (s : Fin 4) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint
            ((-I) ^ s.val *
              (BandVectors.2 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
                BandVectors.2 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
        (BandVectors.1 (geometry.birth (0 : Fin (4 : ℕ))) (geometry.birth
            geometry.parentIndex.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (geometry.birth geometry.parentIndex.succ) (geometry.birth (0 : Fin (4 : ℕ))) ∧
            BandVectors.2 (geometry.birth (0 : Fin (4 : ℕ))) (geometry.birth
            geometry.parentIndex.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (geometry.birth geometry.parentIndex.succ) (geometry.birth (0 : Fin (4 : ℕ)))) →
            (sTarget 1 = -sOff (BandVectors.2 (geometry.birth geometry.parentIndex.succ)
            (geometry.birth 0)) ∧ sTarget 3 = sOff (BandVectors.2 (geometry.birth
            geometry.parentIndex.succ) (geometry.birth 0)) ∧ sTarget 0 = sOff (BandVectors.2
            (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)) ∧ sTarget 2 = -sOff
            (BandVectors.2 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ))) ) := by
  classical
  intro q cfg C0 T cert x geometry I sOff sTarget flip
  dsimp only [sTarget]
  rw [flip.2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Prod.ext <;>
    norm_num [sOff, I, GaussianRealPoint, Prod.smul_mk, pow_succ] <;> ring

private theorem finish :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), ∀ (geometry :
            PositiveCutCompanionRow cert x),
        let I : GaussianInt := ⟨0, 1⟩
        let cTarget (s : Fin 4) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint
            (I ^ s.val *
              (BandVectors.1 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
                BandVectors.1 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
        let sTarget (s : Fin 4) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint
            ((-I) ^ s.val *
              (BandVectors.2 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
                BandVectors.2 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
        ∀ (Uhat : ProtoTile), ∀ (What : ProtoTile), ∀ (hu : PartialOdometer), ∀ (hw :
            PartialOdometer), (TileOdometer (geometry.birth 0) Uhat hu) → ((TileOdometer
            (geometry.birth geometry.parentIndex.succ) What hw) → ((FootprintVertices Uhat =
            FootprintVertices geometry.child) → ((FootprintVertices What = FootprintVertices
            geometry.parent) → ((GlobalOdometerExtends g hu) → ((GlobalOdometerExtends g hw) →
            ((OdometerCompatibility hu hw) → ((0 < (geometry.birth geometry.parentIndex.succ).1)
            → (∀ (pU : Real × Real), ∀ (pW : Real × Real), (PartialOdometerSlope hu = some pU) →
            ((PartialOdometerSlope hw = some pW) → ((TileCentroid What - TileCentroid Uhat =
            cTarget geometry.rotation) → ((pW - pU = sTarget geometry.rotation) →
            (FourNeighborLaplacian g x = 1)))))))))))) ) := by
  classical
  intro q cfg C0 T cert g x geometry I cTarget sTarget Uhat What hu hw hUodo hWodo hUfoot hWfoot
      hUext hWext hcompat hWpos pU pW hpU hpW hcent hslope
  have hp := geometry.proper
  have hUpos := (ProperBandCurvatureStructure geometry.birth hp).1
  let CU : BandCircle :=
    ⟨⟨geometry.birth 0, Or.inl hUpos, geometry.birth, hp.1, 0, rfl⟩, hUpos⟩
  let CW : BandCircle :=
    ⟨⟨geometry.birth geometry.parentIndex.succ, Or.inl hWpos,
      geometry.birth, hp.1, geometry.parentIndex.succ, rfl⟩, hWpos⟩
  have domU := PositiveCurvatureTileOdometerDomain _ Uhat hu hUpos hUodo
  have domW := PositiveCurvatureTileOdometerDomain _ What hw hWpos hWodo
  have memU : x ∈ hu.domain := by
    change x ∈ (hu.domain : Set GaussianInt)
    rw [domU, hUfoot]
    exact geometry.child_mem
  have memW : x ∈ hw.domain := by
    change x ∈ (hw.domain : Set GaussianInt)
    rw [domW, hWfoot]
    exact geometry.parent_mem
  have star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
      y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ hu.domain ∨ y ∈ hw.domain := by
    intro y hy
    change y ∈ (hu.domain : Set GaussianInt) ∨ y ∈ (hw.domain : Set GaussianInt)
    rw [domU, domW, hUfoot, hWfoot]
    exact geometry.star y hy
  let uR := I ^ geometry.rotation.val *
    (if Even geometry.rotation.val then
      BandVectors.1 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)
    else BandVectors.1 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0))
  have translated : FootprintVertices (TileTranslation Uhat uR) =
      FootprintVertices (TileTranslation geometry.child uR) := by
    rw [(TileTranslationFormulas Uhat uR).2.2.2.2.2.1,
      (TileTranslationFormulas geometry.child uR).2.2.2.2.2.1, hUfoot]
  have absent : x ∉ FootprintVertices (TileTranslation Uhat uR) := by
    rw [translated]
    exact geometry.rightAbsent
  have slope1 := congrArg Prod.fst hslope
  have slope2 := congrArg Prod.snd hslope
  have adj : SubtileLatticeAdjacent CU CW Uhat What hu hw :=
    ⟨hUodo, hWodo, pU, pW, hpU, hpW, geometry.birth, geometry.parentIndex,
      geometry.rotation, hp, rfl, rfl, hcent, slope1, slope2⟩
  exact ((OdometerWeb.2 CU CW geometry.birth geometry.parentIndex geometry.rotation
    Uhat What hu hw g x pU pW hp rfl rfl hpU hpW hcent slope1 slope2 adj
    hcompat hUext hWext memU memW star).2 absent)

end PositiveCutOdometerGeometry

namespace PositiveCutOdometerConclusion

private theorem positiveCutConclusion :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt),
            (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → (∀ (geometry :
            PositiveCutCompanionRow cert x), (0 < (q 2).1) → ((0 < (q 3).1) → ((0 <
            (cfg.firstPredecessor 1).1) → (
        let I : GaussianInt := ⟨0, 1⟩
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let sOff (z : GaussianInt) : Real × Real :=
          ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
            (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
        let W := BandVectors.1 (q 3) (q 2)
        let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
        let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
        let A := BandVectors.2 (q 3) (q 2)
        let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
        let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
        (cOff W + cOff Z + cOff X = 0) → ((sOff A + sOff B + sOff D = 0) → ((TileCentroid (Q 0
            false) - TileCentroid T = 0) → ((TileCentroid (Q 1 true) - TileCentroid T = -cOff X)
            → ((TileCentroid (Q 2 true) - TileCentroid T = -cOff Z) → ((TileCentroid (S 1 false)
            - TileCentroid T = cOff X) → ((TileCentroid (S 2 false) - TileCentroid T = cOff Z) →
            (∀ (z : ℝ × ℝ), ∀ (zO : ℝ × ℝ), (PartialOdometerSlope (u (0 : Fin (3 : ℕ)) false) =
            some zO) → (∀ (zQ1 : ℝ × ℝ), (PartialOdometerSlope (u (1 : Fin (3 : ℕ)) true) = some
            zQ1) → (∀ (zQ2 : ℝ × ℝ), (PartialOdometerSlope (u (2 : Fin (3 : ℕ)) true) = some zQ2)
            → (∀ (zS1 : ℝ × ℝ), (PartialOdometerSlope (v (1 : Fin (3 : ℕ)) false) = some zS1) →
            (∀ (zS2 : ℝ × ℝ), (PartialOdometerSlope (v (2 : Fin (3 : ℕ)) false) = some zS2) →
            ((zO - z = 0) → ((zQ1 - z = -sOff D) → ((zQ2 - z = -sOff B) → ((zS1 - z = sOff D) →
            ((zS2 - z = sOff B) → (
        let cTarget (s : Fin 4) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint
            (I ^ s.val *
              (BandVectors.1 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
                BandVectors.1 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
        let sTarget (s : Fin 4) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint
            ((-I) ^ s.val *
              (BandVectors.2 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
                BandVectors.2 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
        (cTarget 1 = -cOff (BandVectors.1 (geometry.birth geometry.parentIndex.succ)
            (geometry.birth 0)) ∧ cTarget 3 = cOff (BandVectors.1 (geometry.birth
            geometry.parentIndex.succ) (geometry.birth 0)) ∧ cTarget 0 = cOff (BandVectors.1
            (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)) ∧ cTarget 2 = -cOff
            (BandVectors.1 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ))) →
            ((sTarget 1 = -sOff (BandVectors.2 (geometry.birth geometry.parentIndex.succ)
            (geometry.birth 0)) ∧ sTarget 3 = sOff (BandVectors.2 (geometry.birth
            geometry.parentIndex.succ) (geometry.birth 0)) ∧ sTarget 0 = sOff (BandVectors.2
            (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)) ∧ sTarget 2 = -sOff
            (BandVectors.2 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ))) → ((∀
            (Uhat : ProtoTile), ∀ (What : ProtoTile), ∀ (hu : PartialOdometer), ∀ (hw :
            PartialOdometer), (TileOdometer (geometry.birth 0) Uhat hu) → ((TileOdometer
            (geometry.birth geometry.parentIndex.succ) What hw) → ((FootprintVertices Uhat =
            FootprintVertices geometry.child) → ((FootprintVertices What = FootprintVertices
            geometry.parent) → ((GlobalOdometerExtends g hu) → ((GlobalOdometerExtends g hw) →
            ((OdometerCompatibility hu hw) → ((0 < (geometry.birth geometry.parentIndex.succ).1)
            → (∀ (pU : Real × Real), ∀ (pW : Real × Real), (PartialOdometerSlope hu = some pU) →
            ((PartialOdometerSlope hw = some pW) → ((TileCentroid What - TileCentroid Uhat =
            cTarget geometry.rotation) → ((pW - pU = sTarget geometry.rotation) →
            (FourNeighborLaplacian g x = 1))))))))))))) → (FourNeighborLaplacian g x =
            1)))))))))))))))))))))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data geometry pos2 pos3 posO I cOff sOff W Z X A B D
      sumC sumS centO centQ1 centQ2 centS1 centS2 z zO hzO zQ1 hzQ1 zQ2 hzQ2 zS1 hzS1 zS2 hzS2
      slopeO slopeQ1 slopeQ2 slopeS1 slopeS2 cTarget sTarget cforms sforms finish
  rcases geometry.literalRow with row | row | row | row | row | row | row | row
  all_goals obtain ⟨hbirth, hindex, hrotation, hx, hchild, hparent⟩ := row
  all_goals
    have hb0 := congrFun hbirth (0 : Fin 4)
    have hb2 := congrFun hbirth (2 : Fin 4)
    have hb3 := congrFun hbirth (3 : Fin 4)
    norm_num at hb0 hb2 hb3
  · refine finish (Q 1 true) (S 2 false) (u 1 true) (v 2 false)
      ?_ ?_ ?_ ?_ (data.hextQ 1 true) (data.hextS 2 false)
      ?_ ?_ zQ1 zS2 hzQ1 hzS2 ?_ ?_
    · simpa [hb0, cfg.firstParentTwo] using data.hQ 1 true
    · simpa [hindex, hb2, cfg.firstParentThree] using data.hS 2 false
    · simpa [hchild] using (data.hobsQ 1 true).2.1
    · simpa [hparent] using (data.hobsS 2 false).2.1
    · exact data.hcompat _ _ ⟨1, true, Or.inr (Or.inl rfl)⟩
        ⟨2, false, Or.inr (Or.inr rfl)⟩
    · simpa [hindex, hb2] using pos3
    · rw [hrotation, cforms.1, hindex]
      change TileCentroid (S 2 false) - TileCentroid (Q 1 true) =
        -cOff (BandVectors.1 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change TileCentroid (S 2 false) - TileCentroid (Q 1 true) = -cOff W
      linear_combination centS2 - centQ1 + sumC
    · rw [hrotation, sforms.1, hindex]
      change zS2 - zQ1 = -sOff (BandVectors.2 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change zS2 - zQ1 = -sOff A
      linear_combination slopeS2 - slopeQ1 + sumS
  · refine finish (Q 1 true) (Q 0 false) (u 1 true) (u 0 false)
      ?_ ?_ ?_ ?_ (data.hextQ 1 true) (data.hextQ 0 false)
      ?_ ?_ zQ1 zO hzQ1 hzO ?_ ?_
    · simpa [hb0, cfg.firstParentTwo] using data.hQ 1 true
    · simpa [hindex, hb3] using data.hQ 0 false
    · simpa [hchild] using (data.hobsQ 1 true).2.1
    · simpa [hparent, cert.precursor_eq] using (data.hobsQ 0 false).2.1
    · exact data.hcompat _ _ ⟨1, true, Or.inr (Or.inl rfl)⟩
        ⟨0, false, Or.inr (Or.inl rfl)⟩
    · simpa [hindex, hb3] using posO
    · rw [hrotation, cforms.2.2.1, hindex]
      change TileCentroid (Q 0 false) - TileCentroid (Q 1 true) =
        cOff (BandVectors.1 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change TileCentroid (Q 0 false) - TileCentroid (Q 1 true) = cOff X
      linear_combination centO - centQ1
    · rw [hrotation, sforms.2.2.1, hindex]
      change zO - zQ1 = sOff (BandVectors.2 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change zO - zQ1 = sOff D
      linear_combination slopeO - slopeQ1
  · refine finish (S 1 false) (Q 2 true) (v 1 false) (u 2 true)
      ?_ ?_ ?_ ?_ (data.hextS 1 false) (data.hextQ 2 true)
      ?_ ?_ zS1 zQ2 hzS1 hzQ2 ?_ ?_
    · simpa [hb0, cfg.firstParentTwo] using data.hS 1 false
    · simpa [hindex, hb2, cfg.firstParentThree] using data.hQ 2 true
    · simpa [hchild] using (data.hobsS 1 false).2.1
    · simpa [hparent] using (data.hobsQ 2 true).2.1
    · exact data.hcompat _ _ ⟨1, false, Or.inr (Or.inr rfl)⟩
        ⟨2, true, Or.inr (Or.inl rfl)⟩
    · simpa [hindex, hb2] using pos3
    · rw [hrotation, cforms.2.1, hindex]
      change TileCentroid (Q 2 true) - TileCentroid (S 1 false) =
        cOff (BandVectors.1 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change TileCentroid (Q 2 true) - TileCentroid (S 1 false) = cOff W
      linear_combination centQ2 - centS1 - sumC
    · rw [hrotation, sforms.2.1, hindex]
      change zQ2 - zS1 = sOff (BandVectors.2 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change zQ2 - zS1 = sOff A
      linear_combination slopeQ2 - slopeS1 - sumS
  · refine finish (S 1 false) (Q 0 false) (v 1 false) (u 0 false)
      ?_ ?_ ?_ ?_ (data.hextS 1 false) (data.hextQ 0 false)
      ?_ ?_ zS1 zO hzS1 hzO ?_ ?_
    · simpa [hb0, cfg.firstParentTwo] using data.hS 1 false
    · simpa [hindex, hb3] using data.hQ 0 false
    · simpa [hchild] using (data.hobsS 1 false).2.1
    · simpa [hparent, cert.precursor_eq] using (data.hobsQ 0 false).2.1
    · exact data.hcompat _ _ ⟨1, false, Or.inr (Or.inr rfl)⟩
        ⟨0, false, Or.inr (Or.inl rfl)⟩
    · simpa [hindex, hb3] using posO
    · rw [hrotation, cforms.2.2.2, hindex]
      change TileCentroid (Q 0 false) - TileCentroid (S 1 false) =
        -cOff (BandVectors.1 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change TileCentroid (Q 0 false) - TileCentroid (S 1 false) = -cOff X
      linear_combination centO - centS1
    · rw [hrotation, sforms.2.2.2, hindex]
      change zO - zS1 = -sOff (BandVectors.2 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change zO - zS1 = -sOff D
      linear_combination slopeO - slopeS1
  · refine finish (Q 0 false) (Q 1 true) (u 0 false) (u 1 true)
      ?_ ?_ ?_ ?_ (data.hextQ 0 false) (data.hextQ 1 true)
      ?_ ?_ zO zQ1 hzO hzQ1 ?_ ?_
    · simpa [hb0] using data.hQ 0 false
    · simpa [hindex, hb2, cfg.firstParentTwo] using data.hQ 1 true
    · simpa [hchild, cert.precursor_eq] using (data.hobsQ 0 false).2.1
    · simpa [hparent] using (data.hobsQ 1 true).2.1
    · exact data.hcompat _ _ ⟨0, false, Or.inr (Or.inl rfl)⟩
        ⟨1, true, Or.inr (Or.inl rfl)⟩
    · simpa [hindex, hb2] using pos2
    · rw [hrotation, cforms.1, hindex]
      change TileCentroid (Q 1 true) - TileCentroid (Q 0 false) =
        -cOff (BandVectors.1 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change TileCentroid (Q 1 true) - TileCentroid (Q 0 false) = -cOff X
      linear_combination centQ1 - centO
    · rw [hrotation, sforms.1, hindex]
      change zQ1 - zO = -sOff (BandVectors.2 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change zQ1 - zO = -sOff D
      linear_combination slopeQ1 - slopeO
  · refine finish (Q 0 false) (S 2 false) (u 0 false) (v 2 false)
      ?_ ?_ ?_ ?_ (data.hextQ 0 false) (data.hextS 2 false)
      ?_ ?_ zO zS2 hzO hzS2 ?_ ?_
    · simpa [hb0] using data.hQ 0 false
    · simpa [hindex, hb3, cfg.firstParentThree] using data.hS 2 false
    · simpa [hchild, cert.precursor_eq] using (data.hobsQ 0 false).2.1
    · simpa [hparent] using (data.hobsS 2 false).2.1
    · exact data.hcompat _ _ ⟨0, false, Or.inr (Or.inl rfl)⟩
        ⟨2, false, Or.inr (Or.inr rfl)⟩
    · simpa [hindex, hb3] using pos3
    · rw [hrotation, cforms.2.2.1, hindex]
      change TileCentroid (S 2 false) - TileCentroid (Q 0 false) =
        cOff (BandVectors.1 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change TileCentroid (S 2 false) - TileCentroid (Q 0 false) = cOff Z
      linear_combination centS2 - centO
    · rw [hrotation, sforms.2.2.1, hindex]
      change zS2 - zO = sOff (BandVectors.2 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change zS2 - zO = sOff B
      linear_combination slopeS2 - slopeO
  · refine finish (Q 0 false) (S 1 false) (u 0 false) (v 1 false)
      ?_ ?_ ?_ ?_ (data.hextQ 0 false) (data.hextS 1 false)
      ?_ ?_ zO zS1 hzO hzS1 ?_ ?_
    · simpa [hb0] using data.hQ 0 false
    · simpa [hindex, hb2, cfg.firstParentTwo] using data.hS 1 false
    · simpa [hchild, cert.precursor_eq] using (data.hobsQ 0 false).2.1
    · simpa [hparent] using (data.hobsS 1 false).2.1
    · exact data.hcompat _ _ ⟨0, false, Or.inr (Or.inl rfl)⟩
        ⟨1, false, Or.inr (Or.inr rfl)⟩
    · simpa [hindex, hb2] using pos2
    · rw [hrotation, cforms.2.1, hindex]
      change TileCentroid (S 1 false) - TileCentroid (Q 0 false) =
        cOff (BandVectors.1 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change TileCentroid (S 1 false) - TileCentroid (Q 0 false) = cOff X
      linear_combination centS1 - centO
    · rw [hrotation, sforms.2.1, hindex]
      change zS1 - zO = sOff (BandVectors.2 (geometry.birth 2) (geometry.birth 0))
      rw [hb0, hb2]
      change zS1 - zO = sOff D
      linear_combination slopeS1 - slopeO
  · refine finish (Q 0 false) (Q 2 true) (u 0 false) (u 2 true)
      ?_ ?_ ?_ ?_ (data.hextQ 0 false) (data.hextQ 2 true)
      ?_ ?_ zO zQ2 hzO hzQ2 ?_ ?_
    · simpa [hb0] using data.hQ 0 false
    · simpa [hindex, hb3, cfg.firstParentThree] using data.hQ 2 true
    · simpa [hchild, cert.precursor_eq] using (data.hobsQ 0 false).2.1
    · simpa [hparent] using (data.hobsQ 2 true).2.1
    · exact data.hcompat _ _ ⟨0, false, Or.inr (Or.inl rfl)⟩
        ⟨2, true, Or.inr (Or.inl rfl)⟩
    · simpa [hindex, hb3] using pos3
    · rw [hrotation, cforms.2.2.2, hindex]
      change TileCentroid (Q 2 true) - TileCentroid (Q 0 false) =
        -cOff (BandVectors.1 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change TileCentroid (Q 2 true) - TileCentroid (Q 0 false) = -cOff Z
      linear_combination centQ2 - centO
    · rw [hrotation, sforms.2.2.2, hindex]
      change zQ2 - zO = -sOff (BandVectors.2 (geometry.birth 0) (geometry.birth 3))
      rw [hb0, hb3]
      change zQ2 - zO = -sOff B
      linear_combination slopeQ2 - slopeO

end PositiveCutOdometerConclusion

theorem BandOrderedGeneralPositiveCutOdometerRows
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (h : PartialOdometer)
    (P : Fin 3 -> Bool -> ProtoTile)
    (r : Fin 3 -> Bool -> PartialOdometer)
    (Q S : Fin 3 -> Bool -> ProtoTile)
    (u v : Fin 3 -> Bool -> PartialOdometer)
    (g : IntegerLatticeFunction) (x : GaussianInt)
    (data : BandOrderedGeneralOdometerRowData
      q cfg C0 T cert h P r Q S u v g)
    (geometry : PositiveCutCompanionRow cert x) :
    FourNeighborLaplacian g x = 1 := by
-- BODY
  classical
  have pos2 : 0 < (q 2).1 := by linarith [cfg.secondLarge]
  have pos3 := PositiveCutOdometerGeometry.pos3 q cfg
  have posO := PositiveCutOdometerGeometry.posO q cfg C0 T cert
      x geometry (PositiveCutOdometerGeometry.positive_of_nonempty)
  have nestedPositive := PositiveCutOdometerGeometry.nestedPositive q cfg pos2 pos3 posO
  let I : GaussianInt := ⟨0, 1⟩
  let cOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint z -
      (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  let sOff (z : GaussianInt) : Real × Real :=
    ((1 / 2 : Real) * ((z.re : Real) - (z.im : Real)),
      (1 / 2 : Real) * ((z.im : Real) + (z.re : Real)))
  let W := BandVectors.1 (q 3) (q 2)
  let Z := BandVectors.1 (cfg.firstPredecessor 1) (q 3)
  let X := BandVectors.1 (q 2) (cfg.firstPredecessor 1)
  let A := BandVectors.2 (q 3) (q 2)
  let B := BandVectors.2 (cfg.firstPredecessor 1) (q 3)
  let D := BandVectors.2 (q 2) (cfg.firstPredecessor 1)
  have cadd (a b : GaussianInt) : cOff (a + b) = cOff a + cOff b := by
    apply Prod.ext <;> simp [cOff, GaussianRealPoint, Prod.smul_mk] <;> ring
  have sadd (a b : GaussianInt) : sOff (a + b) = sOff a + sOff b := by
    apply Prod.ext <;> simp [sOff] <;> ring
  have sumC := PositiveCutOdometerGeometry.sumC q cfg cadd
      (PositiveCutOdometerGeometry.sumV q cfg)
  have sumS := PositiveCutOdometerGeometry.sumS q cfg sadd
      (PositiveCutOdometerGeometry.sumA q cfg)
  have pcent (b : Bool) : TileCentroid (P 0 b) - TileCentroid T =
      (if b then (1 : Real) else -1) • cOff W := PositiveCutOdometerGeometry.pcent q cfg C0 T
          cert h P r Q S u v g data b
  have qcent (j : Fin 3) (b : Bool) :
      TileCentroid (Q j b) - TileCentroid (P 0 true) =
        (if b then (1 : Real) else -1) • cOff
          (BandVectors.1 (cfg.firstPredecessor ((j + 2).succ))
            (cfg.firstPredecessor ((j + 1).succ))) := data.hQcent j b
  have scent (j : Fin 3) (b : Bool) :
      TileCentroid (S j b) - TileCentroid (P 0 false) =
        (if b then (1 : Real) else -1) • cOff
          (BandVectors.1 (cfg.firstPredecessor ((j + 2).succ))
            (cfg.firstPredecessor ((j + 1).succ))) := data.hScent j b
  have centPp : TileCentroid (P 0 true) - TileCentroid T = cOff W := by
    simpa using pcent true
  have centPm : TileCentroid (P 0 false) - TileCentroid T = -cOff W := by
    simpa using pcent false
  have centO := PositiveCutOdometerGeometry.centO
      q cfg T P Q qcent centPp
  have centQ1 := PositiveCutOdometerGeometry.centQ1 q cfg T P Q sumC qcent centPp
  have centQ2 := PositiveCutOdometerGeometry.centQ2 q cfg T P Q sumC qcent centPp
  have centS1 := PositiveCutOdometerGeometry.centS1 q cfg T P S sumC scent centPm
  have centS2 := PositiveCutOdometerGeometry.centS2 q cfg T P S sumC scent centPm
  have pslope :
    ∀ (b : Bool), ∃ a c : Real × Real,
          PartialOdometerSlope h = some a ∧
          PartialOdometerSlope (r 0 b) = some c ∧
          c - a = (if b then (1 : Real) else -1) • sOff A := PositiveCutOdometerGeometry.pslope q
              cfg C0 T cert h P r Q S u v g data
  have qslope :
    ∀ (j : Fin 3) (b : Bool), ∃ a c : Real × Real,
          PartialOdometerSlope (r 0 true) = some a ∧
          PartialOdometerSlope (u j b) = some c ∧
          c - a = (if b then (1 : Real) else -1) • sOff
            (BandVectors.2 (cfg.firstPredecessor ((j + 2).succ))
              (cfg.firstPredecessor ((j + 1).succ))) := PositiveCutOdometerGeometry.qslope q cfg
                  C0 T cert h P r Q S u v g data
      nestedPositive
  have sslope :
    ∀ (j : Fin 3) (b : Bool), ∃ a c : Real × Real,
          PartialOdometerSlope (r 0 false) = some a ∧
          PartialOdometerSlope (v j b) = some c ∧
          c - a = (if b then (1 : Real) else -1) • sOff
            (BandVectors.2 (cfg.firstPredecessor ((j + 2).succ))
              (cfg.firstPredecessor ((j + 1).succ))) := PositiveCutOdometerGeometry.sslope q cfg
                  C0 T cert h P r Q S u v g data
      nestedPositive
  obtain ⟨z, zp, hz, hzp, dzp⟩ := pslope true
  obtain ⟨z', zm, hz', hzm, dzm⟩ := pslope false
  have align : z' = z := Option.some.inj (hz'.symm.trans hz)
  subst z'
  obtain ⟨zp', zO, hzp', hzO, dzO⟩ := qslope 0 false
  have align : zp' = zp := Option.some.inj (hzp'.symm.trans hzp)
  subst zp'
  obtain ⟨zp', zQ1, hzp', hzQ1, dzQ1⟩ := qslope 1 true
  have align : zp' = zp := Option.some.inj (hzp'.symm.trans hzp)
  subst zp'
  obtain ⟨zp', zQ2, hzp', hzQ2, dzQ2⟩ := qslope 2 true
  have align : zp' = zp := Option.some.inj (hzp'.symm.trans hzp)
  subst zp'
  obtain ⟨zm', zS1, hzm', hzS1, dzS1⟩ := sslope 1 false
  have align : zm' = zm := Option.some.inj (hzm'.symm.trans hzm)
  subst zm'
  obtain ⟨zm', zS2, hzm', hzS2, dzS2⟩ := sslope 2 false
  have align : zm' = zm := Option.some.inj (hzm'.symm.trans hzm)
  subst zm'
  have slopePp : zp - z = sOff A := by simpa using dzp
  have slopePm : zm - z = -sOff A := by simpa using dzm
  have slopeO := PositiveCutOdometerGeometry.slopeO q cfg z zp zO dzO slopePp
  have slopeQ1 := PositiveCutOdometerGeometry.slopeQ1 q cfg sumS z zp zQ1
      dzQ1 slopePp
  have slopeQ2 := PositiveCutOdometerGeometry.slopeQ2 q cfg sumS z zp zQ2
      dzQ2 slopePp
  have slopeS1 := PositiveCutOdometerGeometry.slopeS1 q cfg sumS z zm zS1 dzS1
      slopePm
  have slopeS2 := PositiveCutOdometerGeometry.slopeS2 q cfg sumS z zm zS2 dzS2
      slopePm
  let cTarget (s : Fin 4) : Real × Real :=
    (1 / 2 : Real) • GaussianRealPoint
      (I ^ s.val *
        (BandVectors.1 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
          BandVectors.1 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
  let sTarget (s : Fin 4) : Real × Real :=
    (1 / 2 : Real) • GaussianRealPoint
      ((-I) ^ s.val *
        (BandVectors.2 (geometry.birth geometry.parentIndex.succ) (geometry.birth 0) +
          BandVectors.2 (geometry.birth 0) (geometry.birth geometry.parentIndex.succ)))
  have flip := (VectorRecursionLaws geometry.birth geometry.proper.1).2.2.2.2
    geometry.proper geometry.parentIndex
  have cforms := PositiveCutOdometerGeometry.cforms q cfg C0 T cert x geometry flip
  have sforms := PositiveCutOdometerGeometry.sforms q cfg C0 T cert x geometry flip
  have finish := PositiveCutOdometerGeometry.finish q cfg C0 T cert g x geometry
  have positiveCutConclusion := PositiveCutOdometerConclusion.positiveCutConclusion q cfg C0 T
      cert h P r Q S u v g x data geometry pos2 pos3 posO sumC sumS centO centQ1 centQ2 centS1
      centS2 z zO hzO zQ1 hzQ1 zQ2 hzQ2 zS1 hzS1 zS2 hzS2 slopeO slopeQ1 slopeQ2 slopeS1 slopeS2
      cforms sforms finish
  exact positiveCutConclusion


end ApollonianSuperharmonic

end
