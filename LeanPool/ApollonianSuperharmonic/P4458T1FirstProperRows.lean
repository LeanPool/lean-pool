/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AncestorOdometerInnerSupportNormalization
public import LeanPool.ApollonianSuperharmonic.BandCircleEuclideanData
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandVectorOrientationDichotomy
public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryPlacement
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.RecursiveVectorSystem
public import LeanPool.ApollonianSuperharmonic.RecursiveVectorsExistUnique
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TilingLattice
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientationUnique
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.VectorSquareProduct

-- [TABLET NODE: P4458T1FirstProperRows]

/-!
# P4458T1FirstProperRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FirstProperRowProof

private theorem properGt :
    (by
      classical
      exact
        ∀ q : Fin 4 → CircleCoordinates, ProperBandQuadruple q → 1 < (q 0).1 ) := by
  classical
  intro q hq
  have hf := ProperBandCurvatureStructure q hq
  by_contra hn
  have hz : ∀ i : Fin 3, (q i.succ).1 = 0 := by
    intro i
    have hnonneg := hf.2.1 i
    have hbelow := hq.2 i
    omega
  exact (by decide : (0 : Fin 3) ≠ 1) (hf.2.2 0 1 (hz 0) (hz 1))

private theorem forestRows :
    (by
      classical
      exact
        (BandCircle) → (
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let L := fun z : GaussianInt =>
          ![((4 : ℤ), 1 + 8 * z + 4 * I),
            (1, 1 + 2 * z), (0, -1), (1, 1 + 2 * z + 2 * I)]
        let R := fun z : GaussianInt =>
          ![((4 : ℤ), 7 + 8 * z + 4 * I),
            (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * I), (0, 1)]
        (∀ q : Fin 4 → CircleCoordinates, ProperBandQuadruple q → 1 < (q 0).1) → ((∀ (q : Fin 4 →
            CircleCoordinates), ∀ (i : Fin 3), ∀ (j : Fin 3), cyc (cyc q i) j = cyc q (i + j)) →
                (∀ q
            : Fin 4 → CircleCoordinates, SemiProperQuadruple q → ProperBandQuadruple q → (∀ j : Fin
            3, (q j.succ).1 ≤ 1) → ∃ z : GaussianInt, ∃ k : Fin 3, q = cyc (L z) k ∨ q = cyc (R z)
            k))) ) := by
  classical
  intro C I cyc L R properGt cycCyc q hq
  induction hq with
  | base z =>
      intro hp hs
      have h := hp.2 0
      norm_num at h
  | @rotate q hq ih =>
      intro hp hs
      have hp' : ProperBandQuadruple q := by
        refine ⟨hq, ?_⟩
        intro j
        fin_cases j
        · exact hp.2 2
        · exact hp.2 0
        · exact hp.2 1
      have hs' : ∀ j : Fin 3, (q j.succ).1 ≤ 1 := by
        intro j
        fin_cases j
        · exact hs 2
        · exact hs 0
        · exact hs 1
      rcases ih hp' hs' with ⟨z, k, heq | heq⟩
      · refine ⟨z, k + 1, Or.inl ?_⟩
        change cyc q 1 = _
        rw [heq, cycCyc]
      · refine ⟨z, k + 1, Or.inr ?_⟩
        change cyc q 1 = _
        rw [heq, cycCyc]
  | @successor q hq ih =>
      intro hp hs
      rcases (SemiProperForestClassification q hq).2 with
        ⟨z, heq⟩ | ⟨z, heq⟩ | ⟨z, heq⟩ | hp'
      · have h := hp.2 0
        rw [heq] at h
        change (1 : ℤ) < 1 at h
        omega
      · refine ⟨z, 0, Or.inl ?_⟩
        rw [heq]
        funext j
        fin_cases j <;> simp [cyc, L, I]; ring
      · refine ⟨z, 0, Or.inr ?_⟩
        rw [heq]
        funext j
        fin_cases j <;> simp [cyc, R, I]; ring
      · exact (not_le_of_gt (properGt q hp') (hs 0)).elim

private theorem hrAt221 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        ProperBandQuadruple r ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F cyc r
  have rot : ∀ i : Fin 3, ProperBandQuadruple (cyc F.q i) := by
    intro i
    fin_cases i
    · convert F.proper using 1; funext j; fin_cases j <;> rfl
    · refine ⟨SemiProperQuadruple.rotate F.proper.1, ?_⟩
      intro j
      fin_cases j
      · simpa [cyc] using F.proper.2 1
      · simpa [cyc] using F.proper.2 2
      · simpa [cyc] using F.proper.2 0
    · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate F.proper.1), ?_⟩
      intro j
      fin_cases j
      · simpa [cyc] using F.proper.2 2
      · simpa [cyc] using F.proper.2 0
      · simpa [cyc] using F.proper.2 1
  exact rot F.slot

private theorem rotateChart :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        ∀ (i : Fin 3), ∀ (o : Bool), UnitOccurrenceOrientation F.q i o → UnitOccurrenceOrientation
            (cyc F.q i) 0 o ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F cyc i o h
  fin_cases i
  · convert h using 1
    · funext j
      fin_cases j <;> rfl
    · rfl
  · exact UnitOccurrenceOrientation.rotate h
  · exact UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rotate h)

private theorem rootValues :
    (by
      classical
      exact
        (BandCircle) → (
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (z : GaussianInt),
        let q := ![((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z), ((1 :
            ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩),
            ((0 : ℤ), (1 : GaussianInt)), ((0 : ℤ), (-1 : GaussianInt))]; BandVectors.1 (q (3 : Fin
            (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (q (2 : Fin (4 :
                ℕ)))
            (q (1 : Fin (4 : ℕ))) = (-1 : GaussianInt) ∧ BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 :
            Fin (4 : ℕ))) = (1 : GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 :
            ℕ))) = (1 : GaussianInt) ∧ BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) =
            (-1 : GaussianInt) - z - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q
                (3 :
            Fin (4 : ℕ))) = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (q : Fin (4 : ℕ) → CircleCoordinates),
                SemiProperQuadruple q → BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) =
            BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
            BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧ BandVectors.1 (q (0 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) = BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))
            + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧
            BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) = BandVectors.2 (q (2 : Fin (4
            : ℕ))) (q (1 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (q (3 : Fin (4 : ℕ)))
            (q (2 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) =
            BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
            BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → ((∀ (C :
                CircleCoordinates), ∀ (D : CircleCoordinates), PrimitiveVectorOrientation C D →
                BandVectors.1 D C = ⟨(0 :
                ℤ),
            (1 : ℤ)⟩ * BandVectors.1 C D ∧ BandVectors.2 D C = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 C
            D) → (∀ (z : GaussianInt),
        let U : CircleCoordinates := (1, 1 + 2 * z)
          let H : CircleCoordinates := (1, 1 + 2 * z + 2 * I)
          BandVectors.1 (0, -1) U = -I ∧
          BandVectors.2 (0, -1) U = I * z ∧
          BandVectors.1 U H = -1 + I ∧
          BandVectors.2 U H = -z - I - I * z ∧
          BandVectors.1 H (0, -1) = 1 ∧
          BandVectors.2 H (0, -1) = z + I ∧
          BandVectors.1 H U = 1 + I ∧
          BandVectors.2 H U = 1 + z - I * z ∧
          BandVectors.1 U (0, 1) = -I ∧
          BandVectors.2 U (0, 1) = I + I * z ∧
          BandVectors.1 (0, 1) H = -1 ∧
          BandVectors.2 (0, 1) H = -1 - z - I)))) ) := by
  classical
  intro C I baseLaw stepLaw flipLaw z
  let b : Fin 4 → CircleCoordinates :=
    ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * I), (0, 1), (0, -1)]
  have hb : SemiProperQuadruple b := SemiProperQuadruple.base z
  have hb0 := baseLaw z
  change BandVectors.1 (b 3) (b 2) = 0 ∧
    BandVectors.1 (b 2) (b 1) = -1 ∧
    BandVectors.1 (b 1) (b 3) = 1 ∧
    BandVectors.2 (b 3) (b 2) = 1 ∧
    BandVectors.2 (b 2) (b 1) = -1 - z - I ∧
    BandVectors.2 (b 1) (b 3) = z + I at hb0
  rcases hb0 with ⟨v32, v21, v13, a32, a21, a13⟩
  have step := stepLaw b hb
  have vv20 : BandVectors.1 (b 2) (b 0) = -1 := by
    rw [step.1, v21, v32]; ring
  have aa20 : BandVectors.2 (b 2) (b 0) = -1 - z := by
    rw [step.2.2.1, a21, a32]; ring
  have vv03 : BandVectors.1 (b 0) (b 3) = 1 := by
    rw [step.2.1, v13, v32]; ring
  have aa03 : BandVectors.2 (b 0) (b 3) = z := by
    rw [step.2.2.2, a13, a32]; ring
  have hminus : PrimitiveVectorOrientation (b 3) (b 0) := by
    have h := PrimitiveVectorOrientation.base31 (z - I)
    convert h using 1 <;> simp [b, I]; ring
  have hplus : PrimitiveVectorOrientation (b 2) (b 0) := by
    have h := PrimitiveVectorOrientation.base21 (z - I)
    convert h using 1 <;> simp [b, I]; ring
  have fm := flipLaw _ _ hminus
  have fp := flipLaw _ _ hplus
  have f01 := flipLaw _ _ (PrimitiveVectorOrientation.base10 z)
  have h10 := (VectorRecursionLaws b hb).2.2.1
  have ha10 := (VectorRecursionLaws b hb).2.2.2.1
  change BandVectors.1 (b 0) (b 1) = I * BandVectors.1 (b 1) (b 0) ∧
    BandVectors.2 (b 0) (b 1) = -I * BandVectors.2 (b 1) (b 0) at f01
  have vv10 : BandVectors.1 (b 1) (b 0) = 1 + I := by
    rw [h10, v13, v21]; ring
  have aa10 : BandVectors.2 (b 1) (b 0) = 1 + z - I * z := by
    rw [ha10, a13, a21]
    apply Zsqrtd.ext <;> norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  have vv30 : BandVectors.1 (b 3) (b 0) = -I := by
    have h := fm.1
    rw [vv03] at h
    have hr := congrArg Zsqrtd.re h
    have hi := congrArg Zsqrtd.im h
    apply Zsqrtd.ext <;> norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hr hi ⊢ <;> omega
  have aa30 : BandVectors.2 (b 3) (b 0) = I * z := by
    have h := fm.2
    rw [aa03] at h
    have hr := congrArg Zsqrtd.re h
    have hi := congrArg Zsqrtd.im h
    apply Zsqrtd.ext <;> norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hr hi ⊢ <;> omega
  have vv01 : BandVectors.1 (b 0) (b 1) = -1 + I := by
    rw [f01.1, vv10]
    apply Zsqrtd.ext <;> norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have aa01 : BandVectors.2 (b 0) (b 1) = -z - I - I * z := by
    rw [f01.2, aa10]
    apply Zsqrtd.ext <;> norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  have vv02 : BandVectors.1 (b 0) (b 2) = -I := by
    rw [fp.1, vv20]; ring
  have aa02 : BandVectors.2 (b 0) (b 2) = I + I * z := by
    rw [fp.2, aa20]; ring
  exact ⟨vv30, aa30, vv01, aa01, v13, a13, vv10, aa10,
    vv02, aa02, v21, a21⟩

private theorem htable :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let L := fun z : GaussianInt =>
          ![((4 : ℤ), 1 + 8 * z + 4 * I),
            (1, 1 + 2 * z), (0, -1), (1, 1 + 2 * z + 2 * I)]
        let R := fun z : GaussianInt =>
          ![((4 : ℤ), 7 + 8 * z + 4 * I),
            (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * I), (0, 1)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        (r 1 = C.1.1) → (∀ (z : GaussianInt), (r = L z ∧ orientation = true ∨ r = cyc (L z) (2 : Fin
            (3 : ℕ)) ∧ orientation = false ∨ r = R z ∧ orientation = true ∨ r = cyc (R z) (1 :
                Fin (3
            : ℕ)) ∧ orientation = false) → ((∀ (z : GaussianInt),
        let U : CircleCoordinates := (1, 1 + 2 * z)
          let H : CircleCoordinates := (1, 1 + 2 * z + 2 * I)
          BandVectors.1 (0, -1) U = -I ∧
          BandVectors.2 (0, -1) U = I * z ∧
          BandVectors.1 U H = -1 + I ∧
          BandVectors.2 U H = -z - I - I * z ∧
          BandVectors.1 H (0, -1) = 1 ∧
          BandVectors.2 H (0, -1) = z + I ∧
          BandVectors.1 H U = 1 + I ∧
          BandVectors.2 H U = 1 + z - I * z ∧
          BandVectors.1 U (0, 1) = -I ∧
          BandVectors.2 U (0, 1) = I + I * z ∧
          BandVectors.1 (0, 1) H = -1 ∧
          BandVectors.2 (0, 1) H = -1 - z - I) → (
        let x := BandVectors.1 (r 1) (r 3)
        let y := BandVectors.1 (r 2) (r 1)
        let xa := BandVectors.2 (r 1) (r 3)
        let ya := BandVectors.2 (r 2) (r 1)
        let Row := fun (e : Bool) (y d ya da : GaussianInt) =>
            UnitTriangularStep e y ∧
            UnitTriangularStep e d ∧
            y ≠ 0 ∧ d ≠ 0 ∧
            (ya.re : ℝ) = CircleMatrix C 0 0 * y.re + CircleMatrix C 0 1 * y.im ∧
            (ya.im : ℝ) = CircleMatrix C 1 0 * y.re + CircleMatrix C 1 1 * y.im ∧
            (da.re : ℝ) = CircleMatrix C 0 0 * d.re + CircleMatrix C 0 1 * d.im ∧
            (da.im : ℝ) = CircleMatrix C 1 0 * d.re + CircleMatrix C 1 1 * d.im
        Row orientation y (I * x) ya (-I * xa)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F I cyc L R r hcr z hrows rootValues x y xa
      ya Row
  rcases rootValues z with ⟨v30, a30, v01, a01, v13, a13,
    v10, a10, v02, a02, v21, a21⟩
  rcases hrows with ⟨hr, ho⟩ | ⟨hr, ho⟩ | ⟨hr, ho⟩ | ⟨hr, ho⟩
  all_goals
    change r = _ at hr
    have hraw := hcr.symm
    rw [hr] at hraw
    dsimp [cyc, L, R] at hraw
    dsimp only [y, x, ya, xa]
    rw [hr, ho]
  · change Row true
      (BandVectors.1 (0, -1) (1, 1 + 2 * z))
      (I * BandVectors.1 (1, 1 + 2 * z) (1, 1 + 2 * z + 2 * I))
      (BandVectors.2 (0, -1) (1, 1 + 2 * z))
      (-I * BandVectors.2 (1, 1 + 2 * z) (1, 1 + 2 * z + 2 * I))
    rw [v30, v01, a30, a01]
    dsimp only [Row]
    norm_num [UnitTriangularStep, CircleMatrix, BandCircleEuclideanData,
      hraw, I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul,
      GaussianInt.toComplex_def, -GaussianInt.intCast_re, -GaussianInt.intCast_im]
    all_goals repeat' constructor
    all_goals ring
  · change Row false
      (BandVectors.1 (1, 1 + 2 * z) (1, 1 + 2 * z + 2 * I))
      (I * BandVectors.1 (1, 1 + 2 * z + 2 * I) (0, -1))
      (BandVectors.2 (1, 1 + 2 * z) (1, 1 + 2 * z + 2 * I))
      (-I * BandVectors.2 (1, 1 + 2 * z + 2 * I) (0, -1))
    rw [v01, v13, a01, a13]
    dsimp only [Row]
    norm_num [UnitTriangularStep, CircleMatrix, BandCircleEuclideanData,
      hraw, I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul,
      GaussianInt.toComplex_def, -GaussianInt.intCast_re, -GaussianInt.intCast_im]
    all_goals repeat' constructor
    all_goals ring
  · change Row true
      (BandVectors.1 (1, 1 + 2 * z + 2 * I) (1, 1 + 2 * z))
      (I * BandVectors.1 (1, 1 + 2 * z) (0, 1))
      (BandVectors.2 (1, 1 + 2 * z + 2 * I) (1, 1 + 2 * z))
      (-I * BandVectors.2 (1, 1 + 2 * z) (0, 1))
    rw [v10, v02, a10, a02]
    dsimp only [Row]
    norm_num [UnitTriangularStep, CircleMatrix, BandCircleEuclideanData,
      hraw, I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul,
      GaussianInt.toComplex_def, -GaussianInt.intCast_re, -GaussianInt.intCast_im]
    all_goals repeat' constructor
    all_goals ring
  · change Row false
      (BandVectors.1 (0, 1) (1, 1 + 2 * z + 2 * I))
      (I * BandVectors.1 (1, 1 + 2 * z + 2 * I) (1, 1 + 2 * z))
      (BandVectors.2 (0, 1) (1, 1 + 2 * z + 2 * I))
      (-I * BandVectors.2 (1, 1 + 2 * z + 2 * I) (1, 1 + 2 * z))
    rw [v21, v10, a21, a10]
    dsimp only [Row]
    norm_num [UnitTriangularStep, CircleMatrix, BandCircleEuclideanData,
      hraw, I, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul,
      GaussianInt.toComplex_def, -GaussianInt.intCast_re, -GaussianInt.intCast_im]
    all_goals repeat' constructor
    all_goals ring

private theorem hjoinAncestor :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let y := BandVectors.1 (r 2) (r 1)
        (0 < (F.q F.slot.succ).1) → (∀ (u : GaussianInt),
        let join := TileTranslation base (u + y)
        (BandPrototile C.1.1 join) → (((D.tiles F.slot false).cells = join.cells ∧ ((D.tiles F.slot
            false).cells = ∅ → (D.tiles F.slot false).anchor = join.anchor)) → (AncestorOdometer
            C.1.1 F.outer.1.1 join F.tile (D.functions F.slot false) F.odometer))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D cyc r y hCpositive u join hjoinBand
      hjoinCells
  have hstrict : (F.q F.slot.succ).1 < F.outer.1.1.1 := by
    rw [← F.child]
    exact F.proper.2 F.slot
  have h := AncestorOdometerInnerSupportNormalization
    (F.q F.slot.succ) F.outer.1.1 (D.tiles F.slot false) join F.tile
    (D.functions F.slot false) F.odometer hCpositive hstrict
    (D.ancestors F.slot false hCpositive)
    (by rw [F.parent]; exact hjoinBand) hjoinCells.1
  simpa only [F.parent] using h

private theorem hSlopeInfo :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let wa := BandVectors.2 (r 3) (r 2)
        (0 < (F.q F.slot.succ).1) → (∃ root child : ℝ × ℝ, PartialOdometerSlope F.odometer = some
            root ∧ PartialOdometerSlope (D.functions F.slot false) = some child ∧ child.1 - root.1 =
            -(1 / 2 : ℝ) * ((wa.re : ℝ) - (wa.im : ℝ)) ∧ child.2 - root.2 = -(1 / 2 : ℝ) * ((wa.im :
            ℝ) + (wa.re : ℝ))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D cyc r wa hCpositive
  rcases D.slopes F.slot false with hz | ⟨root, child, hroot, hchild, hre, him⟩
  · omega
  · refine ⟨root, child, hroot, hchild, ?_, ?_⟩
    · simpa [r, cyc, wa] using hre
    · simpa [r, cyc, wa] using him

private theorem pairString :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer),
            (P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) → ((C.1.1.1 = 1) →
            ((Function.Injective GaussianRealPoint) → (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (d
                : GaussianInt), U ∈ RegularTileFamily base (TilingLattice C) → V ∈
                RegularTileFamily base
            (TilingLattice C) → UnitTriangularStep orientation d → d ≠ (0 : GaussianInt) →
            TileCentroid V - TileCentroid U = GaussianRealPoint d → TileString C orientation base
                U V
            [U, V]))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F hunit pointInjective U V d hU hV hstep hne
      hcenter
  have hUV : U ≠ V := by
    intro heq
    have hzero : GaussianRealPoint d = GaussianRealPoint 0 := by
      rw [← hcenter, heq]
      simp [GaussianRealPoint]
      rfl
    exact hne (pointInjective hzero)
  refine ⟨F.base_band, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using hUV
  · intro T hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact hU
    · have heq : T = V := by simpa using hT
      simpa [heq] using hV
  · apply List.isChain_pair.mpr
    rw [ite_eq_left hunit]
    exact ⟨d, hstep, hcenter⟩
  · intro pre T post heq hpre hpost
    have hlen := congrArg List.length heq
    have hp : 1 ≤ pre.length := by
      cases pre with
      | nil => simp at hpre
      | cons x xs => simp
    have hq : 1 ≤ post.length := by
      cases post with
      | nil => simp at hpost
      | cons x xs => simp
    simp at hlen
    omega

end FirstProperRowProof

namespace FirstProperRowDetails

private theorem small :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ((F.q (1 :
            Fin (4 : ℕ))).1 = (1 : ℤ) ∧ (F.q (2 : Fin (4 : ℕ))).1 = (0 : ℤ) ∧ (F.q (3 : Fin (4 :
            ℕ))).1 = (1 : ℤ) ∨ (F.q (1 : Fin (4 : ℕ))).1 = (1 : ℤ) ∧ (F.q (2 : Fin (4 : ℕ))).1 =
            (1 : ℤ) ∧ (F.q (3 : Fin (4 : ℕ))).1 = (0 : ℤ) ∨ (F.q (1 : Fin (4 : ℕ))).1 = (0 : ℤ) ∧
            (F.q (2 : Fin (4 : ℕ))).1 = (1 : ℤ) ∧ (F.q (3 : Fin (4 : ℕ))).1 = (1 : ℤ)) → (∀ i :
            Fin 3, (F.q i.succ).1 ≤ 1) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F hroot i
  fin_cases i <;> rcases hroot with h | h | h <;> simp_all

private theorem hunit :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), (∀ i : Fin
            3, (F.q i.succ).1 ≤ 1) → (C.1.1.1 = 1) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F small
  have hpos := C.2
  have hle := small F.slot
  rw [F.parent] at hle
  omega

private theorem cycCyc :
    (by
      classical
      exact
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), cyc
            (cyc q i) j = cyc q (i + j) ) := by
  classical
  intro cyc q i j
  fin_cases i <;> fin_cases j <;> funext k <;> fin_cases k <;> rfl

private theorem chartEq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        (C.1.1.1 = 1) → (
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        (ProperBandQuadruple r) → ((r 1 = C.1.1) → ((∀ (i : Fin 3), ∀ (o : Bool),
            UnitOccurrenceOrientation F.q i o → UnitOccurrenceOrientation (cyc F.q i) 0 o) → (∀
            (e : Bool), UnitOccurrenceOrientation r (0 : Fin (3 : ℕ)) e → orientation = e)))) )
            := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F cyc hunit r hr hcr rotateChart e hc
  have hu : (r (0 : Fin 3).succ).1 = 1 := by
    change (r 1).1 = 1
    rw [hcr]
    exact hunit
  exact (UnitOccurrenceOrientationUnique.1 r hr 0 hu).unique
    (rotateChart F.slot orientation (F.chart hunit)) hc

private theorem hr'At615 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let L := fun z : GaussianInt =>
          ![((4 : ℤ), 1 + 8 * z + 4 * I),
            (1, 1 + 2 * z), (0, -1), (1, 1 + 2 * z + 2 * I)]
        (∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (j : Fin 3), cyc (cyc q i) j = cyc q
            (i + j)) → (
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        ∀ (z : GaussianInt), ∀ (k : Fin (3 : ℕ)), (F.q = cyc (L z) k) → (r = cyc (L z) (k +
            F.slot))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F I cyc L cycCyc r z k heq
  dsimp only [r]
  rw [heq, cycCyc]

private theorem hr'At633 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let R := fun z : GaussianInt =>
          ![((4 : ℤ), 7 + 8 * z + 4 * I),
            (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * I), (0, 1)]
        (∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (j : Fin 3), cyc (cyc q i) j = cyc q
            (i + j)) → (
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        ∀ (z : GaussianInt), ∀ (k : Fin (3 : ℕ)), (F.q = cyc (R z) k) → (r = cyc (R z) (k +
            F.slot))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F I cyc R cycCyc r z k heq
  dsimp only [r]
  rw [heq, cycCyc]

private theorem hw :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        (ProperBandQuadruple r) → (
        let x := BandVectors.1 (r 1) (r 3)
        let y := BandVectors.1 (r 2) (r 1)
        let w := BandVectors.1 (r 3) (r 2)
        w = -x - y) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F cyc r hr x y w
  have h : w + x + y = 0 := (VectorRecursionLaws r hr.1).1
  linear_combination h

private theorem hwa :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        (ProperBandQuadruple r) → (
        let xa := BandVectors.2 (r 1) (r 3)
        let ya := BandVectors.2 (r 2) (r 1)
        let wa := BandVectors.2 (r 3) (r 2)
        wa = -xa - ya) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F cyc r hr xa ya wa
  have h : wa + xa + ya = 0 := (VectorRecursionLaws r hr.1).2.1
  linear_combination h

private theorem hCpositive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), 0 < (F.q
            F.slot.succ).1 ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F
  rw [F.parent]
  exact C.2

private theorem hUcenter :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let w := BandVectors.1 (r 3) (r 2)
        (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then (1 :
            ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2
            : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) → (TileCentroid (D.tiles
            F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D cyc r w hUcent
  simpa [r, cyc, w] using hUcent

private theorem hcenter :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let x := BandVectors.1 (r 1) (r 3)
        let y := BandVectors.1 (r 2) (r 1)
        let w := BandVectors.1 (r 3) (r 2)
        (w = -x - y) → ((BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 0) (r 1) = I
            * BandVectors.1 (r 1) (r 0)) → ((TileCentroid (D.tiles F.slot false) - TileCentroid
            F.tile = -(1 / 2 : ℝ) • (GaussianRealPoint w - (-(GaussianRealPoint w).2,
            (GaussianRealPoint w).1))) → ((TileCentroid Rminus - TileCentroid F.tile = (1 / 2 :
            ℝ) • GaussianRealPoint (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1))) →
            (TileCentroid (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y)))))
            ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D I cyc r x y w hw hvrec hvflip hUcenter
      hMcenter
  rw [show TileCentroid (D.tiles F.slot false) - TileCentroid Rminus =
    (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile) -
      (TileCentroid Rminus - TileCentroid F.tile) by abel]
  rw [hUcenter, hMcenter, hvflip, hvrec, hw]
  apply Prod.ext <;>
    norm_num [GaussianRealPoint, I, Prod.smul_mk,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring

private theorem hplusCenter :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let x := BandVectors.1 (r 1) (r 3)
        let y := BandVectors.1 (r 2) (r 1)
        let w := BandVectors.1 (r 3) (r 2)
        (w = -x - y) → ((BandVectors.1 (r 1) (r 0) = x - I * y) → ((BandVectors.1 (r 0) (r 1) = I
            * BandVectors.1 (r 1) (r 0)) → ((TileCentroid (D.tiles F.slot false) - TileCentroid
            F.tile = -(1 / 2 : ℝ) • (GaussianRealPoint w - (-(GaussianRealPoint w).2,
            (GaussianRealPoint w).1))) → ((TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ)
            • GaussianRealPoint (BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1))) →
            (TileCentroid Rplus - TileCentroid (D.tiles F.slot false) = GaussianRealPoint (I *
            x)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D I cyc r x y w hw hvrec hvflip hUcenter
      hPcenter
  rw [show TileCentroid Rplus - TileCentroid (D.tiles F.slot false) =
    (TileCentroid Rplus - TileCentroid F.tile) -
      (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile) by abel]
  rw [hPcenter, hUcenter, hvflip, hvrec, hw]
  apply Prod.ext <;>
    norm_num [GaussianRealPoint, I, Prod.smul_mk,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring

private theorem hjoinCenter :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let y := BandVectors.1 (r 2) (r 1)
        ∀ (u : GaussianInt), (Rminus = TileTranslation base u) → (
        let join := TileTranslation base (u + y)
        TileCentroid join - TileCentroid Rminus = GaussianRealPoint y) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F cyc r y u hminusTrans join
  rw [hminusTrans]
  change TileCentroid (TileTranslation base (u + y)) -
    TileCentroid (TileTranslation base u) = _
  rw [(TileTranslationFormulas base (u + y)).2.2.2.2.1,
    (TileTranslationFormulas base u).2.2.2.2.1]
  apply Prod.ext <;>
    norm_num [GaussianRealPoint, -GaussianInt.intCast_re, -GaussianInt.intCast_im]

private theorem hjoinCenterEq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let y := BandVectors.1 (r 2) (r 1)
        (TileCentroid (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y) → (∀ (u
            : GaussianInt),
        let join := TileTranslation base (u + y)
        (TileCentroid join - TileCentroid Rminus = GaussianRealPoint y) → (TileCentroid (D.tiles
            F.slot false) = TileCentroid join)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D cyc r y hcenter u join hjoinCenter
  have h := hcenter.trans hjoinCenter.symm
  simpa using congrArg (fun p : ℝ × ℝ => p + TileCentroid Rminus) h

private theorem hUbandC :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), (BandPrototile (F.q F.slot.succ) (D.tiles F.slot
            false)) → (BandPrototile C.1.1 (D.tiles F.slot false)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hUband
  rw [← F.parent]
  exact hUband

private theorem hjoinFoot :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let y := BandVectors.1 (r 2) (r 1)
        ∀ (u : GaussianInt),
        let join := TileTranslation base (u + y)
        (AncestorOdometer C.1.1 F.outer.1.1 join F.tile (D.functions F.slot false) F.odometer) →
            (FootprintVertices join ⊆ FootprintVertices F.tile) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D cyc r y u join hjoinAncestor
  rw [← hjoinAncestor.2.2.1,
    ← PositiveCurvatureTileOdometerDomain F.outer.1.1 F.tile F.odometer
      F.outer.2 F.outer_odo]
  exact hjoinAncestor.2.2.2.1

private theorem hjoinOccurrence :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let y := BandVectors.1 (r 2) (r 1)
        (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then (1 :
            ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2
            : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (u : GaussianInt),
        let join := TileTranslation base (u + y)
        (BandPrototile C.1.1 join) → ((TileCentroid (D.tiles F.slot false) = TileCentroid join) →
            ((FootprintVertices join ⊆ FootprintVertices F.tile) → (BandSubtileOccurrence F.q
            F.tile F.slot false join)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D cyc r y hUcent u join hjoinBand
      hjoinCenterEq hjoinFoot
  refine ⟨by rw [F.parent]; exact hjoinBand, hjoinFoot, ?_⟩
  rw [← hjoinCenterEq]
  exact hUcent

private theorem hDoffset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let wa := BandVectors.2 (r 3) (r 2)
        ∀ (joinSlope : ℝ × ℝ), (joinSlope.1 - F.outer_slope.1 = -(1 / 2 : ℝ) * ((↑wa.re : ℝ) -
            (↑wa.im : ℝ))) → ((joinSlope.2 - F.outer_slope.2 = -(1 / 2 : ℝ) * ((↑wa.im : ℝ) +
            (↑wa.re : ℝ))) → (joinSlope - F.outer_slope = -(1 / 2 : ℝ) • GaussianRealPoint ((1 +
            I) * wa))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F I cyc r wa joinSlope hre him
  apply Prod.ext
  · norm_num [GaussianRealPoint, I, Prod.smul_mk,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im]
    linarith [hre]
  · norm_num [GaussianRealPoint, I, Prod.smul_mk,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im]
    linarith [him]

private theorem hminusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let xa := BandVectors.2 (r 1) (r 3)
        let ya := BandVectors.2 (r 2) (r 1)
        let wa := BandVectors.2 (r 3) (r 2)
        (wa = -xa - ya) → ((BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((BandVectors.2 (r 0) (r
            1) = -I * BandVectors.2 (r 1) (r 0)) → (∀ (joinSlope : ℝ × ℝ), (joinSlope -
            F.outer_slope = -(1 / 2 : ℝ) • GaussianRealPoint ((1 + I) * wa)) → ((F.minus_slope -
            F.outer_slope = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (r 1) (r 0) -
            BandVectors.2 (r 0) (r 1))) → (joinSlope - F.minus_slope = GaussianRealPoint ya)))))
            ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F I cyc r xa ya wa hwa harec haflip
      joinSlope hDoffset hFminus
  rw [show joinSlope - F.minus_slope =
    (joinSlope - F.outer_slope) - (F.minus_slope - F.outer_slope) by abel]
  rw [hDoffset, hFminus, haflip, harec, hwa]
  apply Prod.ext <;>
    norm_num [GaussianRealPoint, I, Prod.smul_mk,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring

private theorem hplusSlope :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let xa := BandVectors.2 (r 1) (r 3)
        let ya := BandVectors.2 (r 2) (r 1)
        let wa := BandVectors.2 (r 3) (r 2)
        (wa = -xa - ya) → ((BandVectors.2 (r 1) (r 0) = xa + I * ya) → ((BandVectors.2 (r 0) (r
            1) = -I * BandVectors.2 (r 1) (r 0)) → (∀ (joinSlope : ℝ × ℝ), (joinSlope -
            F.outer_slope = -(1 / 2 : ℝ) • GaussianRealPoint ((1 + I) * wa)) → ((F.plus_slope -
            F.outer_slope = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (r 1) (r 0) +
            BandVectors.2 (r 0) (r 1))) → (F.plus_slope - joinSlope = GaussianRealPoint (-I *
            xa)))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F I cyc r xa ya wa hwa harec haflip
      joinSlope hDoffset hFplus
  rw [show F.plus_slope - joinSlope =
    (F.plus_slope - F.outer_slope) - (joinSlope - F.outer_slope) by abel]
  rw [hFplus, hDoffset, haflip, harec, hwa]
  apply Prod.ext <;>
    norm_num [GaussianRealPoint, I, Prod.smul_mk,
      -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring

private theorem hleftAdjacent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        (C.1.1.1 = 1) → (
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let y := BandVectors.1 (r 2) (r 1)
        let ya := BandVectors.2 (r 2) (r 1)
        (UnitTriangularStep orientation y) → (((↑ya.re : ℝ) = CircleMatrix C (0 : Fin (2 : ℕ)) (0
            : Fin (2 : ℕ)) * (↑y.re : ℝ) + CircleMatrix C (0 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) *
            (↑y.im : ℝ)) → (((↑ya.im : ℝ) = CircleMatrix C (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) *
            (↑y.re : ℝ) + CircleMatrix C (1 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) * (↑y.im : ℝ)) → (∀
            (u : GaussianInt),
        let join := TileTranslation base (u + y)
        (TileCentroid join - TileCentroid Rminus = GaussianRealPoint y) → ((TileOdometer C.1.1
            join (D.functions F.slot false)) → (∀ (joinSlope : ℝ × ℝ), (PartialOdometerSlope
            (D.functions F.slot false) = some joinSlope) → ((joinSlope - F.minus_slope =
            GaussianRealPoint ya) → (LeftLatticeAdjacent C Rminus join hminus (D.functions F.slot
            false))))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D cyc hunit r y ya hyStep hyRe hyIm u join
      hjoinCenter hjoinOdo joinSlope hjoinSlope hminusSlope
  refine ⟨F.minus_odo, hjoinOdo, F.minus_slope, joinSlope,
    F.slope_minus, hjoinSlope, Or.inl ⟨hunit, orientation, y, hyStep, hjoinCenter, ?_, ?_⟩⟩
  · rw [← hyRe]
    exact congrArg Prod.fst hminusSlope
  · rw [← hyIm]
    exact congrArg Prod.snd hminusSlope

private theorem hrightAdjacent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let I : GaussianInt := ⟨0, 1⟩
        let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
          ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
        (C.1.1.1 = 1) → (
        let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
        let x := BandVectors.1 (r 1) (r 3)
        let y := BandVectors.1 (r 2) (r 1)
        let xa := BandVectors.2 (r 1) (r 3)
        (UnitTriangularStep orientation (I * x)) → (((↑(-I * xa).re : ℝ) = CircleMatrix C (0 :
            Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * (↑(I * x).re : ℝ) + CircleMatrix C (0 : Fin (2 : ℕ))
            (1 : Fin (2 : ℕ)) * (↑(I * x).im : ℝ)) → (((↑(-I * xa).im : ℝ) = CircleMatrix C (1 :
            Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * (↑(I * x).re : ℝ) + CircleMatrix C (1 : Fin (2 : ℕ))
            (1 : Fin (2 : ℕ)) * (↑(I * x).im : ℝ)) → (∀ (u : GaussianInt),
        let join := TileTranslation base (u + y)
        (TileOdometer C.1.1 join (D.functions F.slot false)) → ((TileCentroid Rplus -
            TileCentroid join = GaussianRealPoint (I * x)) → (∀ (joinSlope : ℝ × ℝ),
            (PartialOdometerSlope (D.functions F.slot false) = some joinSlope) → ((F.plus_slope -
            joinSlope = GaussianRealPoint (-I * xa)) → (LeftLatticeAdjacent C join Rplus
            (D.functions F.slot false) hplus)))))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D I cyc hunit r x y xa hxStep hxRe hxIm u
      join hjoinOdo hrightCenter joinSlope hjoinSlope hplusSlope
  refine ⟨hjoinOdo, F.plus_odo, joinSlope, F.plus_slope,
    hjoinSlope, F.slope_plus, Or.inl ⟨hunit, orientation, I * x, hxStep, hrightCenter, ?_, ?_⟩⟩
  · rw [← hxRe]
    exact congrArg Prod.fst hplusSlope
  · rw [← hxIm]
    exact congrArg Prod.snd hplusSlope

private theorem pointInjective :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro a b hab
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hab
    change (a.re : ℝ) = (b.re : ℝ) at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hab
    change (a.im : ℝ) = (b.im : ℝ) at h
    exact_mod_cast h

end FirstProperRowDetails

theorem P4458T1FirstProperRows
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (hroot :
      ((F.q 1).1 = 1 ∧ (F.q 2).1 = 0 ∧ (F.q 3).1 = 1) ∨
      ((F.q 1).1 = 1 ∧ (F.q 2).1 = 1 ∧ (F.q 3).1 = 0) ∨
      ((F.q 1).1 = 0 ∧ (F.q 2).1 = 1 ∧ (F.q 3).1 = 1)) :
    Nonempty (P4458T1BoundaryPlacement F D) := by
-- BODY
  classical
  let I : GaussianInt := ⟨0, 1⟩
  let cyc := fun (q : Fin 4 → CircleCoordinates) (i : Fin 3) =>
    ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
  let L := fun z : GaussianInt =>
    ![((4 : ℤ), 1 + 8 * z + 4 * I),
      (1, 1 + 2 * z), (0, -1), (1, 1 + 2 * z + 2 * I)]
  let R := fun z : GaussianInt =>
    ![((4 : ℤ), 7 + 8 * z + 4 * I),
      (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * I), (0, 1)]
  have small : ∀ i : Fin 3, (F.q i.succ).1 ≤ 1 := FirstProperRowDetails.small C orientation base
      Rminus Rplus hminus hplus F hroot
  have hunit : C.1.1.1 = 1 := FirstProperRowDetails.hunit C orientation base Rminus Rplus hminus
      hplus F small
  -- Classify the literal coordinates before comparing occurrence charts.
  have cycCyc (q : Fin 4 → CircleCoordinates) (i j : Fin 3) :
      cyc (cyc q i) j = cyc q (i + j) := FirstProperRowDetails.cycCyc q i j
  have forestRows : ∀ q : Fin 4 → CircleCoordinates,
      SemiProperQuadruple q → ProperBandQuadruple q →
      (∀ j : Fin 3, (q j.succ).1 ≤ 1) →
      ∃ z : GaussianInt, ∃ k : Fin 3,
        q = cyc (L z) k ∨ q = cyc (R z) k := FirstProperRowProof.forestRows C
            (FirstProperRowProof.properGt) cycCyc
  let r : Fin 4 → CircleCoordinates := cyc F.q F.slot
  have hr : ProperBandQuadruple r := FirstProperRowProof.hrAt221 C orientation base Rminus Rplus
      hminus hplus F
  have hcr : r 1 = C.1.1 := F.parent
  have chartEq (e : Bool) (hc : UnitOccurrenceOrientation r 0 e) : orientation = e :=
      FirstProperRowDetails.chartEq C orientation base Rminus Rplus hminus hplus F hunit hr hcr
      (FirstProperRowProof.rotateChart C orientation base Rminus Rplus hminus hplus F) e hc
  obtain ⟨z, hrows⟩ : ∃ z : GaussianInt,
      (r = L z ∧ orientation = true) ∨
      (r = cyc (L z) 2 ∧ orientation = false) ∨
      (r = R z ∧ orientation = true) ∨
      (r = cyc (R z) 1 ∧ orientation = false) := by
    rcases forestRows F.q F.proper.1 F.proper small with ⟨z, k, heq | heq⟩
    · have hr' : r = cyc (L z) (k + F.slot) := FirstProperRowDetails.hr'At615 C orientation base
        Rminus Rplus hminus hplus F cycCyc z k heq
      generalize k + F.slot = j at hr'
      fin_cases j
      · have he : r = L z := by
          convert hr' using 1; funext j; fin_cases j <;> rfl
        refine ⟨z, Or.inl ⟨he, chartEq true ?_⟩⟩
        rw [he]
        exact UnitOccurrenceOrientation.leftLower z
      · have hu : (r 1).1 = 1 := by rw [hcr]; exact hunit
        rw [hr'] at hu
        change (0 : ℤ) = 1 at hu
        omega
      · refine ⟨z, Or.inr (Or.inl ⟨hr', chartEq false ?_⟩)⟩
        rw [hr']
        exact UnitOccurrenceOrientation.rotate
          (UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.leftUpper z))
    · have hr' : r = cyc (R z) (k + F.slot) := FirstProperRowDetails.hr'At633 C orientation base
        Rminus Rplus hminus hplus F cycCyc z k heq
      generalize k + F.slot = j at hr'
      fin_cases j
      · have he : r = R z := by
          convert hr' using 1; funext j; fin_cases j <;> rfl
        refine ⟨z, Or.inr (Or.inr (Or.inl ⟨he, chartEq true ?_⟩))⟩
        rw [he]
        exact UnitOccurrenceOrientation.rightUpper z
      · refine ⟨z, Or.inr (Or.inr (Or.inr ⟨hr', chartEq false ?_⟩))⟩
        rw [hr']
        exact UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rightLower z)
      · have hu : (r 1).1 = 1 := by rw [hcr]; exact hunit
        rw [hr'] at hu
        change (0 : ℤ) = 1 at hu
        omega
  -- These directed base pairs determine all four local edge rows.
  have systemLaw : RecursiveVectorSystem BandVectors := by
    simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
  rcases systemLaw with ⟨zeroLaw, baseLaw, stepLaw, flipLaw⟩
  let x := BandVectors.1 (r 1) (r 3)
  let y := BandVectors.1 (r 2) (r 1)
  let xa := BandVectors.2 (r 1) (r 3)
  let ya := BandVectors.2 (r 2) (r 1)
  let Row := fun (e : Bool) (y d ya da : GaussianInt) =>
      UnitTriangularStep e y ∧
      UnitTriangularStep e d ∧
      y ≠ 0 ∧ d ≠ 0 ∧
      (ya.re : ℝ) = CircleMatrix C 0 0 * y.re + CircleMatrix C 0 1 * y.im ∧
      (ya.im : ℝ) = CircleMatrix C 1 0 * y.re + CircleMatrix C 1 1 * y.im ∧
      (da.re : ℝ) = CircleMatrix C 0 0 * d.re + CircleMatrix C 0 1 * d.im ∧
      (da.im : ℝ) = CircleMatrix C 1 0 * d.re + CircleMatrix C 1 1 * d.im
  have htable : Row orientation y (I * x) ya (-I * xa) := FirstProperRowProof.htable C
      orientation base Rminus Rplus hminus hplus F hcr z hrows (FirstProperRowProof.rootValues C
          baseLaw stepLaw flipLaw)
  rcases htable with ⟨hyStep, hxStep, hyNe, hxNe, hyRe, hyIm, hxRe, hxIm⟩
  -- Subtract the actual endpoint offsets from the selected negative piece.
  let w := BandVectors.1 (r 3) (r 2)
  let wa := BandVectors.2 (r 3) (r 2)
  have hw : w = -x - y := FirstProperRowDetails.hw C orientation base Rminus Rplus hminus hplus F hr
  have hwa : wa = -xa - ya := FirstProperRowDetails.hwa C orientation base Rminus Rplus hminus
      hplus F hr
  have hvrec : BandVectors.1 (r 1) (r 0) = x - I * y :=
    (VectorRecursionLaws r hr.1).2.2.1
  have harec : BandVectors.2 (r 1) (r 0) = xa + I * ya :=
    (VectorRecursionLaws r hr.1).2.2.2.1
  have hvflip : BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0) :=
    (VectorRecursionLaws r hr.1).2.2.2.2 hr 0 |>.1
  have haflip : BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0) :=
    (VectorRecursionLaws r hr.1).2.2.2.2 hr 0 |>.2
  have hCpositive : 0 < (F.q F.slot.succ).1 := FirstProperRowDetails.hCpositive C orientation
      base Rminus Rplus hminus hplus F
  rcases D.occurrences F.slot false with ⟨hUband, hUfoot, hUcent⟩
  have hUcenter : TileCentroid (D.tiles F.slot false) - TileCentroid F.tile =
      -(1 / 2 : ℝ) • (GaussianRealPoint w -
        (-(GaussianRealPoint w).2, (GaussianRealPoint w).1)) := FirstProperRowDetails.hUcenter C
            orientation base Rminus Rplus hminus hplus F D hUcent
  have hcenter : TileCentroid (D.tiles F.slot false) - TileCentroid Rminus =
      GaussianRealPoint y := FirstProperRowDetails.hcenter C orientation base Rminus Rplus hminus
          hplus F D hw hvrec hvflip hUcenter (F.minus_centroid)
  have hplusCenter : TileCentroid Rplus - TileCentroid (D.tiles F.slot false) =
      GaussianRealPoint (I * x) := FirstProperRowDetails.hplusCenter C orientation base Rminus
          Rplus hminus hplus F D hw hvrec hvflip hUcenter (F.plus_centroid)
  -- Normalize only the join support; the function and endpoints stay literal.
  obtain ⟨u, hu, hminusTrans⟩ := F.minus_family
  let join := TileTranslation base (u + y)
  have hyLattice : y ∈ TilingLattice C := by simp [TilingLattice, hunit]
  have hjoinFamily : join ∈ RegularTileFamily base (TilingLattice C) :=
    ⟨u + y, (TilingLattice C).add_mem hu hyLattice, rfl⟩
  have hjoinBand : BandPrototile C.1.1 join :=
    BandPrototileTranslation C.1.1 base (u + y) F.base_band
  have hjoinCenter : TileCentroid join - TileCentroid Rminus = GaussianRealPoint y :=
      FirstProperRowDetails.hjoinCenter C orientation base Rminus Rplus hminus hplus F u hminusTrans
  have hjoinCenterEq : TileCentroid (D.tiles F.slot false) = TileCentroid join :=
      FirstProperRowDetails.hjoinCenterEq C orientation base Rminus Rplus hminus hplus F D
      hcenter u hjoinCenter
  have hjoinCells := BandPrototileCentroidUnique C.1.1
    (D.tiles F.slot false) join (FirstProperRowDetails.hUbandC C orientation base Rminus Rplus
        hminus hplus F D hUband) hjoinBand hjoinCenterEq
  have hjoinOdo : TileOdometer C.1.1 join (D.functions F.slot false) :=
    PositiveCurvatureTileOdometerSupportTransport C.1.1
      (D.tiles F.slot false) join (D.functions F.slot false) C.2
      (by rw [← F.parent]; exact D.odometers F.slot false) hjoinBand hjoinCells.1
  have hjoinAncestor : AncestorOdometer C.1.1 F.outer.1.1
      join F.tile (D.functions F.slot false) F.odometer := FirstProperRowProof.hjoinAncestor C
          orientation base Rminus Rplus hminus hplus F D hCpositive u hjoinBand hjoinCells
  have hrightCenter : TileCentroid Rplus - TileCentroid join =
      GaussianRealPoint (I * x) := by rw [← hjoinCenterEq]; exact hplusCenter
  have hSlopeInfo : ∃ root child : ℝ × ℝ,
      PartialOdometerSlope F.odometer = some root ∧
      PartialOdometerSlope (D.functions F.slot false) = some child ∧
      child.1 - root.1 = -(1 / 2 : ℝ) * ((wa.re : ℝ) - (wa.im : ℝ)) ∧
      child.2 - root.2 = -(1 / 2 : ℝ) * ((wa.im : ℝ) + (wa.re : ℝ)) :=
          FirstProperRowProof.hSlopeInfo C orientation base Rminus Rplus hminus hplus F D hCpositive
  rcases hSlopeInfo with ⟨rootSlope, joinSlope, hrootSlope, hjoinSlope, hre, him⟩
  have hrootSlopeEq : rootSlope = F.outer_slope :=
    Option.some.inj (hrootSlope.symm.trans F.slope_outer)
  rw [hrootSlopeEq] at hre him
  have hDoffset : joinSlope - F.outer_slope =
      -(1 / 2 : ℝ) • GaussianRealPoint ((1 + I) * wa) := FirstProperRowDetails.hDoffset C
          orientation base Rminus Rplus hminus hplus F joinSlope hre him
  have pairString (U V : ProtoTile) (d : GaussianInt)
      (hU : U ∈ RegularTileFamily base (TilingLattice C))
      (hV : V ∈ RegularTileFamily base (TilingLattice C))
      (hstep : UnitTriangularStep orientation d) (hne : d ≠ 0)
      (hcenter : TileCentroid V - TileCentroid U = GaussianRealPoint d) :
      TileString C orientation base U V [U, V] := FirstProperRowProof.pairString C orientation
          base Rminus Rplus hminus hplus F hunit (FirstProperRowDetails.pointInjective) U V d hU
              hV hstep hne hcenter
  exact ⟨⟨join, hjoinCells.1.symm, hjoinOdo, hjoinAncestor,
      (FirstProperRowDetails.hjoinOccurrence C orientation base Rminus Rplus hminus hplus F D
      hUcent u hjoinBand hjoinCenterEq (FirstProperRowDetails.hjoinFoot C orientation base Rminus
      Rplus hminus hplus F D u hjoinAncestor)),
    .direct (pairString Rminus join y F.minus_family hjoinFamily hyStep hyNe hjoinCenter)
        (FirstProperRowDetails.hleftAdjacent C orientation base Rminus Rplus hminus hplus F D
            hunit hyStep hyRe hyIm u hjoinCenter hjoinOdo joinSlope hjoinSlope
            (FirstProperRowDetails.hminusSlope C orientation base Rminus Rplus hminus hplus F hwa
            harec haflip joinSlope hDoffset (F.minus_difference))),
    .direct (pairString join Rplus (I * x) hjoinFamily F.plus_family hxStep hxNe hrightCenter)
        (FirstProperRowDetails.hrightAdjacent C orientation base Rminus Rplus hminus hplus F D
            hunit hxStep hxRe hxIm u hjoinOdo hrightCenter joinSlope hjoinSlope
            (FirstProperRowDetails.hplusSlope C orientation base Rminus Rplus hminus hplus F hwa
            harec haflip joinSlope hDoffset (F.plus_difference)))⟩⟩

end ApollonianSuperharmonic

end
