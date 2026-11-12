/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3996T1SRowTable
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms

-- [TABLET NODE: P3996T1SRowAlignment]

/-!
# P3996T1SRowAlignment

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SRowAlignmentGeometry

private theorem q1pos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 1).1) )
            := by
  classical
  intro q cfg
  have h12 := cfg.order12
  have h2 := cfg.secondLarge
  omega

private theorem q2pos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 2).1) )
            := by
  classical
  intro q cfg
  have h2 := cfg.secondLarge
  omega

private theorem q3pos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 3).1) )
            := by
  classical
  intro q cfg
  have h := (ProperBandCurvatureStructure q cfg.proper).2.1 2
  exact lt_of_le_of_ne h (Ne.symm (cfg.noLine 3))

private theorem occA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (m : Int), ∀ (n : Int), BandPrototile (q 1) (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v ⟨.A, m, n⟩) ) := by
  classical
  intro q cfg C T cert m n
  simp only [SubtileOccurrenceInterpretation]
  exact BandPrototileTranslation _ _ _ (cert.outer_occurrence 0 true).1

private theorem occB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (m : Int), ∀ (n : Int), BandPrototile (q 1) (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v ⟨.B, m, n⟩) ) := by
  classical
  intro q cfg C T cert m n
  simp only [SubtileOccurrenceInterpretation]
  exact BandPrototileTranslation _ _ _ (cert.outer_occurrence 0 false).1

private theorem occC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (m : Int), ∀ (n : Int), BandPrototile (q 2) (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v ⟨.C, m, n⟩) ) := by
  classical
  intro q cfg C T cert m n
  simp only [SubtileOccurrenceInterpretation]
  exact BandPrototileTranslation _ _ _ (cert.outer_occurrence 1 true).1

private theorem occD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (m : Int), ∀ (n : Int), BandPrototile (q 2) (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v ⟨.D, m, n⟩) ) := by
  classical
  intro q cfg C T cert m n
  simp only [SubtileOccurrenceInterpretation]
  exact BandPrototileTranslation _ _ _ (cert.outer_occurrence 1 false).1

private theorem occE :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (m : Int), ∀ (n : Int), BandPrototile (q 3) (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v ⟨.E, m, n⟩) ) := by
  classical
  intro q cfg C T cert m n
  simp only [SubtileOccurrenceInterpretation]
  exact BandPrototileTranslation _ _ _ (cert.outer_occurrence 2 true).1

private theorem occF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (m : Int), ∀ (n : Int), BandPrototile (q 3) (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v ⟨.F, m, n⟩) ) := by
  classical
  intro q cfg C T cert m n
  simp only [SubtileOccurrenceInterpretation]
  exact BandPrototileTranslation _ _ _ (cert.outer_occurrence 2 false).1

private theorem cellsTranslate :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).cells = X.cells.image
            (GaussianTranslation d) ) := by
  classical
  intro X d
  exact (TileTranslationFormulas X d).1

private theorem anchorTranslate :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).anchor =
            GaussianTranslation d X.anchor ) := by
  classical
  intro X d
  exact (TileTranslationFormulas X d).2.1

private theorem centroidTranslate :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (d : GaussianInt), TileCentroid (TileTranslation X d) =
            ((TileCentroid X).1 + (d.re : Real), (TileCentroid X).2 + (d.im : Real)) ) := by
  classical
  intro X d
  have h := (TileTranslationFormulas X d).2.2.2.2.1
  simpa [GaussianRealPoint] using h

private theorem translationCentroidGP :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (d : GaussianInt), TileCentroid (TileTranslation X d) =
            ((TileCentroid X).1 + (d.re : Real), (TileCentroid X).2 + (d.im : Real))) → (∀ (X :
            ProtoTile), ∀ (d : GaussianInt), TileCentroid (TileTranslation X d) = TileCentroid X
            + GaussianRealPoint d) ) := by
  classical
  intro centroidTranslate X d
  rw [centroidTranslate]
  ext <;> simp [GaussianRealPoint]

private theorem composeCells :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).cells = X.cells.image
            (GaussianTranslation d)) → (∀ (X : ProtoTile), ∀ (s : GaussianInt), ∀ (d :
            GaussianInt), (TileTranslation (TileTranslation X s) d).cells = (TileTranslation X (s
            + d)).cells) ) := by
  classical
  intro cellsTranslate X s d
  rw [cellsTranslate, cellsTranslate, cellsTranslate, Finset.image_image]
  congr 1
  funext x
  simp [GaussianTranslation]
  abel

private theorem composeCellsEq :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).cells = X.cells.image
            (GaussianTranslation d)) → (∀ (X : ProtoTile), ∀ (s : GaussianInt), ∀ (d :
            GaussianInt), ∀ (t : GaussianInt), (s + d = t) → ((TileTranslation (TileTranslation X
            s) d).cells = (TileTranslation X t).cells)) ) := by
  classical
  intro cellsTranslate X s d t h
  rw [cellsTranslate, cellsTranslate, cellsTranslate, Finset.image_image]
  congr 1
  funext x
  simp only [Function.comp_apply, GaussianTranslation]
  calc
    x + s + d = x + (s + d) := by abel
    _ = x + t := by rw [h]

private theorem composeAnchor :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (s : GaussianInt), ∀ (d : GaussianInt), (TileTranslation
            (TileTranslation X s) d).anchor = (TileTranslation X (s + d)).anchor ) := by
  classical
  intro X s d
  simp [TileTranslation, GaussianTranslation]
  abel

private theorem composeAnchorEq :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (s : GaussianInt), ∀ (d : GaussianInt), (TileTranslation
            (TileTranslation X s) d).anchor = (TileTranslation X (s + d)).anchor) → (∀ (X :
            ProtoTile), ∀ (s : GaussianInt), ∀ (d : GaussianInt), ∀ (t : GaussianInt), (s + d =
            t) → ((TileTranslation (TileTranslation X s) d).anchor = (TileTranslation X
            t).anchor)) ) := by
  classical
  intro composeAnchor X s d t h
  rw [composeAnchor, h]

private theorem cI3 :
    (by
      classical
      exact
        (GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) ^ 3 = -GaussianInt.toComplex (⟨0, 1⟩ :
            GaussianInt) ) := by
  classical
  norm_num [GaussianInt.toComplex_def]

private theorem p0plus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        TileCentroid (cert.P 0 true) - TileCentroid T = cOff (BandVectors.1 (q 3) (q 2)) ) := by
  classical
  intro q cfg C T cert cOff
  simpa [cOff, BandSubtileOccurrence, Fin.add_def, GaussianRealPoint] using
    (cert.outer_occurrence 0 true).2.2

private theorem p0minus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        TileCentroid (cert.P 0 false) - TileCentroid T = -cOff (BandVectors.1 (q 3) (q 2)) ) := by
  classical
  intro q cfg C T cert cOff
  simpa [cOff, BandSubtileOccurrence, Fin.add_def, GaussianRealPoint] using
    (cert.outer_occurrence 0 false).2.2

private theorem p1plus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        TileCentroid (cert.P 1 true) - TileCentroid T = cOff (BandVectors.1 (q 1) (q 3)) ) := by
  classical
  intro q cfg C T cert cOff
  simpa [cOff, BandSubtileOccurrence, Fin.add_def, GaussianRealPoint] using
    (cert.outer_occurrence 1 true).2.2

private theorem p1minus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        TileCentroid (cert.P 1 false) - TileCentroid T = -cOff (BandVectors.1 (q 1) (q 3)) ) := by
  classical
  intro q cfg C T cert cOff
  simpa [cOff, BandSubtileOccurrence, Fin.add_def, GaussianRealPoint] using
    (cert.outer_occurrence 1 false).2.2

private theorem p0plusAbs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        (TileCentroid (cert.P 0 true) - TileCentroid T = cOff (BandVectors.1 (q 3) (q 2))) →
            (TileCentroid (cert.P 0 true) = TileCentroid T + cOff (BandVectors.1 (q 3) (q 2))) )
            := by
  classical
  intro q cfg C T cert cOff p0plus
  calc
    _ = (TileCentroid (cert.P 0 true) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [p0plus]; exact add_comm _ _

private theorem p0minusAbs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        (TileCentroid (cert.P 0 false) - TileCentroid T = -cOff (BandVectors.1 (q 3) (q 2))) →
            (TileCentroid (cert.P 0 false) = TileCentroid T - cOff (BandVectors.1 (q 3) (q 2))) )
            := by
  classical
  intro q cfg C T cert cOff p0minus
  calc
    _ = (TileCentroid (cert.P 0 false) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [p0minus]; abel

private theorem p1plusAbs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        (TileCentroid (cert.P 1 true) - TileCentroid T = cOff (BandVectors.1 (q 1) (q 3))) →
            (TileCentroid (cert.P 1 true) = TileCentroid T + cOff (BandVectors.1 (q 1) (q 3))) )
            := by
  classical
  intro q cfg C T cert cOff p1plus
  calc
    _ = (TileCentroid (cert.P 1 true) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [p1plus]; exact add_comm _ _

private theorem p1minusAbs :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        (TileCentroid (cert.P 1 false) - TileCentroid T = -cOff (BandVectors.1 (q 1) (q 3))) →
            (TileCentroid (cert.P 1 false) = TileCentroid T - cOff (BandVectors.1 (q 1) (q 3))) )
            := by
  classical
  intro q cfg C T cert cOff p1minus
  calc
    _ = (TileCentroid (cert.P 1 false) - TileCentroid T) + TileCentroid T := by abel
    _ = _ := by rw [p1minus]; abel

private theorem q13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.1 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt)) → (BandVectors.1 (q 1) (q 3) = -a - w) ) := by
  classical
  intro q a w qCycle
  dsimp [a, w]
  linear_combination qCycle

private theorem q10 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.1 (q 1) (q 0) = BandVectors.1 (q 1) (q 3) - I * a) ) := by
  classical
  intro q cfg a I
  simpa [a, I] using (VectorRecursionLaws q cfg.proper.1).2.2.1

private theorem q20 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        BandVectors.1 (q 2) (q 0) = a - I * w) ) := by
  classical
  intro q cfg a I w
  simpa [a, w, I] using
    (VectorRecursionLaws ![q 0, q 2, q 3, q 1]
      (SemiProperQuadruple.rotate cfg.proper.1)).2.2.1

private theorem certU :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q 1) (q 3) = -a - w) → ((BandVectors.1 (q 1) (q 0) = BandVectors.1 (q 1)
            (q 3) - I * a) → ((BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (Fin.succ (0 : Fin (3 :
            ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (Fin.succ (0 : Fin (3 :
            ℕ)))) (q (0 : Fin (4 : ℕ)))) → (cert.u = (1 - I) * a - I * w)))) ) := by
  classical
  intro q cfg C T cert a I hI2 w q13 q10 qflip1
  calc
    cert.u = BandVectors.1 (q 0) (q 1) := cert.period_u
    _ = I * BandVectors.1 (q 1) (q 0) := qflip1
    _ = (1 - I) * a - I * w := by
      rw [q10, q13]
      have hprod : I * (-a - w - I * a) = (1 - I) * a - I * w := by
        rw [show I * (-a - w - I * a) = -(I * a) - I * w - (I * I) * a by ring,
          hI2]
        ring
      exact hprod

private theorem certV :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (Fin.succ (1 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q (Fin.succ (1 : Fin (3 : ℕ)))) (q (0 : Fin (4 :
            ℕ)))) → ((BandVectors.1 (q 2) (q 0) = a - I * w) → (cert.v = I * a + w))) ) := by
  classical
  intro q cfg C T cert a I hI2 w qflip2 q20
  calc
    cert.v = BandVectors.1 (q 0) (q 2) := cert.period_v
    _ = I * BandVectors.1 (q 2) (q 0) := qflip2
    _ = I * a + w := by
      rw [q20]
      have hprod : I * (a - I * w) = I * a + w := by
        rw [show I * (a - I * w) = I * a - (I * I) * w by ring, hI2]
        ring
      exact hprod

private theorem rvec2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (Fin.succ
            (1 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (cfg.firstPredecessor (Fin.succ (1 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ)))) → (BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = I * a) )
            := by
  classical
  intro q cfg a I rflip1
  calc
    _ = I * BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) := rflip1
    _ = I * a := by rw [cfg.firstVectorTwo]

private theorem rvec3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        (-I * I = 1) → (
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q 1) (q 3) = -a - w) → ((BandVectors.1 (cfg.firstPredecessor (0 : Fin (4
            : ℕ))) (cfg.firstPredecessor (Fin.succ (2 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (cfg.firstPredecessor (Fin.succ (2 : Fin (3 : ℕ))))
            (cfg.firstPredecessor (0 : Fin (4 : ℕ)))) → (BandVectors.1 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 0) = I * (a + w)))) ) := by
  classical
  intro q cfg a I hIinv w q13 rflip2
  have hflip : BandVectors.1 (q 1) (q 3) =
      I * BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) := by
    rw [← cfg.firstChild, ← cfg.firstParentThree]
    exact rflip2
  have h : BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) =
      -I * BandVectors.1 (q 1) (q 3) := by
    calc
      _ = (-I * I) * BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) := by
        rw [hIinv, one_mul]
      _ = -I * (I * BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)) := by ring
      _ = -I * BandVectors.1 (q 1) (q 3) := by rw [← hflip]
  rw [h, q13]
  have hprod : -I * (-a - w) = I * (a + w) := by
    rw [show -I * (-a - w) = I * a + I * w by ring]
    ring
  exact hprod

private theorem tvec1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = I * w ) := by
  classical
  intro q cfg I w
  have tf := (VectorRecursionLaws cfg.secondPredecessor cfg.secondProper.1).2.2.2.2
    cfg.secondProper 0 |>.1
  calc
    _ = I * BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) := tf
    _ = I * w := by rw [cfg.secondVectorOne]

private theorem qnormal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.1 (q 1) (q 2) = I * a) ) := by
  classical
  intro q cfg a I
  have h := P3055T1ParentVectorNormalForms q cfg
  dsimp only at h
  exact h.2.1

private theorem q31 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (
        let a : GaussianInt := BandVectors.1 (q 2) (q 1)
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        BandVectors.1 (q 3) (q 1) = I * (a + w)) ) := by
  classical
  intro q cfg a I w
  have h := P3055T1ParentVectorNormalForms q cfg
  dsimp only at h
  exact h.2.2.1

private theorem q23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (
        let I : GaussianInt := ⟨0, 1⟩
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        BandVectors.1 (q 2) (q 3) = I * w) ) := by
  classical
  intro q cfg I w
  have h := P3055T1ParentVectorNormalForms q cfg
  dsimp only at h
  exact h.2.2.2.1

end SRowAlignmentGeometry

namespace SRowCaseAlignment

private theorem rowAlignment :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (z :
            P3996T1SRowParameters), (P3996T1SRowTable q cfg C T cert row = some z) → ((0 < (q
            1).1) → ((0 < (q 2).1) → ((0 < (q 3).1) → ((ProperBandQuadruple cfg.firstPredecessor)
            → ((ProperBandQuadruple cfg.secondPredecessor) → ((cfg.firstPredecessor 0 = q 1) →
            ((cfg.firstPredecessor 2 = q 2) → ((cfg.firstPredecessor 3 = q 3) →
            ((cfg.secondPredecessor 0 = q 2) → ((cfg.secondPredecessor 1 = q 3) → ((∀ (m : Int),
            ∀ (n : Int), BandPrototile (q 1) (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v ⟨.A, m, n⟩)) → ((∀ (m : Int), ∀ (n : Int), BandPrototile (q 1)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.B, m, n⟩)) → ((∀ (m : Int), ∀
            (n : Int), BandPrototile (q 2) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            ⟨.C, m, n⟩)) → ((∀ (m : Int), ∀ (n : Int), BandPrototile (q 2)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.D, m, n⟩)) → ((∀ (m : Int), ∀
            (n : Int), BandPrototile (q 3) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            ⟨.E, m, n⟩)) → ((∀ (m : Int), ∀ (n : Int), BandPrototile (q 3)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.F, m, n⟩)) → ((∀ (X :
            ProtoTile), ∀ (d : GaussianInt), TileCentroid (TileTranslation X d) = TileCentroid X
            + GaussianRealPoint d) → ((∀ (X : ProtoTile), ∀ (s : GaussianInt), ∀ (d :
            GaussianInt), ∀ (t : GaussianInt), s + d = t → (TileTranslation (TileTranslation X s)
            d).cells = (TileTranslation X t).cells) → ((∀ (X : ProtoTile), ∀ (s : GaussianInt), ∀
            (d : GaussianInt), (TileTranslation (TileTranslation X s) d).anchor =
            (TileTranslation X (s + d)).anchor) → ((∀ (X : ProtoTile), ∀ (s : GaussianInt), ∀ (d
            : GaussianInt), ∀ (t : GaussianInt), (s + d = t) → ((TileTranslation (TileTranslation
            X s) d).anchor = (TileTranslation X t).anchor)) → (
        let I : GaussianInt := ⟨0, 1⟩
        ((GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) ^ 2 = -1) → (((GaussianInt.toComplex (⟨0,
            1⟩ : GaussianInt)) ^ 3 = -GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) → (
        let cOff (g : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint
              g).1))
        (TileCentroid (cert.P 0 true) - TileCentroid T = cOff (BandVectors.1 (q 3) (q 2))) →
            ((TileCentroid (cert.P 0 false) - TileCentroid T = -cOff (BandVectors.1 (q 3) (q 2)))
            → ((TileCentroid (cert.P 1 true) - TileCentroid T = cOff (BandVectors.1 (q 1) (q 3)))
            → ((TileCentroid (cert.P 1 false) - TileCentroid T = -cOff (BandVectors.1 (q 1) (q
            3))) → ((TileCentroid (cert.P 0 true) = TileCentroid T + cOff (BandVectors.1 (q 3) (q
            2))) → ((TileCentroid (cert.P 0 false) = TileCentroid T - cOff (BandVectors.1 (q 3)
            (q 2))) → ((TileCentroid (cert.P 1 true) = TileCentroid T + cOff (BandVectors.1 (q 1)
            (q 3))) → ((TileCentroid (cert.P 1 false) = TileCentroid T - cOff (BandVectors.1 (q
            1) (q 3))) → (
        let edgeVector : GaussianInt := BandVectors.1 (q 2) (q 1)
        let w : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q 1) (q 3) = -edgeVector - w) → ((cert.u = (1 - I) * edgeVector - I * w)
            → ((cert.v = I * edgeVector + w) → ((BandVectors.1 (q 1) (q 2) = I * edgeVector) →
            ((BandVectors.1 (q 3) (q 1) = I * (edgeVector + w)) → ((BandVectors.1 (q 2) (q 3) = I
            * w) → (
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occurrence z.childIndex
        let W := occurrence z.parentIndex
        let newRight := TileTranslation V z.rightShift
        ProperBandQuadruple z.predecessor ∧
          z.predecessor 0 = q z.childSlot.succ ∧
          BandPrototile (z.predecessor 0) V ∧
          BandPrototile (z.predecessor z.parentSlot.succ) W ∧
          0 < (z.predecessor 0).1 ∧
          0 < (z.predecessor z.parentSlot.succ).1 ∧
          (if z.childIsExterior then
            z.childIndex = a ∧ z.parentIndex = b
           else z.childIndex = b ∧ z.parentIndex = a) ∧
          (newRight.cells =
              (TileTranslation (cert.P z.childSlot z.childSign)
                (z.childShift + z.rightShift)).cells ∧
            (newRight.cells = ∅ → newRight.anchor =
              (TileTranslation (cert.P z.childSlot z.childSign)
                (z.childShift + z.rightShift)).anchor)) ∧
          z.rightShift = (⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
            (if Even z.rotation.val then
              BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ)
             else BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0)) ∧
          TileCentroid W - TileCentroid V = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
              (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
                BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
          TileCentroid newRight - TileCentroid (TileTranslation T z.oldShift) =
            (-((TileCentroid (cert.P z.childSlot z.sourceSign) - TileCentroid T).2),
              (TileCentroid (cert.P z.childSlot z.sourceSign) - TileCentroid
                  T).1)))))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro q cfg C T cert a b row z hz q1pos q2pos q3pos hfp hsp hfc hft hfr hsc hsr occA occB occC
      occD occE occF translationCentroidGP composeCellsEq composeAnchor composeAnchorEq I cI2 cI3
      cOff p0plus p0minus p1plus p1minus p0plusAbs p0minusAbs p1plusAbs p1minusAbs edgeVector w
      q13 certU certV qnormal q31 q23
  cases row <;> simp only [P3996T1SRowTable] at hz <;> cases hz <;> rename_i presentation
  all_goals simp only [hfp, Fin.isValue, hfc, Fin.succ_zero_eq_one,
      SubtileOccurrenceInterpretation, Int.cast_one, certU, Int.reduceNeg, one_mul, certV,
      Fin.succ_one_eq_two, hft, Int.cast_zero, zero_mul, add_zero, q1pos, q2pos, ↓reduceIte,
      and_self, Fin.coe_ofNat_eq_mod, Nat.reduceMod, even_two, one_div, GaussianRealPoint,
      Zsqrtd.re_mul, Zsqrtd.re_add, neg_mul, Zsqrtd.im_add, Int.cast_add, Int.cast_mul,
      GaussianInt.intCast_re, map_pow, Int.cast_neg, GaussianInt.intCast_im, Zsqrtd.im_mul,
      Prod.smul_mk, smul_eq_mul, p0plus, Prod.mk_sub_mk, sub_neg_eq_add, true_and, I, cOff,
      neg_add_rev, zero_add, Fin.reduceSucc, hfr, q3pos, Nat.mod_succ, mul_ite,
      right_eq_ite_iff, mul_eq_mul_left_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, Nat.one_mod, pow_one, Nat.not_even_one, mul_one, neg_sub, p0minus,
      Prod.neg_mk, neg_neg, Bool.false_eq_true, Nat.zero_mod, pow_zero, Even.zero, hsp, hsc,
      hsr, p1minus, p1plus]
  all_goals refine ⟨?_, ?_, ?_⟩
  case positiveS1.refl.refine_1 =>
    simpa [SubtileOccurrenceInterpretation, TileTranslation, GaussianTranslation, certU, certV,
        I, edgeVector, w] using occA (-1) (-1)
  case positiveS1.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occC 0 0
  case positiveS2.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occA 0 (-1)
  case positiveS2.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occE 0 0
  case positiveS3.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occC 1 0
  case positiveS3.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occE 0 0
  case positiveS4.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occA 0 0
  case positiveS4.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occC 1 1
  case positiveS5.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occA 0 0
  case positiveS5.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occE 0 1
  case positiveS6.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occC 0 0
  case positiveS6.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occE (-1) 0
  case reflectedS1.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occB 1 1
  case reflectedS1.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occD 0 0
  case reflectedS2.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occB 0 1
  case reflectedS2.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occF 0 0
  case reflectedS3.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occD (-1) 0
  case reflectedS3.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occF 0 0
  case reflectedS4.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occB 0 0
  case reflectedS4.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occD (-1) (-1)
  case reflectedS5.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occB 0 0
  case reflectedS5.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occF 0 (-1)
  case reflectedS6.refl.refine_1 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occD 0 0
  case reflectedS6.refl.refine_2 => simpa [SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation, certU, certV, I, edgeVector, w] using occF 1 0
  all_goals constructor
  all_goals try constructor
  all_goals try first
    | (apply composeCellsEq; abel)
    | (intro _; apply composeAnchorEq; simp []; abel)
  all_goals try norm_num [Even]
  all_goals try constructor
  case positiveS1.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
      Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
          presentation
  case positiveS2.refl.refine_3.right.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
      Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
          presentation
  case positiveS1.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p0plusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      qnormal, I] <;> ring
  case positiveS2.refl.refine_3.right.right.right =>
    simp only [translationCentroidGP]
    rw [p0plusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q31, cI3, I] <;> ring
  case positiveS3.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p1plusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q13, q23, I] <;> ring
  case positiveS4.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p0plusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      qnormal, I] <;> ring
  case positiveS5.refl.refine_3.right.right.right =>
    simp only [translationCentroidGP]
    rw [p0plusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q31, cI3, I] <;> ring
  case positiveS6.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p1plusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q13, q23, I] <;> ring
  case reflectedS1.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p0minusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      qnormal, cI2, I] <;> ring
  case reflectedS2.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p0minusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q31, I] <;> ring
  case reflectedS3.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p1minusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q13, q23, cI2, I] <;> ring
  case reflectedS4.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p0minusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      qnormal, cI2, I] <;> ring
  case reflectedS5.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p0minusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q31, I] <;> ring
  case reflectedS6.refl.refine_3.right.right =>
    simp only [translationCentroidGP]
    rw [p1minusAbs]
    ext <;> simp [GaussianRealPoint, cOff,
      q13, q23, cI2, I] <;> ring
  all_goals try first
    | (intro _; exact composeAnchor _ _ _)
    | (intro _; rw [composeAnchor]; simp)
  all_goals try (intro x hx; omega)
  case positiveS3.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case positiveS4.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case positiveS5.refl.refine_3.right.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case positiveS6.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case reflectedS1.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case reflectedS2.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case reflectedS3.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case reflectedS4.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case reflectedS5.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation
  case reflectedS6.refl.refine_3.right.left =>
    simpa [SubtileOccurrenceInterpretation, translationCentroidGP, GaussianRealPoint,
        Prod.add_def, hfc, hft, hfr, hsc, hsr, certU, certV, I] using
        presentation

end SRowCaseAlignment

theorem P3996T1SRowAlignment
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b)
    (z : P3996T1SRowParameters)
    (hz : P3996T1SRowTable q cfg C T cert row = some z) :
    let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    let V := occurrence z.childIndex
    let W := occurrence z.parentIndex
    let newRight := TileTranslation V z.rightShift
    ProperBandQuadruple z.predecessor ∧
      z.predecessor 0 = q z.childSlot.succ ∧
      BandPrototile (z.predecessor 0) V ∧
      BandPrototile (z.predecessor z.parentSlot.succ) W ∧
      0 < (z.predecessor 0).1 ∧
      0 < (z.predecessor z.parentSlot.succ).1 ∧
      (if z.childIsExterior then
        z.childIndex = a ∧ z.parentIndex = b
       else z.childIndex = b ∧ z.parentIndex = a) ∧
      (newRight.cells =
          (TileTranslation (cert.P z.childSlot z.childSign)
            (z.childShift + z.rightShift)).cells ∧
        (newRight.cells = ∅ → newRight.anchor =
          (TileTranslation (cert.P z.childSlot z.childSign)
            (z.childShift + z.rightShift)).anchor)) ∧
      z.rightShift = (⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
        (if Even z.rotation.val then
          BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ)
         else BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0)) ∧
      TileCentroid W - TileCentroid V = (1 / 2 : Real) •
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
          (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
            BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
      TileCentroid newRight - TileCentroid (TileTranslation T z.oldShift) =
        (-((TileCentroid (cert.P z.childSlot z.sourceSign) - TileCentroid T).2),
          (TileCentroid (cert.P z.childSlot z.sourceSign) - TileCentroid T).1) := by
-- BODY
  have q1pos : 0 < (q 1).1 := SRowAlignmentGeometry.q1pos q cfg
  have q2pos : 0 < (q 2).1 := SRowAlignmentGeometry.q2pos q cfg
  have q3pos : 0 < (q 3).1 := SRowAlignmentGeometry.q3pos q cfg
  have hfp : ProperBandQuadruple cfg.firstPredecessor := cfg.firstProper
  have hsp : ProperBandQuadruple cfg.secondPredecessor := cfg.secondProper
  have hfc : cfg.firstPredecessor 0 = q 1 := cfg.firstChild
  have hft : cfg.firstPredecessor 2 = q 2 := cfg.firstParentTwo
  have hfr : cfg.firstPredecessor 3 = q 3 := cfg.firstParentThree
  have hsc : cfg.secondPredecessor 0 = q 2 := cfg.secondChild
  have hsr : cfg.secondPredecessor 1 = q 3 := cfg.secondParentOne
  have occA (m n : Int) : BandPrototile (q 1)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.A, m, n⟩) :=
          SRowAlignmentGeometry.occA q cfg C T cert m n
  have occB (m n : Int) : BandPrototile (q 1)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.B, m, n⟩) :=
          SRowAlignmentGeometry.occB q cfg C T cert m n
  have occC (m n : Int) : BandPrototile (q 2)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.C, m, n⟩) :=
          SRowAlignmentGeometry.occC q cfg C T cert m n
  have occD (m n : Int) : BandPrototile (q 2)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.D, m, n⟩) :=
          SRowAlignmentGeometry.occD q cfg C T cert m n
  have occE (m n : Int) : BandPrototile (q 3)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.E, m, n⟩) :=
          SRowAlignmentGeometry.occE q cfg C T cert m n
  have occF (m n : Int) : BandPrototile (q 3)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.F, m, n⟩) :=
          SRowAlignmentGeometry.occF q cfg C T cert m n
  have cellsTranslate := SRowAlignmentGeometry.cellsTranslate
  have anchorTranslate := SRowAlignmentGeometry.anchorTranslate
  have centroidTranslate := SRowAlignmentGeometry.centroidTranslate
  have translationCentroidGP (X : ProtoTile) (d : GaussianInt) :
      TileCentroid (TileTranslation X d) = TileCentroid X + GaussianRealPoint d :=
          SRowAlignmentGeometry.translationCentroidGP centroidTranslate X d
  have composeCells := SRowAlignmentGeometry.composeCells cellsTranslate
  have composeCellsEq := SRowAlignmentGeometry.composeCellsEq cellsTranslate
  have composeAnchor (X : ProtoTile) (s d : GaussianInt) :
      (TileTranslation (TileTranslation X s) d).anchor =
        (TileTranslation X (s + d)).anchor := SRowAlignmentGeometry.composeAnchor X s d
  have composeAnchorEq (X : ProtoTile) (s d t : GaussianInt) (h : s + d = t) :
      (TileTranslation (TileTranslation X s) d).anchor =
        (TileTranslation X t).anchor := SRowAlignmentGeometry.composeAnchorEq composeAnchor X s d
            t h
  let I : GaussianInt := ⟨0, 1⟩
  have hI2 : I * I = -1 := by dsimp [I]; apply Zsqrtd.ext <;> norm_num
  have hIinv : -I * I = 1 := by rw [show -I * I = -(I * I) by ring, hI2]; norm_num
  have cI2 : (GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) ^ 2 = -1 := by
    norm_num [GaussianInt.toComplex_def]
  have cI3 : (GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) ^ 3 =
      -GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt) := SRowAlignmentGeometry.cI3
  let cOff (g : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint g - (-(GaussianRealPoint g).2, (GaussianRealPoint g).1))
  have p0plus : TileCentroid (cert.P 0 true) - TileCentroid T =
      cOff (BandVectors.1 (q 3) (q 2)) := SRowAlignmentGeometry.p0plus q cfg C T cert
  have p0minus : TileCentroid (cert.P 0 false) - TileCentroid T =
      -cOff (BandVectors.1 (q 3) (q 2)) := SRowAlignmentGeometry.p0minus q cfg C T cert
  have p1plus : TileCentroid (cert.P 1 true) - TileCentroid T =
      cOff (BandVectors.1 (q 1) (q 3)) := SRowAlignmentGeometry.p1plus q cfg C T cert
  have p1minus : TileCentroid (cert.P 1 false) - TileCentroid T =
      -cOff (BandVectors.1 (q 1) (q 3)) := SRowAlignmentGeometry.p1minus q cfg C T cert
  have p0plusAbs : TileCentroid (cert.P 0 true) =
      TileCentroid T + cOff (BandVectors.1 (q 3) (q 2)) := SRowAlignmentGeometry.p0plusAbs q cfg
          C T cert p0plus
  have p0minusAbs : TileCentroid (cert.P 0 false) =
      TileCentroid T - cOff (BandVectors.1 (q 3) (q 2)) := SRowAlignmentGeometry.p0minusAbs q cfg
          C T cert p0minus
  have p1plusAbs : TileCentroid (cert.P 1 true) =
      TileCentroid T + cOff (BandVectors.1 (q 1) (q 3)) := SRowAlignmentGeometry.p1plusAbs q cfg
          C T cert p1plus
  have p1minusAbs : TileCentroid (cert.P 1 false) =
      TileCentroid T - cOff (BandVectors.1 (q 1) (q 3)) := SRowAlignmentGeometry.p1minusAbs q cfg
          C T cert p1minus
  let edgeVector : GaussianInt := BandVectors.1 (q 2) (q 1)
  let w : GaussianInt := BandVectors.1 (q 3) (q 2)
  have qCycle := (VectorRecursionLaws q cfg.proper.1).1
  have q13 : BandVectors.1 (q 1) (q 3) = -edgeVector - w := SRowAlignmentGeometry.q13 q qCycle
  have q10 := SRowAlignmentGeometry.q10 q cfg
  have qflip1 := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper 0 |>.1
  have qflip2 := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper 1 |>.1
  have q20 := SRowAlignmentGeometry.q20 q cfg
  have certU : cert.u = (1 - I) * edgeVector - I * w := SRowAlignmentGeometry.certU q cfg C T
      cert hI2 q13
      q10 qflip1
  have certV : cert.v = I * edgeVector + w := SRowAlignmentGeometry.certV q cfg C T cert hI2
      qflip2 q20
  have rflip1 := (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.2.2.2
    cfg.firstProper 1 |>.1
  have rflip2 := (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.2.2.2
    cfg.firstProper 2 |>.1
  have rvec2 : BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = I * edgeVector :=
      SRowAlignmentGeometry.rvec2 q cfg rflip1
  have rvec3 : BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = I * (edgeVector
      + w) :=
      SRowAlignmentGeometry.rvec3 q cfg hIinv q13 rflip2
  have tvec1 : BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = I * w :=
      SRowAlignmentGeometry.tvec1 q cfg
  have qnormal :
      BandVectors.1 (q 1) (q 2) = I * edgeVector := SRowAlignmentGeometry.qnormal q cfg
  have q31 : BandVectors.1 (q 3) (q 1) = I * (edgeVector + w) := SRowAlignmentGeometry.q31 q cfg
  have q23 : BandVectors.1 (q 2) (q 3) = I * w := SRowAlignmentGeometry.q23 q cfg
  have rowAlignment :
    let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    let V := occurrence z.childIndex
    let W := occurrence z.parentIndex
    let newRight := TileTranslation V z.rightShift
    ProperBandQuadruple z.predecessor ∧
      z.predecessor 0 = q z.childSlot.succ ∧
      BandPrototile (z.predecessor 0) V ∧
      BandPrototile (z.predecessor z.parentSlot.succ) W ∧
      0 < (z.predecessor 0).1 ∧
      0 < (z.predecessor z.parentSlot.succ).1 ∧
      (if z.childIsExterior then
        z.childIndex = a ∧ z.parentIndex = b
       else z.childIndex = b ∧ z.parentIndex = a) ∧
      (newRight.cells =
          (TileTranslation (cert.P z.childSlot z.childSign)
            (z.childShift + z.rightShift)).cells ∧
        (newRight.cells = ∅ → newRight.anchor =
          (TileTranslation (cert.P z.childSlot z.childSign)
            (z.childShift + z.rightShift)).anchor)) ∧
      z.rightShift = (⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
        (if Even z.rotation.val then
          BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ)
         else BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0)) ∧
      TileCentroid W - TileCentroid V = (1 / 2 : Real) •
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ z.rotation.val *
          (BandVectors.1 (z.predecessor z.parentSlot.succ) (z.predecessor 0) +
            BandVectors.1 (z.predecessor 0) (z.predecessor z.parentSlot.succ))) ∧
      TileCentroid newRight - TileCentroid (TileTranslation T z.oldShift) =
        (-((TileCentroid (cert.P z.childSlot z.sourceSign) - TileCentroid T).2),
          (TileCentroid (cert.P z.childSlot z.sourceSign) - TileCentroid T).1) :=
              SRowCaseAlignment.rowAlignment q cfg C T cert a b row z hz q1pos q2pos q3pos hfp
              hsp hfc hft hfr hsc hsr occA occB occC occD occE occF translationCentroidGP
              composeCellsEq composeAnchor composeAnchorEq cI2 cI3 p0plus p0minus p1plus p1minus
              p0plusAbs p0minusAbs p1plusAbs p1minusAbs q13 certU certV qnormal q31 q23
  exact rowAlignment


end ApollonianSuperharmonic

end
