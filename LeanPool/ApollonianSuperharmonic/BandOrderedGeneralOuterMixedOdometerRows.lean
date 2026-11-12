/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorWebRow
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import LeanPool.ApollonianSuperharmonic.OdometerWeb
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: BandOrderedGeneralOuterMixedOdometerRows]

/-!
# BandOrderedGeneralOuterMixedOdometerRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OuterMixedOdometerGeometry

private theorem hW :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.1 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
            + BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.2 (q (2 :
            Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (q (1 : Fin
            (4 : ℕ))) (q (0 : Fin (4 : ℕ))) = BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4
            : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) =
            BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) ∧
            (ProperBandQuadruple q → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin
            (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))))) → (BandVectors.1 (q
            1) (q 3) = -U - W) ) := by
  classical
  intro q U W laws
  apply eq_of_sub_eq_zero
  dsimp [U, W]
  linear_combination laws.1

private theorem hA :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.1 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
            + BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.2 (q (2 :
            Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (q (1 : Fin
            (4 : ℕ))) (q (0 : Fin (4 : ℕ))) = BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4
            : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) =
            BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) ∧
            (ProperBandQuadruple q → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin
            (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))))) → (BandVectors.2 (q
            1) (q 3) = -A - B) ) := by
  classical
  intro q A B laws
  apply eq_of_sub_eq_zero
  dsimp [A, B]
  linear_combination laws.2.1

private theorem hrotV :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) - I * W ) := by
  classical
  intro q cfg I W
  simpa [I, W, cfg.firstParentThree, cfg.firstParentTwo] using
    (VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.1

private theorem hrotA :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) + I * B ) := by
  classical
  intro q cfg I B
  simpa [I, B, cfg.firstParentThree, cfg.firstParentTwo] using
    (VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.2.1

private theorem hV21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) - I * W) → (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) ) := by
  classical
  intro q cfg I U W hrotV
  have h := hrotV
  rw [cfg.firstParentTwo, cfg.firstChild] at h
  rw [cfg.firstParentTwo]
  dsimp [U, W, I] at h ⊢
  linear_combination -h

private theorem hA21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) + I * B) → (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) ) := by
  classical
  intro q cfg I A B hrotA
  have h := hrotA
  rw [cfg.firstParentTwo, cfg.firstChild] at h
  rw [cfg.firstParentTwo]
  dsimp [A, B, I] at h ⊢
  linear_combination -h

private theorem hV13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.2
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4 : ℕ))) +
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple
            cfg.firstPredecessor → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (cfg.firstPredecessor (0 :
            Fin (4 : ℕ))) (cfg.firstPredecessor j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (cfg.firstPredecessor j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ)))
            ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ))))) → ((BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) → (BandVectors.1
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -U - (1 + I) * W)) ) := by
  classical
  intro q cfg I U W firstLaws hV21
  have h := firstLaws.1
  rw [cfg.firstParentThree, cfg.firstParentTwo] at h
  have hV21' := hV21
  rw [cfg.firstParentTwo] at hV21'
  rw [hV21'] at h
  rw [cfg.firstParentThree]
  dsimp [U, W, I]
  linear_combination h

private theorem hA13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.2
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4 : ℕ))) +
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple
            cfg.firstPredecessor → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (cfg.firstPredecessor (0 :
            Fin (4 : ℕ))) (cfg.firstPredecessor j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (cfg.firstPredecessor j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ)))
            ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ))))) → ((BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) → (BandVectors.2
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -A - (1 - I) * B)) ) := by
  classical
  intro q cfg I A B firstLaws hA21
  have h := firstLaws.2.1
  rw [cfg.firstParentThree, cfg.firstParentTwo] at h
  have hA21' := hA21
  rw [cfg.firstParentTwo] at hA21'
  rw [hA21'] at h
  rw [cfg.firstParentThree]
  dsimp [A, B, I]
  linear_combination h

private theorem hpos2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 2).1) )
            := by
  classical
  intro q cfg
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 1
  have hn' : 0 ≤ (q 2).1 := by simpa using hn
  have hne : (q 2).1 ≠ 0 := cfg.noLine 2
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · linarith
  · exact hpos

private theorem hpos3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 3).1) )
            := by
  classical
  intro q cfg
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 2
  have hn' : 0 ≤ (q 3).1 := by simpa using hn
  have hne : (q 3).1 ≠ 0 := cfg.noLine 3
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · linarith
  · exact hpos

private theorem hpos1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (0 < (q 1).1) )
            := by
  classical
  intro q cfg
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 0
  have hn' : 0 ≤ (q 1).1 := by simpa using hn
  have hne : (q 1).1 ≠ 0 := cfg.noLine 1
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · linarith
  · exact hpos

private theorem pPack :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (i : Fin 3), ∀ (s : Bool), ∃ p pi : Real ×
            Real, PartialOdometerSlope h = some p ∧ PartialOdometerSlope (r i s) = some pi ∧ pi.1
            - p.1 = (if s then (1 : Real) else -1) * (1 / 2) * (((BandVectors.2 (q ((i + 2).succ)
            ) (q ((i + 1).succ))).re : Int) - ((BandVectors.2 (q ((i + 2).succ) ) (q ((i +
            1).succ))).im : Int)) ∧ pi.2 - p.2 = (if s then (1 : Real) else -1) * (1 / 2) *
            (((BandVectors.2 (q ((i + 2).succ) ) (q ((i + 1).succ))).im : Int) + ((BandVectors.2
            (q ((i + 2).succ) ) (q ((i + 1).succ))).re : Int))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data i s
  rcases data.hPslope i s with hzero | hgood
  · have hz : (q i.succ).1 = 0 := by simpa using hzero
    exact False.elim ((cfg.noLine i.succ) hz)
  · exact hgood

private theorem hdelta0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p0 : ℝ × ℝ), ∀ (p0leaf : ℝ × ℝ), (p0leaf.1 - p0.1 = (if true = true then (1 : ℝ) else
            (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((0 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((0 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((p0leaf.2 - p0.2 = (if true = true then
            (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) + (2 :
            Fin (3 : ℕ))).succ) (q ((0 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((0 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (p0leaf - p0 = sOff B)) ) := by
  classical
  intro q B sOff p0 p0leaf hp0x hp0y
  apply Prod.ext
  · dsimp [sOff]
    simpa [Fin.add_def, B] using hp0x
  · dsimp [sOff]
    simpa [Fin.add_def, B] using hp0y

private theorem hdelta1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        (BandVectors.2 (q 1) (q 3) = -A - B) → (∀ (p0 : ℝ × ℝ), ∀ (p1leaf : ℝ × ℝ), (p1leaf.1 -
            p0.1 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (q ((1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3
            : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q ((1 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((p1leaf.2 -
            p0.2 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (q ((1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3
            : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q ((1 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (p1leaf - p0
            = -sOff (BandVectors.2 (q 1) (q 3))))) ) := by
  classical
  intro q A B sOff hA p0 p1leaf hp1x hp1y
  apply Prod.ext
  · dsimp [sOff]
    simpa [Fin.add_def, hA] using hp1x
  · dsimp [sOff]
    simpa [Fin.add_def, hA] using hp1y

private theorem hc1minus :
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
        TileCentroid (P 1 false) - TileCentroid T = -cOff (BandVectors.1 (q 1) (q 3))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data cOff
  simpa [cOff, Fin.add_def] using data.hPcent 1 false

private theorem hcent12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile),
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.2
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4 : ℕ))) +
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple
            cfg.firstPredecessor → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (cfg.firstPredecessor (0 :
            Fin (4 : ℕ))) (cfg.firstPredecessor j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (cfg.firstPredecessor j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ)))
            ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ))))) → ((BandVectors.1 (q 1) (q 3) = -U
            - W) → ((TileCentroid (P 0 true) - TileCentroid T = cOff W) → ((TileCentroid (P 1
            false) - TileCentroid T = -cOff (BandVectors.1 (q 1) (q 3))) → (TileCentroid (P 1
            false) - TileCentroid (P 0 true) = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ (3 : Nat) * (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 2))))))) ) := by
  classical
  intro q cfg T P U W cOff firstLaws hW hc0plus hc1minus
  let I : GaussianInt := ⟨0, 1⟩
  have hbase : TileCentroid (P 1 false) - TileCentroid (P 0 true) =
      -cOff (BandVectors.1 (q 1) (q 3)) - cOff W := by
    calc
      _ = (TileCentroid (P 1 false) - TileCentroid T) -
          (TileCentroid (P 0 true) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc1minus, hc0plus]
  have hflipPair := firstLaws.2.2.2.2 cfg.firstProper 1
  have hflip := hflipPair.1
  change BandVectors.1 (cfg.firstPredecessor 0)
      (cfg.firstPredecessor 2) = I * BandVectors.1
        (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) at hflip
  rw [cfg.firstChild, cfg.firstParentTwo] at hflip
  rw [hbase, hW, cfg.firstVectorTwo]
  rw [cfg.firstChild, cfg.firstParentTwo]
  rw [hflip]
  dsimp [cOff, W, U, I, GaussianRealPoint, Prod.smul_mk,
    Prod.add_def, Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; simp

private theorem hsumA12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.2
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4 : ℕ))) +
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) =
            BandVectors.2 (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin
            (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple
            cfg.firstPredecessor → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (cfg.firstPredecessor (0 :
            Fin (4 : ℕ))) (cfg.firstPredecessor j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (cfg.firstPredecessor j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ)))
            ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ))))) → ((BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) + I * B) → ((BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) → (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = (1 - I) * A))) ) := by
  classical
  intro q cfg I A B firstLaws hrotA hA21
  have hflipPair := firstLaws.2.2.2.2 cfg.firstProper 1
  have hflip := hflipPair.2
  change BandVectors.2 (cfg.firstPredecessor 0)
      (cfg.firstPredecessor 2) = -I * BandVectors.2
        (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) at hflip
  have hbase : BandVectors.2 (cfg.firstPredecessor 2)
      (cfg.firstPredecessor 0) = A := by
    rw [hrotA, hA21]
    dsimp [A, B]
    ring
  rw [hbase] at hflip ⊢
  linear_combination hflip

private theorem hslope12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        (BandVectors.2 (q 1) (q 3) = -A - B) → (∀ (p0 : ℝ × ℝ), ∀ (p0leaf : ℝ × ℝ), ∀ (p1leaf : ℝ
            × ℝ), (p0leaf - p0 = sOff B) → ((p1leaf - p0 = -sOff (BandVectors.2 (q 1) (q 3))) →
            ((BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = (1 - I) * A) → (p1leaf - p0leaf =
            (1 / 2 : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) *
            (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2))))))) ) := by
  classical
  intro q cfg I A B sOff hA p0 p0leaf p1leaf hdelta0 hdelta1 hsumA12
  have hbase : p1leaf - p0leaf = sOff A := by
    calc
      _ = (p1leaf - p0) - (p0leaf - p0) := by ext <;> dsimp <;> ring
      _ = -sOff (BandVectors.2 (q 1) (q 3)) - sOff B := by rw [hdelta1, hdelta0]
      _ = sOff A := by rw [hA]; dsimp [A, B, sOff]; ext <;> norm_num [I] <;> ring
  rw [hbase, hsumA12]
  dsimp [sOff, GaussianRealPoint]
  norm_num [GaussianRealPoint, I, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem adj12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (hpos2 : 0 < (q 2).1), ∀ (hpos1 : 0 < (q 1).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl hpos1, q, cfg.proper.1, 1, rfl⟩, hpos1⟩
        let C2 : BandCircle := ⟨⟨q 2, Or.inl hpos2, q, cfg.proper.1, 2, rfl⟩, hpos2⟩
        ∀ (p0leaf : ℝ × ℝ), (PartialOdometerSlope (r (0 : Fin (3 : ℕ)) true) = some p0leaf) → (∀
            (p1leaf : ℝ × ℝ), (PartialOdometerSlope (r (1 : Fin (3 : ℕ)) false) = some p1leaf) →
            ((TileCentroid (P 1 false) - TileCentroid (P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → ((p1leaf - p0leaf = (1 / 2 :
            Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) * (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → (SubtileLatticeAdjacent C1 C2
            (P 0 true) (P 1 false) (r 0 true) (r 1 false)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data hpos2 hpos1 C1 C2 p0leaf hp0leaf p1leaf hp1leaf
      hcent12 hslope12
  refine ⟨?_, ?_, ⟨p0leaf, p1leaf, hp0leaf, hp1leaf, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using data.hP 0 true
  · simpa [C2, cfg.firstParentTwo] using data.hP 1 false
  refine ⟨cfg.firstPredecessor, 1, 3, cfg.firstProper, ?_, ?_, hcent12, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C2] using cfg.firstParentTwo
  · exact congrArg Prod.fst hslope12
  · exact congrArg Prod.snd hslope12

private theorem hdelta2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p0 : ℝ × ℝ), ∀ (p2leaf : ℝ × ℝ), (p2leaf.1 - p0.1 = (if false = true then (1 : ℝ) else
            (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 :
            ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((p2leaf.2 - p0.2 = (if false = true then
            (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 :
            Fin (3 : ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (p2leaf - p0 = -sOff A)) ) := by
  classical
  intro q A sOff p0 p2leaf hp2x hp2y
  apply Prod.ext
  · dsimp [sOff]
    simpa [Fin.add_def, A] using hp2x
  · dsimp [sOff]
    simpa [Fin.add_def, A] using hp2y

private theorem hrot2V :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) - I * BandVectors.1
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) ) := by
  classical
  intro q cfg I
  simpa [I] using (VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.firstProper.1))).2.2.1

private theorem hV30 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -U - (1 + I) * W) →
            ((BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) - I * BandVectors.1
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)) → (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = I * (U + W)))) ) := by
  classical
  intro q cfg I hImul U W hV13 hrot2V
  rw [hrot2V, hV13, cfg.firstParentThree, cfg.firstParentTwo]
  dsimp [U, W]
  linear_combination hImul * BandVectors.1 (q 3) (q 2)

private theorem hsumV03 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = I * (U + W)) →
            ((BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = I * BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)) → (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 + I) * (I * (U + W)))) ) := by
  classical
  intro q cfg I U W hV30 hflip03
  rw [hflip03, hV30]
  ring

private theorem hcent13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (P 0 true) - TileCentroid T = cOff W) → ((TileCentroid (P 2 false) -
            TileCentroid T = -cOff U) → ((BandVectors.1 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 3) = (1 + I) * (I * (U + W))) → (TileCentroid (P 2 false) -
            TileCentroid (P 0 true) = (1 / 2 : Real) • GaussianRealPoint (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3))))) ) := by
  classical
  intro q cfg T P I U W cOff hc0plus hc2minus hsumV03
  have hbase : TileCentroid (P 2 false) - TileCentroid (P 0 true) =
      -cOff U - cOff W := by
    calc
      _ = (TileCentroid (P 2 false) - TileCentroid T) -
          (TileCentroid (P 0 true) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc2minus, hc0plus]
  rw [hbase, hsumV03]
  dsimp [cOff, GaussianRealPoint, I, U, W, Prod.smul_mk,
    Prod.add_def, Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hrot2A :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) + I * BandVectors.2
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) ) := by
  classical
  intro q cfg I
  simpa [I] using (VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.firstProper.1))).2.2.2.1

private theorem hA30 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        (I * I = -1) → (
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -A - (1 - I) * B) →
            ((BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) + I * BandVectors.2
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)) → (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = -I * (A + B)))) ) := by
  classical
  intro q cfg I hImul A B hA13 hrot2A
  rw [hrot2A, hA13, cfg.firstParentThree, cfg.firstParentTwo]
  dsimp [A, B]
  linear_combination hImul * BandVectors.2 (q 3) (q 2)

private theorem hsumA03 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = -I * (A + B)) →
            ((BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = -I *
            BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)) → (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 - I) * (-I * (A + B)))) ) := by
  classical
  intro q cfg I A B hA30 hflip03A
  rw [hflip03A, hA30]
  ring

private theorem hslope13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p0 : ℝ × ℝ), ∀ (p0leaf : ℝ × ℝ), (p0leaf - p0 = sOff B) → (∀ (p2leaf : ℝ × ℝ), (p2leaf
            - p0 = -sOff A) → ((BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
            BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 - I) * (-I * (A
            + B))) → (p2leaf - p0leaf = (1 / 2 : Real) • GaussianRealPoint (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3))))) ) := by
  classical
  intro q cfg I A B sOff p0 p0leaf hdelta0 p2leaf hdelta2 hsumA03
  have hbase : p2leaf - p0leaf = -sOff (A + B) := by
    calc
      _ = (p2leaf - p0) - (p0leaf - p0) := by ext <;> dsimp <;> ring
      _ = -sOff A - sOff B := by rw [hdelta2, hdelta0]
      _ = -sOff (A + B) := by
        dsimp [sOff]
        ext <;> norm_num [I] <;> ring
  rw [hbase, hsumA03]
  dsimp [sOff, GaussianRealPoint, I, A, B, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem adj13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (hpos3 : 0 < (q 3).1), ∀ (hpos1 : 0 < (q 1).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl hpos1, q, cfg.proper.1, 1, rfl⟩, hpos1⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl hpos3, q, cfg.proper.1, 3, rfl⟩, hpos3⟩
        ∀ (p0leaf : ℝ × ℝ), (PartialOdometerSlope (r (0 : Fin (3 : ℕ)) true) = some p0leaf) → (∀
            (p2leaf : ℝ × ℝ), (PartialOdometerSlope (r (2 : Fin (3 : ℕ)) false) = some p2leaf) →
            ((TileCentroid (P 2 false) - TileCentroid (P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3))) → ((p2leaf - p0leaf
            = (1 / 2 : Real) • GaussianRealPoint (BandVectors.2 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 0) + BandVectors.2 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 3))) → (SubtileLatticeAdjacent C1 C3 (P 0 true) (P 2 false) (r
            0 true) (r 2 false)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data hpos3 hpos1 C1 C3 p0leaf hp0leaf p2leaf hp2leaf
      hcent13 hslope13
  refine ⟨?_, ?_, ⟨p0leaf, p2leaf, hp0leaf, hp2leaf, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using data.hP 0 true
  · simpa [C3, cfg.firstParentThree] using data.hP 2 false
  refine ⟨cfg.firstPredecessor, 2, 0, cfg.firstProper, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C3] using cfg.firstParentThree
  · simpa using hcent13
  · simpa using congrArg Prod.fst hslope13
  · simpa using congrArg Prod.snd hslope13

private theorem hdelta1p :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p0 : ℝ × ℝ), ∀ (p1pleaf : ℝ × ℝ), (p1pleaf.1 - p0.1 = (if true = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((1 : Fin (3 : ℕ)) + (2 : Fin (3
            : ℕ))).succ) (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q ((1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((1 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((p1pleaf.2 - p0.2 = (if true = true then
            (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((1 : Fin (3 : ℕ)) + (2 :
            Fin (3 : ℕ))).succ) (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (q ((1 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((1 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (p1pleaf - p0 = sOff (BandVectors.2 (q 1)
            (q 3)))) ) := by
  classical
  intro q sOff p0 p1pleaf hp1px hp1py
  apply Prod.ext
  · dsimp [sOff]
    simpa [Fin.add_def] using hp1px
  · dsimp [sOff]
    simpa [Fin.add_def] using hp1py

private theorem hdelta0m :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p0 : ℝ × ℝ), ∀ (p0mleaf : ℝ × ℝ), (p0mleaf.1 - p0.1 = (if false = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) + (2 : Fin (3
            : ℕ))).succ) (q ((0 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((0 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((p0mleaf.2 - p0.2 = (if false = true
            then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) +
            (2 : Fin (3 : ℕ))).succ) (q ((0 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (q ((0 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((0 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (p0mleaf - p0 = -sOff B)) ) := by
  classical
  intro q B sOff p0 p0mleaf hp0mx hp0my
  apply Prod.ext
  · dsimp [sOff, B]
    simpa [Fin.add_def] using hp0mx
  · dsimp [sOff, B]
    simpa [Fin.add_def] using hp0my

private theorem hpair21base :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        (BandVectors.2 (q 1) (q 3) = -A - B) → (∀ (p0 : ℝ × ℝ), ∀ (p1pleaf : ℝ × ℝ), ∀ (p0mleaf :
            ℝ × ℝ), (p1pleaf - p0 = sOff (BandVectors.2 (q 1) (q 3))) → ((p0mleaf - p0 = -sOff B)
            → (p1pleaf - p0mleaf = -sOff A))) ) := by
  classical
  intro q A B sOff hA p0 p1pleaf p0mleaf hdelta1p hdelta0m
  calc
    _ = (p1pleaf - p0) - (p0mleaf - p0) := by ext <;> dsimp <;> ring
    _ = sOff (BandVectors.2 (q 1) (q 3)) - (-sOff B) := by
      rw [hdelta1p, hdelta0m]
    _ = -sOff A := by rw [hA]; dsimp [A, B, sOff]; ext <;> norm_num <;> ring

private theorem hflip12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        (BandVectors.1 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (Fin.succ
            (1 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (cfg.firstPredecessor (Fin.succ (1 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ))) ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (Fin.succ (1 : Fin (3 : ℕ)))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (cfg.firstPredecessor (Fin.succ (1 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ)))) → (BandVectors.1 (q 1) (q 2) = I * U) ) := by
  classical
  intro q cfg I U hflip12pair
  have hflip := hflip12pair.1
  change BandVectors.1 (cfg.firstPredecessor 0)
      (cfg.firstPredecessor 2) = I * BandVectors.1
        (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) at hflip
  rw [cfg.firstVectorTwo, cfg.firstChild, cfg.firstParentTwo] at hflip
  exact hflip

private theorem hsumV12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        (BandVectors.1 (q 1) (q 2) = I * U) → (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 2) = (1 + I) * U) ) := by
  classical
  intro q cfg I U hflip12
  rw [cfg.firstVectorTwo, cfg.firstChild, cfg.firstParentTwo, hflip12]
  ring

private theorem hc1plus :
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
        TileCentroid (P 1 true) - TileCentroid T = cOff (BandVectors.1 (q 1) (q 3))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data cOff
  simpa [cOff, Fin.add_def] using data.hPcent 1 true

private theorem hcent21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (BandVectors.1 (q 1) (q 3) = -U - W) → ((BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 2) = (1 + I) * U) → ((TileCentroid (P 1 true) - TileCentroid T
            = cOff (BandVectors.1 (q 1) (q 3))) → ((TileCentroid (P 0 false) - TileCentroid T =
            -cOff W) → (TileCentroid (P 1 true) - TileCentroid (P 0 false) = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2))))))) ) := by
  classical
  intro q cfg T P I U W cOff hW hsumV12 hc1plus hc0minus
  have hbase : TileCentroid (P 1 true) - TileCentroid (P 0 false) =
      -cOff U := by
    calc
      _ = (TileCentroid (P 1 true) - TileCentroid T) -
          (TileCentroid (P 0 false) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by
        rw [hc1plus, hc0minus, hW]
        dsimp [cOff, GaussianRealPoint, U, W]
        ext <;> push_cast <;> ring
  rw [hbase, hsumV12]
  dsimp [cOff, GaussianRealPoint, U, I, Prod.smul_mk,
    Prod.add_def, Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hslope21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = (1 - I) * A) → (∀ (p1pleaf : ℝ ×
            ℝ), ∀ (p0mleaf : ℝ × ℝ), (p1pleaf - p0mleaf = -sOff A) → (p1pleaf - p0mleaf = (1 / 2
            : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) * (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2))))) ) := by
  classical
  intro q cfg I A sOff hsumA12 p1pleaf p0mleaf hpair21base
  rw [hpair21base, hsumA12]
  dsimp [sOff, GaussianRealPoint, A, I, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem adj21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (hpos2 : 0 < (q 2).1), ∀ (hpos1 : 0 < (q 1).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl hpos1, q, cfg.proper.1, 1, rfl⟩, hpos1⟩
        let C2 : BandCircle := ⟨⟨q 2, Or.inl hpos2, q, cfg.proper.1, 2, rfl⟩, hpos2⟩
        ∀ (p1pleaf : ℝ × ℝ), (PartialOdometerSlope (r (1 : Fin (3 : ℕ)) true) = some p1pleaf) →
            (∀ (p0mleaf : ℝ × ℝ), (PartialOdometerSlope (r (0 : Fin (3 : ℕ)) false) = some
            p0mleaf) → ((TileCentroid (P 1 true) - TileCentroid (P 0 false) = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → ((p1pleaf - p0mleaf = (1 / 2 :
            Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) * (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → (SubtileLatticeAdjacent C1 C2
            (P 0 false) (P 1 true) (r 0 false) (r 1 true)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data hpos2 hpos1 C1 C2 p1pleaf hp1pleaf p0mleaf hp0mleaf
      hcent21 hslope21
  refine ⟨?_, ?_, ⟨p0mleaf, p1pleaf, hp0mleaf, hp1pleaf, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using data.hP 0 false
  · simpa [C2, cfg.firstParentTwo] using data.hP 1 true
  refine ⟨cfg.firstPredecessor, 1, 1, cfg.firstProper, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C2] using cfg.firstParentTwo
  · simpa using hcent21
  · exact congrArg Prod.fst hslope21
  · exact congrArg Prod.snd hslope21

private theorem hdelta2p :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p0 : ℝ × ℝ), ∀ (p2pleaf : ℝ × ℝ), (p2pleaf.1 - p0.1 = (if true = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3
            : ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ) -
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((p2pleaf.2 - p0.2 = (if true = true then
            (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 :
            Fin (3 : ℕ))).succ) (q ((2 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (q ((2 : Fin (3 : ℕ)) + (2 : Fin (3 : ℕ))).succ) (q ((2 : Fin (3 :
            ℕ)) + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (p2pleaf - p0 = sOff A)) ) := by
  classical
  intro q A sOff p0 p2pleaf hp2px hp2py
  apply Prod.ext
  · dsimp [sOff, A]
    simpa [Fin.add_def] using hp2px
  · dsimp [sOff, A]
    simpa [Fin.add_def] using hp2py

private theorem hpair31base :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p0 : ℝ × ℝ), ∀ (p0mleaf : ℝ × ℝ), (p0mleaf - p0 = -sOff B) → (∀ (p2pleaf : ℝ × ℝ),
            (p2pleaf - p0 = sOff A) → (p2pleaf - p0mleaf = sOff (A + B))) ) := by
  classical
  intro q A B sOff p0 p0mleaf hdelta0m p2pleaf hdelta2p
  calc
    _ = (p2pleaf - p0) - (p0mleaf - p0) := by ext <;> dsimp <;> ring
    _ = sOff A - (-sOff B) := by rw [hdelta2p, hdelta0m]
    _ = sOff (A + B) := by
      dsimp [sOff]
      ext <;> norm_num <;> ring

private theorem hcent31 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 + I) * (I * (U + W))) →
            ((TileCentroid (P 0 false) - TileCentroid T = -cOff W) → ((TileCentroid (P 2 true) -
            TileCentroid T = cOff U) → (TileCentroid (P 2 true) - TileCentroid (P 0 false) = (1 /
            2 : Real) • GaussianRealPoint (((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat)) * (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))))) ) := by
  classical
  intro q cfg T P I U W cOff hsumV03 hc0minus hc2plus
  have hbase : TileCentroid (P 2 true) - TileCentroid (P 0 false) =
      cOff (U + W) := by
    calc
      _ = (TileCentroid (P 2 true) - TileCentroid T) -
          (TileCentroid (P 0 false) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc2plus, hc0minus]; dsimp [cOff, GaussianRealPoint, U, W]; ext <;>
          push_cast <;> ring
  rw [hbase, hsumV03]
  dsimp [cOff, GaussianRealPoint, I, U, W, Prod.smul_mk,
    Prod.add_def, Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hslope31 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        (BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 - I) * (-I * (A + B))) → (∀
            (p0mleaf : ℝ × ℝ), ∀ (p2pleaf : ℝ × ℝ), (p2pleaf - p0mleaf = sOff (A + B)) → (p2pleaf
            - p0mleaf = (1 / 2 : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (2 : Nat))
            * (BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3))))) ) := by
  classical
  intro q cfg I A B sOff hsumA03 p0mleaf p2pleaf hpair31base
  rw [hpair31base, hsumA03]
  dsimp [sOff, GaussianRealPoint, I, A, B, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring

private theorem adj31 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (hpos3 : 0 < (q 3).1), ∀ (hpos1 : 0 < (q 1).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl hpos1, q, cfg.proper.1, 1, rfl⟩, hpos1⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl hpos3, q, cfg.proper.1, 3, rfl⟩, hpos3⟩
        ∀ (p0mleaf : ℝ × ℝ), (PartialOdometerSlope (r (0 : Fin (3 : ℕ)) false) = some p0mleaf) →
            (∀ (p2pleaf : ℝ × ℝ), (PartialOdometerSlope (r (2 : Fin (3 : ℕ)) true) = some
            p2pleaf) → ((TileCentroid (P 2 true) - TileCentroid (P 0 false) = (1 / 2 : Real) •
            GaussianRealPoint (((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat)) * (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) → ((p2pleaf - p0mleaf = (1 / 2 :
            Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (2 : Nat)) * (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) → (SubtileLatticeAdjacent C1 C3
            (P 0 false) (P 2 true) (r 0 false) (r 2 true)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data hpos3 hpos1 C1 C3 p0mleaf hp0mleaf p2pleaf hp2pleaf
      hcent31 hslope31
  refine ⟨?_, ?_, ⟨p0mleaf, p2pleaf, hp0mleaf, hp2pleaf, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using data.hP 0 false
  · simpa [C3, cfg.firstParentThree] using data.hP 2 true
  refine ⟨cfg.firstPredecessor, 2, 2, cfg.firstProper, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C3] using cfg.firstParentThree
  · simpa using hcent31
  · exact congrArg Prod.fst hslope31
  · exact congrArg Prod.snd hslope31

private theorem hsumVsecond :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = I * BandVectors.1 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → (BandVectors.1 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 + I) * W) ) := by
  classical
  intro q cfg I W hflipV
  rw [cfg.secondVectorOne, cfg.secondChild, cfg.secondParentOne, hflipV]
  ring

private theorem hsumAsecond :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -I * BandVectors.2 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 - I) * B) ) := by
  classical
  intro q cfg I B hflipA
  rw [cfg.secondParentOne, cfg.secondChild, hflipA]
  ring

private theorem hpair23base :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        (BandVectors.2 (q 1) (q 3) = -A - B) → (∀ (p0 : ℝ × ℝ), ∀ (p2leaf : ℝ × ℝ), (p2leaf - p0
            = -sOff A) → (∀ (p1pleaf : ℝ × ℝ), (p1pleaf - p0 = sOff (BandVectors.2 (q 1) (q 3)))
            → (p2leaf - p1pleaf = sOff B))) ) := by
  classical
  intro q A B sOff hA p0 p2leaf hdelta2 p1pleaf hdelta1p
  calc
    _ = (p2leaf - p0) - (p1pleaf - p0) := by ext <;> dsimp <;> ring
    _ = -sOff A - sOff (BandVectors.2 (q 1) (q 3)) := by
      rw [hdelta2, hdelta1p]
    _ = sOff B := by rw [hA]; dsimp [A, B, sOff]; ext <;> push_cast <;> ring

private theorem hcent23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (BandVectors.1 (q 1) (q 3) = -U - W) → ((TileCentroid (P 2 false) - TileCentroid T =
            -cOff U) → ((TileCentroid (P 1 true) - TileCentroid T = cOff (BandVectors.1 (q 1) (q
            3))) → ((BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = (1 + I) * W) →
            (TileCentroid (P 2 false) - TileCentroid (P 1 true) = (1 / 2 : Real) •
            GaussianRealPoint (((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) * (BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))))) ) := by
  classical
  intro q cfg T P I U W cOff hW hc2minus hc1plus hsumVsecond
  have hbase : TileCentroid (P 2 false) - TileCentroid (P 1 true) = cOff W := by
    calc
      _ = (TileCentroid (P 2 false) - TileCentroid T) -
          (TileCentroid (P 1 true) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by
        rw [hc2minus, hc1plus, hW]
        dsimp [cOff, GaussianRealPoint, U, W]
        ext <;> push_cast <;> ring
  rw [hbase, hsumVsecond]
  dsimp [cOff, GaussianRealPoint, W, I, Prod.smul_mk,
    Prod.add_def, Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hslope23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p2leaf : ℝ × ℝ), ∀ (p1pleaf : ℝ × ℝ), (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 - I) * B) → ((p2leaf - p1pleaf = sOff B) → (p2leaf -
            p1pleaf = (1 / 2 : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) *
            (BandVectors.2 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))) ) := by
  classical
  intro q cfg I B sOff p2leaf p1pleaf hsumAsecond hpair23base
  rw [hpair23base, hsumAsecond]
  dsimp [sOff, GaussianRealPoint, I, B, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hpair32base :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates),
        let A : GaussianInt := BandVectors.2 (q 2) (q 1)
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        (BandVectors.2 (q 1) (q 3) = -A - B) → (∀ (p0 : ℝ × ℝ), ∀ (p1leaf : ℝ × ℝ), (p1leaf - p0
            = -sOff (BandVectors.2 (q 1) (q 3))) → (∀ (p2pleaf : ℝ × ℝ), (p2pleaf - p0 = sOff A)
            → (p2pleaf - p1leaf = -sOff B))) ) := by
  classical
  intro q A B sOff hA p0 p1leaf hdelta1 p2pleaf hdelta2p
  calc
    _ = (p2pleaf - p0) - (p1leaf - p0) := by ext <;> dsimp <;> ring
    _ = sOff A - sOff (A + B) := by
      rw [hdelta2p, hdelta1, hA]
      dsimp [sOff, A, B]
      ext <;> push_cast <;> ring
    _ = -sOff B := by dsimp [sOff]; ext <;> push_cast <;> ring

private theorem hcent32 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin 3 -> Bool -> ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let U : GaussianInt := BandVectors.1 (q 2) (q 1)
        let W : GaussianInt := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (BandVectors.1 (q 1) (q 3) = -U - W) → ((TileCentroid (P 1 false) - TileCentroid T =
            -cOff (BandVectors.1 (q 1) (q 3))) → ((TileCentroid (P 2 true) - TileCentroid T =
            cOff U) → ((BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = (1 + I) * W) →
            (TileCentroid (P 2 true) - TileCentroid (P 1 false) = (1 / 2 : Real) •
            GaussianRealPoint (((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) * (BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))))) ) := by
  classical
  intro q cfg T P I U W cOff hW hc1minus hc2plus hsumVsecond
  have hbase : TileCentroid (P 2 true) - TileCentroid (P 1 false) = -cOff W := by
    calc
      _ = (TileCentroid (P 2 true) - TileCentroid T) -
          (TileCentroid (P 1 false) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by
        rw [hc2plus, hc1minus, hW]
        dsimp [cOff, GaussianRealPoint, U, W]
        ext <;> push_cast <;> ring
  rw [hbase, hsumVsecond]
  dsimp [cOff, GaussianRealPoint, W, I, Prod.smul_mk,
    Prod.add_def, Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hslope32 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B : GaussianInt := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) •
            (((z.re : Int) : Real) - ((z.im : Int) : Real),
              ((z.im : Int) : Real) + ((z.re : Int) : Real))
        ∀ (p1leaf : ℝ × ℝ), ∀ (p2pleaf : ℝ × ℝ), (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 - I) * B) → ((p2pleaf - p1leaf = -sOff B) → (p2pleaf -
            p1leaf = (1 / 2 : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) *
            (BandVectors.2 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))) ) := by
  classical
  intro q cfg I B sOff p1leaf p2pleaf hsumAsecond hpair32base
  rw [hpair32base, hsumAsecond]
  dsimp [sOff, GaussianRealPoint, I, B, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem adj23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (hpos2 : 0 < (q 2).1), ∀ (hpos3 : 0 < (q 3).1),
        let C2 : BandCircle := ⟨⟨q 2, Or.inl hpos2, q, cfg.proper.1, 2, rfl⟩, hpos2⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl hpos3, q, cfg.proper.1, 3, rfl⟩, hpos3⟩
        ∀ (p2leaf : ℝ × ℝ), (PartialOdometerSlope (r (2 : Fin (3 : ℕ)) false) = some p2leaf) → (∀
            (p1pleaf : ℝ × ℝ), (PartialOdometerSlope (r (1 : Fin (3 : ℕ)) true) = some p1pleaf) →
            ((TileCentroid (P 2 false) - TileCentroid (P 1 true) = (1 / 2 : Real) •
            GaussianRealPoint (((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) * (BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → ((p2leaf - p1pleaf = (1 / 2
            : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) * (BandVectors.2
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → (SubtileLatticeAdjacent C2
            C3 (P 1 true) (P 2 false) (r 1 true) (r 2 false)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data hpos2 hpos3 C2 C3 p2leaf hp2leaf p1pleaf hp1pleaf
      hcent23 hslope23
  refine ⟨?_, ?_, ⟨p1pleaf, p2leaf, hp1pleaf, hp2leaf, ?_⟩⟩
  · simpa [C2, cfg.secondChild, cfg.firstParentTwo] using data.hP 1 true
  · simpa [C3, cfg.secondParentOne, cfg.firstParentThree] using data.hP 2 false
  refine ⟨cfg.secondPredecessor, 0, 3, cfg.secondProper, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C2] using cfg.secondChild
  · simpa [C3] using cfg.secondParentOne
  · simpa using hcent23
  · exact congrArg Prod.fst hslope23
  · exact congrArg Prod.snd hslope23

private theorem adj32 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (hpos2 : 0 < (q 2).1), ∀ (hpos3 : 0 < (q 3).1),
        let C2 : BandCircle := ⟨⟨q 2, Or.inl hpos2, q, cfg.proper.1, 2, rfl⟩, hpos2⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl hpos3, q, cfg.proper.1, 3, rfl⟩, hpos3⟩
        ∀ (p1leaf : ℝ × ℝ), (PartialOdometerSlope (r (1 : Fin (3 : ℕ)) false) = some p1leaf) → (∀
            (p2pleaf : ℝ × ℝ), (PartialOdometerSlope (r (2 : Fin (3 : ℕ)) true) = some p2pleaf) →
            ((TileCentroid (P 2 true) - TileCentroid (P 1 false) = (1 / 2 : Real) •
            GaussianRealPoint (((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) * (BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → ((p2pleaf - p1leaf = (1 / 2
            : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) * (BandVectors.2
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → (SubtileLatticeAdjacent C2
            C3 (P 1 false) (P 2 true) (r 1 false) (r 2 true)))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data hpos2 hpos3 C2 C3 p1leaf hp1leaf p2pleaf hp2pleaf
      hcent32 hslope32
  refine ⟨?_, ?_, ⟨p1leaf, p2pleaf, hp1leaf, hp2pleaf, ?_⟩⟩
  · simpa [C2, cfg.secondChild, cfg.firstParentTwo] using data.hP 1 false
  · simpa [C3, cfg.secondParentOne, cfg.firstParentThree] using data.hP 2 true
  refine ⟨cfg.secondPredecessor, 0, 1, cfg.secondProper, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C2] using cfg.secondChild
  · simpa [C3] using cfg.secondParentOne
  · simpa using hcent32
  · exact congrArg Prod.fst hslope32
  · exact congrArg Prod.snd hslope32

private theorem translatedObs :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (∀ (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt),
            FootprintVertices (TileTranslation (P i s) d) = FootprintVertices (TileTranslation
            (cert.P i s) d)) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data i s d
  rw [(TileTranslationFormulas (P i s) d).2.2.2.2.2.1,
    (TileTranslationFormulas (cert.P i s) d).2.2.2.2.2.1,
    (data.hobsP i s).2.1]

private theorem finish :
    (by
      classical
      exact
        ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), ∀ (marked : Bool), ∀ (leftTile :
            ProtoTile), ∀ (rightTile : ProtoTile), ∀ (leftOdo : PartialOdometer), ∀ (rightOdo :
            PartialOdometer), ∀ (leftCircle : BandCircle), ∀ (rightCircle : BandCircle), ∀ (tuple
            : Fin 4 → CircleCoordinates), ∀ (slot : Fin 3), ∀ (rot : Fin 4), ∀ (pL : Real ×
            Real), ∀ (pR : Real × Real), (ProperBandQuadruple tuple) → ((tuple 0 =
            leftCircle.1.1) → ((tuple slot.succ = rightCircle.1.1) → ((PartialOdometerSlope
            leftOdo = some pL) → ((PartialOdometerSlope rightOdo = some pR) → ((TileCentroid
            rightTile - TileCentroid leftTile =
            (1 / 2 : Real) • GaussianRealPoint
              ((⟨0, 1⟩ : GaussianInt) ^ rot.val *
                (BandVectors.1 (tuple slot.succ) (tuple 0) +
                  BandVectors.1 (tuple 0) (tuple slot.succ)))) → ((pR.1 - pL.1 = ((1 / 2 : Real)
                      • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ rot.val *
              (BandVectors.2 (tuple slot.succ) (tuple 0) +
                BandVectors.2 (tuple 0) (tuple slot.succ)))).1) → ((pR.2 - pL.2 = ((1 / 2 : Real)
                    • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ rot.val *
              (BandVectors.2 (tuple slot.succ) (tuple 0) +
                BandVectors.2 (tuple 0) (tuple slot.succ)))).2) → ((SubtileLatticeAdjacent
                    leftCircle rightCircle leftTile rightTile leftOdo rightOdo) →
                    ((GlobalOdometerExtends g leftOdo) → ((GlobalOdometerExtends g rightOdo) →
                    ((OdometerCompatibility leftOdo rightOdo) → ((x ∈ FootprintVertices leftTile)
                    → ((x ∈ FootprintVertices rightTile) → ((∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
              y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
            y ∈ FootprintVertices leftTile ∨ y ∈ FootprintVertices rightTile) → ((x ∈
                FootprintVertices
            (TileTranslation leftTile
              ((⟨0, 1⟩ : GaussianInt) ^ rot.val *
                (if Even rot.val then BandVectors.1 (tuple 0) (tuple slot.succ)
                 else BandVectors.1 (tuple slot.succ) (tuple 0)))) ↔ marked = true) → ((marked =
                     true → FourNeighborLaplacian g x = 0) ∧ (marked = false →
                     FourNeighborLaplacian g x = 1))))))))))))))))) ) := by
  classical
  intro g x marked leftTile rightTile leftOdo rightOdo leftCircle rightCircle tuple slot rot pL
      pR proper tupleRoot tupleChild hrootSlope hchildSlope hcent hslopeRe hslopeIm adj leftExt
      rightExt compat leftMem rightMem star companion
  have domL := PositiveCurvatureTileOdometerDomain leftCircle.1.1 leftTile leftOdo
    leftCircle.2 adj.1
  have domR := PositiveCurvatureTileOdometerDomain rightCircle.1.1 rightTile rightOdo
    rightCircle.2 adj.2.1
  have web := (OdometerWeb).2 leftCircle rightCircle tuple slot rot leftTile rightTile
    leftOdo rightOdo g x pL pR proper tupleRoot tupleChild hrootSlope hchildSlope
    hcent hslopeRe hslopeIm adj compat leftExt rightExt
    (by change x ∈ (leftOdo.domain : Set GaussianInt); rw [domL]; exact leftMem)
    (by change x ∈ (rightOdo.domain : Set GaussianInt); rw [domR]; exact rightMem)
    (by intro y hy; change y ∈ (leftOdo.domain : Set GaussianInt) ∨
        y ∈ (rightOdo.domain : Set GaussianInt)
        rw [domL, domR]; exact star y hy)
  constructor
  · intro hm
    exact web.1 (companion.mpr hm)
  · intro hm
    exact web.2 (fun hmem => by
      have := companion.mp hmem
      simp [hm] at this)

private theorem star'At871 :
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
            FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.P (1
            : Fin (3 : ℕ)) false)) → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x
            - ⟨0, 1⟩ → y ∈ FootprintVertices (P 0 true) ∨ y ∈ FootprintVertices (P 1 false))) )
            := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star
  simpa [(data.hobsP 0 true).2.1, (data.hobsP 1 false).2.1] using star

private theorem compAt875 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool), (∀
            (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), FootprintVertices (TileTranslation (P
            i s) d) = FootprintVertices (TileTranslation (cert.P i s) d)) → ((x ∈
            FootprintVertices (TileTranslation (cert.P (0 : Fin (3 : ℕ)) true) ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (3 : ℕ) * if Even (3 : ℕ) then BandVectors.1
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            else BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (0
            : Fin (4 : ℕ))))) ↔ marked = true) → (x ∈ FootprintVertices (TileTranslation (P 0
            true) ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * (if Even (3 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) else BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0)))) ↔ marked = true)) ) := by
  classical
  intro q cfg C0 T cert P x marked translatedObs webCompanion
  rw [translatedObs]
  simpa [Even] using webCompanion

private theorem star'At896 :
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
            FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.P (2
            : Fin (3 : ℕ)) false)) → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x
            - ⟨0, 1⟩ → y ∈ FootprintVertices (P 0 true) ∨ y ∈ FootprintVertices (P 2 false))) )
            := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star
  simpa [(data.hobsP 0 true).2.1, (data.hobsP 2 false).2.1] using star

private theorem compAt900 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool), (∀
            (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), FootprintVertices (TileTranslation (P
            i s) d) = FootprintVertices (TileTranslation (cert.P i s) d)) → ((x ∈
            FootprintVertices (TileTranslation (cert.P (0 : Fin (3 : ℕ)) true) ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (0 : ℕ) * if Even (0 : ℕ) then BandVectors.1
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))
            else BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (0
            : Fin (4 : ℕ))))) ↔ marked = true) → (x ∈ FootprintVertices (TileTranslation (P 0
            true) ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) * (if Even (0 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) else BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)))) ↔ marked = true)) ) := by
  classical
  intro q cfg C0 T cert P x marked translatedObs webCompanion
  rw [translatedObs]
  simpa [Even] using webCompanion

private theorem star'At922 :
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
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.P (0
            : Fin (3 : ℕ)) false)) → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x
            - ⟨0, 1⟩ → y ∈ FootprintVertices (P 0 false) ∨ y ∈ FootprintVertices (P 1 true))) )
            := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star y hy
  rcases star y hy with hL | hR
  · exact Or.inr (by simpa [(data.hobsP 1 true).2.1] using hL)
  · exact Or.inl (by simpa [(data.hobsP 0 false).2.1] using hR)

private theorem compAt929 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool), (∀
            (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), FootprintVertices (TileTranslation (P
            i s) d) = FootprintVertices (TileTranslation (cert.P i s) d)) → ((x ∈
            FootprintVertices (TileTranslation (cert.P (0 : Fin (3 : ℕ)) false) ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (1 : ℕ) * if Even (1 : ℕ) then BandVectors.1
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            else BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (0
            : Fin (4 : ℕ))))) ↔ marked = true) → (x ∈ FootprintVertices (TileTranslation (P 0
            false) ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * (if Even (1 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) else BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0)))) ↔ marked = true)) ) := by
  classical
  intro q cfg C0 T cert P x marked translatedObs webCompanion
  rw [translatedObs]
  simpa [Even] using webCompanion

private theorem star'At950 :
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
            FootprintVertices (cert.P (2 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.P (0
            : Fin (3 : ℕ)) false)) → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x
            - ⟨0, 1⟩ → y ∈ FootprintVertices (P 0 false) ∨ y ∈ FootprintVertices (P 2 true))) )
            := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star y hy
  rcases star y hy with hL | hR
  · exact Or.inr (by simpa [(data.hobsP 2 true).2.1] using hL)
  · exact Or.inl (by simpa [(data.hobsP 0 false).2.1] using hR)

private theorem compAt957 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool), (∀
            (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), FootprintVertices (TileTranslation (P
            i s) d) = FootprintVertices (TileTranslation (cert.P i s) d)) → ((x ∈
            FootprintVertices (TileTranslation (cert.P (0 : Fin (3 : ℕ)) false) ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (2 : ℕ) * if Even (2 : ℕ) then BandVectors.1
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))
            else BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ))) (cfg.firstPredecessor (0
            : Fin (4 : ℕ))))) ↔ marked = true) → (x ∈ FootprintVertices (TileTranslation (P 0
            false) ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * (if Even (2 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) else BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)))) ↔ marked = true)) ) := by
  classical
  intro q cfg C0 T cert P x marked translatedObs webCompanion
  rw [translatedObs]
  simpa [Even] using webCompanion

private theorem star'At978 :
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
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.P (2
            : Fin (3 : ℕ)) false)) → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x
            - ⟨0, 1⟩ → y ∈ FootprintVertices (P 1 true) ∨ y ∈ FootprintVertices (P 2 false))) )
            := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star
  simpa [(data.hobsP 1 true).2.1, (data.hobsP 2 false).2.1] using star

private theorem compAt982 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool), (∀
            (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), FootprintVertices (TileTranslation (P
            i s) d) = FootprintVertices (TileTranslation (cert.P i s) d)) → ((x ∈
            FootprintVertices (TileTranslation (cert.P (1 : Fin (3 : ℕ)) true) ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (3 : ℕ) * if Even (3 : ℕ) then BandVectors.1
            (cfg.secondPredecessor (0 : Fin (4 : ℕ))) (cfg.secondPredecessor (1 : Fin (4 : ℕ)))
            else BandVectors.1 (cfg.secondPredecessor (1 : Fin (4 : ℕ))) (cfg.secondPredecessor
            (0 : Fin (4 : ℕ))))) ↔ marked = true) → (x ∈ FootprintVertices (TileTranslation (P 1
            true) ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * (if Even (3 : Nat) then BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) else BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))) ↔ marked = true)) ) := by
  classical
  intro q cfg C0 T cert P x marked translatedObs webCompanion
  rw [translatedObs]
  simpa [Even] using webCompanion

private theorem star'At1004 :
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
            FootprintVertices (cert.P (2 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.P (1
            : Fin (3 : ℕ)) false)) → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x
            - ⟨0, 1⟩ → y ∈ FootprintVertices (P 1 false) ∨ y ∈ FootprintVertices (P 2 true))) )
            := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x data star y hy
  rcases star y hy with hL | hR
  · exact Or.inr (by simpa [(data.hobsP 2 true).2.1] using hL)
  · exact Or.inl (by simpa [(data.hobsP 1 false).2.1] using hR)

private theorem compAt1011 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (x : GaussianInt), ∀ (marked : Bool), (∀
            (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), FootprintVertices (TileTranslation (P
            i s) d) = FootprintVertices (TileTranslation (cert.P i s) d)) → ((x ∈
            FootprintVertices (TileTranslation (cert.P (1 : Fin (3 : ℕ)) false) ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (1 : ℕ) * if Even (1 : ℕ) then BandVectors.1
            (cfg.secondPredecessor (0 : Fin (4 : ℕ))) (cfg.secondPredecessor (1 : Fin (4 : ℕ)))
            else BandVectors.1 (cfg.secondPredecessor (1 : Fin (4 : ℕ))) (cfg.secondPredecessor
            (0 : Fin (4 : ℕ))))) ↔ marked = true) → (x ∈ FootprintVertices (TileTranslation (P 1
            false) ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * (if Even (1 : Nat) then BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) else BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))) ↔ marked = true)) ) := by
  classical
  intro q cfg C0 T cert P x marked translatedObs webCompanion
  rw [translatedObs]
  simpa [Even] using webCompanion

end OuterMixedOdometerGeometry

namespace OuterMixedOdometerConclusion

private theorem outerMixedConclusion :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), ∀ (marked :
            Bool), (BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g) → (∀ (row
            : BandOrderedGeneralInteriorWebRow cert x marked), ((exists (left_mem : x ∈
            FootprintVertices (cert.P 0 true)) (right_mem : x ∈ FootprintVertices (cert.P 1
            false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/ y = x + ⟨0, 1⟩ \/ y = x
            - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.P 0 true) \/ y ∈ FootprintVertices (cert.P 1
            false)) (coarseThird : x ∈ FootprintVertices (cert.P 0 false) <-> marked = true)
            (webCompanion : x ∈ FootprintVertices (TileTranslation (cert.P 0 true) ((⟨0, 1⟩ :
            GaussianInt) ^ (3 : Nat) * (if Even (3 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) else BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0)))) <-> marked = true), row =
            .outer12 left_mem right_mem star coarseThird webCompanion) \/ (exists (left_mem : x ∈
            FootprintVertices (cert.P 0 true)) (right_mem : x ∈ FootprintVertices (cert.P 2
            false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/ y = x + ⟨0, 1⟩ \/ y = x
            - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.P 0 true) \/ y ∈ FootprintVertices (cert.P 2
            false)) (coarseThird : x ∈ FootprintVertices (cert.P 1 true) <-> marked = true)
            (webCompanion : x ∈ FootprintVertices (TileTranslation (cert.P 0 true) ((⟨0, 1⟩ :
            GaussianInt) ^ (0 : Nat) * (if Even (0 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) else BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)))) <-> marked = true), row =
            .outer13 left_mem right_mem star coarseThird webCompanion) \/ (exists (left_mem : x ∈
            FootprintVertices (cert.P 1 true)) (right_mem : x ∈ FootprintVertices (cert.P 0
            false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/ y = x + ⟨0, 1⟩ \/ y = x
            - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.P 1 true) \/ y ∈ FootprintVertices (cert.P 0
            false)) (coarseThird : x ∈ FootprintVertices (cert.P 0 true) <-> marked = true)
            (webCompanion : x ∈ FootprintVertices (TileTranslation (cert.P 0 false) ((⟨0, 1⟩ :
            GaussianInt) ^ (1 : Nat) * (if Even (1 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) else BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0)))) <-> marked = true), row =
            .outer21 left_mem right_mem star coarseThird webCompanion) \/ (exists (left_mem : x ∈
            FootprintVertices (cert.P 2 true)) (right_mem : x ∈ FootprintVertices (cert.P 0
            false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/ y = x + ⟨0, 1⟩ \/ y = x
            - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.P 2 true) \/ y ∈ FootprintVertices (cert.P 0
            false)) (coarseThird : x ∈ FootprintVertices (cert.P 1 false) <-> marked = true)
            (webCompanion : x ∈ FootprintVertices (TileTranslation (cert.P 0 false) ((⟨0, 1⟩ :
            GaussianInt) ^ (2 : Nat) * (if Even (2 : Nat) then BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) else BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)))) <-> marked = true), row =
            .outer31 left_mem right_mem star coarseThird webCompanion) \/ (exists (left_mem : x ∈
            FootprintVertices (cert.P 1 true)) (right_mem : x ∈ FootprintVertices (cert.P 2
            false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/ y = x + ⟨0, 1⟩ \/ y = x
            - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.P 1 true) \/ y ∈ FootprintVertices (cert.P 2
            false)) (coarseThird : x ∈ FootprintVertices (cert.P 0 true) <-> marked = true)
            (webCompanion : x ∈ FootprintVertices (TileTranslation (cert.P 1 true) ((⟨0, 1⟩ :
            GaussianInt) ^ (3 : Nat) * (if Even (3 : Nat) then BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) else BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))) <-> marked = true), row =
            .outer23 left_mem right_mem star coarseThird webCompanion) \/ (exists (left_mem : x ∈
            FootprintVertices (cert.P 2 true)) (right_mem : x ∈ FootprintVertices (cert.P 1
            false)) (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/ y = x + ⟨0, 1⟩ \/ y = x
            - ⟨0, 1⟩ -> y ∈ FootprintVertices (cert.P 2 true) \/ y ∈ FootprintVertices (cert.P 1
            false)) (coarseThird : x ∈ FootprintVertices (cert.P 0 false) <-> marked = true)
            (webCompanion : x ∈ FootprintVertices (TileTranslation (cert.P 1 false) ((⟨0, 1⟩ :
            GaussianInt) ^ (1 : Nat) * (if Even (1 : Nat) then BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) else BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0)))) <-> marked = true), row =
            .outer32 left_mem right_mem star coarseThird webCompanion)) → (∀ (hpos2 : 0 < (q
            2).1), ∀ (hpos3 : 0 < (q 3).1), ∀ (hpos1 : 0 < (q 1).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl hpos1, q, cfg.proper.1, 1, rfl⟩, hpos1⟩
        let C2 : BandCircle := ⟨⟨q 2, Or.inl hpos2, q, cfg.proper.1, 2, rfl⟩, hpos2⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl hpos3, q, cfg.proper.1, 3, rfl⟩, hpos3⟩
        ∀ (p0leaf : ℝ × ℝ), (PartialOdometerSlope (r (0 : Fin (3 : ℕ)) true) = some p0leaf) → (∀
            (p1leaf : ℝ × ℝ), (PartialOdometerSlope (r (1 : Fin (3 : ℕ)) false) = some p1leaf) →
            ((TileCentroid (P 1 false) - TileCentroid (P 0 true) = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → ((p1leaf - p0leaf = (1 / 2 :
            Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) * (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → ((SubtileLatticeAdjacent C1 C2
            (P 0 true) (P 1 false) (r 0 true) (r 1 false)) → (∀ (p2leaf : ℝ × ℝ),
            (PartialOdometerSlope (r (2 : Fin (3 : ℕ)) false) = some p2leaf) → ((TileCentroid (P
            2 false) - TileCentroid (P 0 true) = (1 / 2 : Real) • GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3))) → ((p2leaf - p0leaf = (1 / 2 :
            Real) • GaussianRealPoint (BandVectors.2 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 0) + BandVectors.2 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 3))) → ((SubtileLatticeAdjacent C1 C3 (P 0 true) (P 2 false) (r
            0 true) (r 2 false)) → (∀ (p1pleaf : ℝ × ℝ), (PartialOdometerSlope (r (1 : Fin (3 :
            ℕ)) true) = some p1pleaf) → (∀ (p0mleaf : ℝ × ℝ), (PartialOdometerSlope (r (0 : Fin
            (3 : ℕ)) false) = some p0mleaf) → ((TileCentroid (P 1 true) - TileCentroid (P 0
            false) = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → ((p1pleaf - p0mleaf = (1 / 2 :
            Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) * (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → ((SubtileLatticeAdjacent C1 C2
            (P 0 false) (P 1 true) (r 0 false) (r 1 true)) → (∀ (p2pleaf : ℝ × ℝ),
            (PartialOdometerSlope (r (2 : Fin (3 : ℕ)) true) = some p2pleaf) → ((TileCentroid (P
            2 true) - TileCentroid (P 0 false) = (1 / 2 : Real) • GaussianRealPoint (((⟨0, 1⟩ :
            GaussianInt) ^ (2 : Nat)) * (BandVectors.1 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 3)))) → ((p2pleaf - p0mleaf = (1 / 2 : Real) •
            GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (2 : Nat)) * (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) → ((SubtileLatticeAdjacent C1 C3
            (P 0 false) (P 2 true) (r 0 false) (r 2 true)) → ((TileCentroid (P 2 false) -
            TileCentroid (P 1 true) = (1 / 2 : Real) • GaussianRealPoint (((⟨0, 1⟩ : GaussianInt)
            ^ (3 : Nat)) * (BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → ((p2leaf -
            p1pleaf = (1 / 2 : Real) • GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (3 : Nat)) *
            (BandVectors.2 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → ((TileCentroid (P 2 true) -
            TileCentroid (P 1 false) = (1 / 2 : Real) • GaussianRealPoint (((⟨0, 1⟩ :
            GaussianInt) ^ (1 : Nat)) * (BandVectors.1 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1)))) → ((p2pleaf - p1leaf = (1 / 2 : Real) •
            GaussianRealPoint (((-⟨0, 1⟩ : GaussianInt) ^ (1 : Nat)) * (BandVectors.2
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → ((SubtileLatticeAdjacent C2
            C3 (P 1 true) (P 2 false) (r 1 true) (r 2 false)) → ((SubtileLatticeAdjacent C2 C3 (P
            1 false) (P 2 true) (r 1 false) (r 2 true)) → ((∀ (i : Fin 3), ∀ (s : Bool), ∀ (d :
            GaussianInt), FootprintVertices (TileTranslation (P i s) d) = FootprintVertices
            (TileTranslation (cert.P i s) d)) → ((∀ (leftTile : ProtoTile), ∀ (rightTile :
            ProtoTile), ∀ (leftOdo : PartialOdometer), ∀ (rightOdo : PartialOdometer), ∀
            (leftCircle : BandCircle), ∀ (rightCircle : BandCircle), ∀ (tuple : Fin 4 →
            CircleCoordinates), ∀ (slot : Fin 3), ∀ (rot : Fin 4), ∀ (pL : Real × Real), ∀ (pR :
            Real × Real), (ProperBandQuadruple tuple) → ((tuple 0 = leftCircle.1.1) → ((tuple
            slot.succ = rightCircle.1.1) → ((PartialOdometerSlope leftOdo = some pL) →
            ((PartialOdometerSlope rightOdo = some pR) → ((TileCentroid rightTile - TileCentroid
            leftTile = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ rot.val *
            (BandVectors.1 (tuple slot.succ) (tuple 0) + BandVectors.1 (tuple 0) (tuple
            slot.succ)))) → ((pR.1 - pL.1 = ((1 / 2 : Real) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ rot.val * (BandVectors.2 (tuple slot.succ) (tuple 0) + BandVectors.2
            (tuple 0) (tuple slot.succ)))).1) → ((pR.2 - pL.2 = ((1 / 2 : Real) •
            GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt) ^ rot.val * (BandVectors.2 (tuple
            slot.succ) (tuple 0) + BandVectors.2 (tuple 0) (tuple slot.succ)))).2) →
            ((SubtileLatticeAdjacent leftCircle rightCircle leftTile rightTile leftOdo rightOdo)
            → ((GlobalOdometerExtends g leftOdo) → ((GlobalOdometerExtends g rightOdo) →
            ((OdometerCompatibility leftOdo rightOdo) → ((x ∈ FootprintVertices leftTile) → ((x ∈
            FootprintVertices rightTile) → ((∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩
            ∨ y = x - ⟨0, 1⟩ → y ∈ FootprintVertices leftTile ∨ y ∈ FootprintVertices rightTile)
            → ((x ∈ FootprintVertices (TileTranslation leftTile ((⟨0, 1⟩ : GaussianInt) ^ rot.val
            * (if Even rot.val then BandVectors.1 (tuple 0) (tuple slot.succ) else BandVectors.1
            (tuple slot.succ) (tuple 0)))) ↔ marked = true) → ((marked = true →
            FourNeighborLaplacian g x = 0) ∧ (marked = false → FourNeighborLaplacian g x =
            1)))))))))))))))))) → ((marked = true -> FourNeighborLaplacian g x = 0) /\ (marked =
            false -> FourNeighborLaplacian g x = 1))))))))))))))))))))))))))))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g x marked data row outer hpos2 hpos3 hpos1 C1 C2 C3 p0leaf
      hp0leaf p1leaf hp1leaf hcent12 hslope12 adj12 p2leaf hp2leaf hcent13 hslope13 adj13 p1pleaf
      hp1pleaf p0mleaf hp0mleaf hcent21 hslope21 adj21 p2pleaf hp2pleaf hcent31 hslope31 adj31
      hcent23 hslope23 hcent32 hslope32 adj23 adj32 translatedObs finish
  rcases outer with case12 | case13 | case21 | case31 | case23 | case32
  · obtain ⟨left_mem, right_mem, star, _coarse, webCompanion, _rowEq⟩ := case12
    have leftMem : x ∈ FootprintVertices (P 0 true) := by
      simpa [(data.hobsP 0 true).2.1] using left_mem
    have rightMem : x ∈ FootprintVertices (P 1 false) := by
      simpa [(data.hobsP 1 false).2.1] using right_mem
    have star' := OuterMixedOdometerGeometry.star'At871 q cfg C0 T cert h P r Q S u v g x data
        star
    have comp := OuterMixedOdometerGeometry.compAt875 q cfg C0 T cert P x marked translatedObs
        webCompanion
    exact finish (P 0 true) (P 1 false) (r 0 true) (r 1 false)
      C1 C2 cfg.firstPredecessor 1 3 p0leaf p1leaf cfg.firstProper
      cfg.firstChild cfg.firstParentTwo hp0leaf hp1leaf hcent12
      (congrArg Prod.fst hslope12) (congrArg Prod.snd hslope12) adj12
      (data.hextP 0 true) (data.hextP 1 false)
      (data.hcompat _ _ ⟨0, true, Or.inl rfl⟩ ⟨1, false, Or.inl rfl⟩)
      leftMem rightMem star' comp
  · obtain ⟨left_mem, right_mem, star, _coarse, webCompanion, _rowEq⟩ := case13
    have leftMem : x ∈ FootprintVertices (P 0 true) := by
      simpa [(data.hobsP 0 true).2.1] using left_mem
    have rightMem : x ∈ FootprintVertices (P 2 false) := by
      simpa [(data.hobsP 2 false).2.1] using right_mem
    have star' := OuterMixedOdometerGeometry.star'At896 q cfg C0 T cert h P r Q S u v g x data
        star
    have comp := OuterMixedOdometerGeometry.compAt900 q cfg C0 T cert P x marked translatedObs
        webCompanion
    exact finish (P 0 true) (P 2 false) (r 0 true) (r 2 false)
      C1 C3 cfg.firstPredecessor 2 0 p0leaf p2leaf cfg.firstProper
      cfg.firstChild cfg.firstParentThree hp0leaf hp2leaf (by simpa using hcent13)
      (by simpa using congrArg Prod.fst hslope13)
      (by simpa using congrArg Prod.snd hslope13) adj13
      (data.hextP 0 true) (data.hextP 2 false)
      (data.hcompat _ _ ⟨0, true, Or.inl rfl⟩ ⟨2, false, Or.inl rfl⟩)
      leftMem rightMem star' comp
  · obtain ⟨left_mem, right_mem, star, _coarse, webCompanion, _rowEq⟩ := case21
    have leftMem : x ∈ FootprintVertices (P 0 false) := by
      simpa [(data.hobsP 0 false).2.1] using right_mem
    have rightMem : x ∈ FootprintVertices (P 1 true) := by
      simpa [(data.hobsP 1 true).2.1] using left_mem
    have star' := OuterMixedOdometerGeometry.star'At922 q cfg C0 T cert h P r Q S u v g x data
        star
    have comp := OuterMixedOdometerGeometry.compAt929 q cfg C0 T cert P x marked translatedObs
        webCompanion
    exact finish (P 0 false) (P 1 true) (r 0 false) (r 1 true)
      C1 C2 cfg.firstPredecessor 1 1 p0mleaf p1pleaf cfg.firstProper
      cfg.firstChild cfg.firstParentTwo hp0mleaf hp1pleaf hcent21
      (congrArg Prod.fst hslope21) (congrArg Prod.snd hslope21) adj21
      (data.hextP 0 false) (data.hextP 1 true)
      (data.hcompat _ _ ⟨0, false, Or.inl rfl⟩ ⟨1, true, Or.inl rfl⟩)
      leftMem rightMem star' comp
  · obtain ⟨left_mem, right_mem, star, _coarse, webCompanion, _rowEq⟩ := case31
    have leftMem : x ∈ FootprintVertices (P 0 false) := by
      simpa [(data.hobsP 0 false).2.1] using right_mem
    have rightMem : x ∈ FootprintVertices (P 2 true) := by
      simpa [(data.hobsP 2 true).2.1] using left_mem
    have star' := OuterMixedOdometerGeometry.star'At950 q cfg C0 T cert h P r Q S u v g x data
        star
    have comp := OuterMixedOdometerGeometry.compAt957 q cfg C0 T cert P x marked translatedObs
        webCompanion
    exact finish (P 0 false) (P 2 true) (r 0 false) (r 2 true)
      C1 C3 cfg.firstPredecessor 2 2 p0mleaf p2pleaf cfg.firstProper
      cfg.firstChild cfg.firstParentThree hp0mleaf hp2pleaf hcent31
      (congrArg Prod.fst hslope31) (congrArg Prod.snd hslope31) adj31
      (data.hextP 0 false) (data.hextP 2 true)
      (data.hcompat _ _ ⟨0, false, Or.inl rfl⟩ ⟨2, true, Or.inl rfl⟩)
      leftMem rightMem star' comp
  · obtain ⟨left_mem, right_mem, star, _coarse, webCompanion, _rowEq⟩ := case23
    have leftMem : x ∈ FootprintVertices (P 1 true) := by
      simpa [(data.hobsP 1 true).2.1] using left_mem
    have rightMem : x ∈ FootprintVertices (P 2 false) := by
      simpa [(data.hobsP 2 false).2.1] using right_mem
    have star' := OuterMixedOdometerGeometry.star'At978 q cfg C0 T cert h P r Q S u v g x data
        star
    have comp := OuterMixedOdometerGeometry.compAt982 q cfg C0 T cert P x marked translatedObs
        webCompanion
    exact finish (P 1 true) (P 2 false) (r 1 true) (r 2 false)
      C2 C3 cfg.secondPredecessor 0 3 p1pleaf p2leaf cfg.secondProper
      cfg.secondChild cfg.secondParentOne hp1pleaf hp2leaf (by simpa using hcent23)
      (by simpa using congrArg Prod.fst hslope23)
      (by simpa using congrArg Prod.snd hslope23) adj23
      (data.hextP 1 true) (data.hextP 2 false)
      (data.hcompat _ _ ⟨1, true, Or.inl rfl⟩ ⟨2, false, Or.inl rfl⟩)
      leftMem rightMem star' comp
  · obtain ⟨left_mem, right_mem, star, _coarse, webCompanion, _rowEq⟩ := case32
    have leftMem : x ∈ FootprintVertices (P 1 false) := by
      simpa [(data.hobsP 1 false).2.1] using right_mem
    have rightMem : x ∈ FootprintVertices (P 2 true) := by
      simpa [(data.hobsP 2 true).2.1] using left_mem
    have star' := OuterMixedOdometerGeometry.star'At1004 q cfg C0 T cert h P r Q S u v g x data
        star
    have comp := OuterMixedOdometerGeometry.compAt1011 q cfg C0 T cert P x marked translatedObs
        webCompanion
    exact finish (P 1 false) (P 2 true) (r 1 false) (r 2 true)
      C2 C3 cfg.secondPredecessor 0 1 p1leaf p2pleaf cfg.secondProper
      cfg.secondChild cfg.secondParentOne hp1leaf hp2pleaf (by simpa using hcent32)
      (by simpa using congrArg Prod.fst hslope32)
      (by simpa using congrArg Prod.snd hslope32) adj32
      (data.hextP 1 false) (data.hextP 2 true)
      (data.hcompat _ _ ⟨1, false, Or.inl rfl⟩ ⟨2, true, Or.inl rfl⟩)
      leftMem rightMem star' comp

end OuterMixedOdometerConclusion

theorem BandOrderedGeneralOuterMixedOdometerRows
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
    (outer :
      (exists
        (left_mem : x ∈ FootprintVertices (cert.P 0 true))
        (right_mem : x ∈ FootprintVertices (cert.P 1 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.P 0 true) \/
            y ∈ FootprintVertices (cert.P 1 false))
        (coarseThird : x ∈ FootprintVertices (cert.P 0 false) <->
          marked = true)
        (webCompanion :
          x ∈ FootprintVertices
            (TileTranslation (cert.P 0 true)
              ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
                (if Even (3 : Nat) then
                  BandVectors.1 (cfg.firstPredecessor 0)
                    (cfg.firstPredecessor 2)
                else
                  BandVectors.1 (cfg.firstPredecessor 2)
                    (cfg.firstPredecessor 0)))) <-> marked = true),
        row = .outer12 left_mem right_mem star coarseThird webCompanion) \/
      (exists
        (left_mem : x ∈ FootprintVertices (cert.P 0 true))
        (right_mem : x ∈ FootprintVertices (cert.P 2 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.P 0 true) \/
            y ∈ FootprintVertices (cert.P 2 false))
        (coarseThird : x ∈ FootprintVertices (cert.P 1 true) <->
          marked = true)
        (webCompanion :
          x ∈ FootprintVertices
            (TileTranslation (cert.P 0 true)
              ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) *
                (if Even (0 : Nat) then
                  BandVectors.1 (cfg.firstPredecessor 0)
                    (cfg.firstPredecessor 3)
                else
                  BandVectors.1 (cfg.firstPredecessor 3)
                    (cfg.firstPredecessor 0)))) <-> marked = true),
        row = .outer13 left_mem right_mem star coarseThird webCompanion) \/
      (exists
        (left_mem : x ∈ FootprintVertices (cert.P 1 true))
        (right_mem : x ∈ FootprintVertices (cert.P 0 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.P 1 true) \/
            y ∈ FootprintVertices (cert.P 0 false))
        (coarseThird : x ∈ FootprintVertices (cert.P 0 true) <->
          marked = true)
        (webCompanion :
          x ∈ FootprintVertices
            (TileTranslation (cert.P 0 false)
              ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
                (if Even (1 : Nat) then
                  BandVectors.1 (cfg.firstPredecessor 0)
                    (cfg.firstPredecessor 2)
                else
                  BandVectors.1 (cfg.firstPredecessor 2)
                    (cfg.firstPredecessor 0)))) <-> marked = true),
        row = .outer21 left_mem right_mem star coarseThird webCompanion) \/
      (exists
        (left_mem : x ∈ FootprintVertices (cert.P 2 true))
        (right_mem : x ∈ FootprintVertices (cert.P 0 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.P 2 true) \/
            y ∈ FootprintVertices (cert.P 0 false))
        (coarseThird : x ∈ FootprintVertices (cert.P 1 false) <->
          marked = true)
        (webCompanion :
          x ∈ FootprintVertices
            (TileTranslation (cert.P 0 false)
              ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
                (if Even (2 : Nat) then
                  BandVectors.1 (cfg.firstPredecessor 0)
                    (cfg.firstPredecessor 3)
                else
                  BandVectors.1 (cfg.firstPredecessor 3)
                    (cfg.firstPredecessor 0)))) <-> marked = true),
        row = .outer31 left_mem right_mem star coarseThird webCompanion) \/
      (exists
        (left_mem : x ∈ FootprintVertices (cert.P 1 true))
        (right_mem : x ∈ FootprintVertices (cert.P 2 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.P 1 true) \/
            y ∈ FootprintVertices (cert.P 2 false))
        (coarseThird : x ∈ FootprintVertices (cert.P 0 true) <->
          marked = true)
        (webCompanion :
          x ∈ FootprintVertices
            (TileTranslation (cert.P 1 true)
              ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
                (if Even (3 : Nat) then
                  BandVectors.1 (cfg.secondPredecessor 0)
                    (cfg.secondPredecessor 1)
                else
                  BandVectors.1 (cfg.secondPredecessor 1)
                    (cfg.secondPredecessor 0)))) <-> marked = true),
        row = .outer23 left_mem right_mem star coarseThird webCompanion) \/
      (exists
        (left_mem : x ∈ FootprintVertices (cert.P 2 true))
        (right_mem : x ∈ FootprintVertices (cert.P 1 false))
        (star : forall y, y = x \/ y = x + 1 \/ y = x - 1 \/
          y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
          y ∈ FootprintVertices (cert.P 2 true) \/
            y ∈ FootprintVertices (cert.P 1 false))
        (coarseThird : x ∈ FootprintVertices (cert.P 0 false) <->
          marked = true)
        (webCompanion :
          x ∈ FootprintVertices
            (TileTranslation (cert.P 1 false)
              ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
                (if Even (1 : Nat) then
                  BandVectors.1 (cfg.secondPredecessor 0)
                    (cfg.secondPredecessor 1)
                else
                  BandVectors.1 (cfg.secondPredecessor 1)
                    (cfg.secondPredecessor 0)))) <-> marked = true),
        row = .outer32 left_mem right_mem star coarseThird webCompanion)) :
    (marked = true -> FourNeighborLaplacian g x = 0) /\
    (marked = false -> FourNeighborLaplacian g x = 1) := by
-- BODY
  classical
  let I : GaussianInt := ⟨0, 1⟩
  have hI2 : (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 := by
    ext <;> norm_num [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hImul : I * I = -1 := by
    rw [← pow_two, hI2]
  let U : GaussianInt := BandVectors.1 (q 2) (q 1)
  let W : GaussianInt := BandVectors.1 (q 3) (q 2)
  let A : GaussianInt := BandVectors.2 (q 2) (q 1)
  let B : GaussianInt := BandVectors.2 (q 3) (q 2)
  let cOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint z -
      (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  let sOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) •
      (((z.re : Int) : Real) - ((z.im : Int) : Real),
        ((z.im : Int) : Real) + ((z.re : Int) : Real))
  have laws := VectorRecursionLaws q cfg.proper.1
  have firstLaws := VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1
  have secondFlip := (VectorRecursionLaws cfg.secondPredecessor
    cfg.secondProper.1).2.2.2.2 cfg.secondProper 0
  have hW := OuterMixedOdometerGeometry.hW q laws
  have hA := OuterMixedOdometerGeometry.hA q laws
  have hrotA := OuterMixedOdometerGeometry.hrotA q cfg
  have hA21 := OuterMixedOdometerGeometry.hA21 q cfg hrotA
  have hV13 := OuterMixedOdometerGeometry.hV13 q cfg firstLaws (OuterMixedOdometerGeometry.hV21 q
      cfg (OuterMixedOdometerGeometry.hrotV q cfg))
  have hA13 := OuterMixedOdometerGeometry.hA13 q cfg firstLaws hA21
  have hflipV := secondFlip.1
  have hflipA := secondFlip.2
  change BandVectors.1 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = I * BandVectors.1
        (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) at hflipV
  change BandVectors.2 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = -I * BandVectors.2
        (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) at hflipA
  rw [cfg.secondChild, cfg.secondParentOne] at hflipV hflipA
  have hpos2 := OuterMixedOdometerGeometry.hpos2 q cfg
  have hpos3 := OuterMixedOdometerGeometry.hpos3 q cfg
  have hpos1 := OuterMixedOdometerGeometry.hpos1 q cfg
  let C1 : BandCircle := ⟨⟨q 1, Or.inl hpos1, q, cfg.proper.1, 1, rfl⟩, hpos1⟩
  let C2 : BandCircle := ⟨⟨q 2, Or.inl hpos2, q, cfg.proper.1, 2, rfl⟩, hpos2⟩
  let C3 : BandCircle := ⟨⟨q 3, Or.inl hpos3, q, cfg.proper.1, 3, rfl⟩, hpos3⟩
  have pPack := OuterMixedOdometerGeometry.pPack q cfg C0 T cert h P r Q S u v g data
  have p0plus := pPack 0 true
  have p1minus := pPack 1 false
  obtain ⟨p0, p0leaf, hp0, hp0leaf, hp0x, hp0y⟩ := p0plus
  obtain ⟨p1, p1leaf, hp1, hp1leaf, hp1x, hp1y⟩ := p1minus
  have hroot01 : p0 = p1 := Option.some.inj (hp0.symm.trans hp1)
  subst p1
  have hdelta0 := OuterMixedOdometerGeometry.hdelta0 q p0 p0leaf hp0x hp0y
  have hdelta1 := OuterMixedOdometerGeometry.hdelta1 q hA p0 p1leaf hp1x hp1y
  have hc0plus : TileCentroid (P 0 true) - TileCentroid T = cOff W := by
    simpa [cOff, Fin.add_def] using data.hPcent 0 true
  have hc1minus := OuterMixedOdometerGeometry.hc1minus q cfg C0 T cert h P r Q S u v g data
  have hcent12 := OuterMixedOdometerGeometry.hcent12 q cfg T P firstLaws hW hc0plus hc1minus
  have hsumA12 := OuterMixedOdometerGeometry.hsumA12 q cfg firstLaws hrotA hA21
  have hslope12 := OuterMixedOdometerGeometry.hslope12 q cfg hA p0 p0leaf p1leaf hdelta0 hdelta1
      hsumA12
  have adj12 := OuterMixedOdometerGeometry.adj12 q cfg C0 T cert h P r Q S u v g data hpos2 hpos1
      p0leaf hp0leaf p1leaf hp1leaf hcent12 hslope12
  obtain ⟨p2, p2leaf, hp2, hp2leaf, hp2x, hp2y⟩ := pPack 2 false
  have hroot02 : p0 = p2 := Option.some.inj (hp0.symm.trans hp2)
  subst p2
  have hdelta2 := OuterMixedOdometerGeometry.hdelta2 q p0 p2leaf hp2x hp2y
  have hc2minus : TileCentroid (P 2 false) - TileCentroid T = -cOff U := by
    simpa [cOff, Fin.add_def, U] using data.hPcent 2 false
  have hflip03pair := firstLaws.2.2.2.2 cfg.firstProper 2
  have hflip03 : BandVectors.1 (cfg.firstPredecessor 0)
      (cfg.firstPredecessor 3) = I * BandVectors.1
        (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) := hflip03pair.1
  have hsumV03 := OuterMixedOdometerGeometry.hsumV03 q cfg (OuterMixedOdometerGeometry.hV30 q cfg
      hImul hV13 (OuterMixedOdometerGeometry.hrot2V q cfg)) hflip03
  have hcent13 := OuterMixedOdometerGeometry.hcent13 q cfg T P hc0plus hc2minus hsumV03
  have hflip03A : BandVectors.2 (cfg.firstPredecessor 0)
      (cfg.firstPredecessor 3) = -I * BandVectors.2
        (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) := hflip03pair.2
  have hsumA03 := OuterMixedOdometerGeometry.hsumA03 q cfg (OuterMixedOdometerGeometry.hA30 q cfg
      hImul hA13 (OuterMixedOdometerGeometry.hrot2A q cfg)) hflip03A
  have hslope13 := OuterMixedOdometerGeometry.hslope13 q cfg p0 p0leaf hdelta0 p2leaf hdelta2
      hsumA03
  have adj13 := OuterMixedOdometerGeometry.adj13 q cfg C0 T cert h P r Q S u v g
          data hpos3 hpos1 p0leaf hp0leaf p2leaf hp2leaf hcent13 hslope13
  obtain ⟨p1p, p1pleaf, hp1p, hp1pleaf, hp1px, hp1py⟩ := pPack 1 true
  have hroot1p : p1p = p0 := Option.some.inj (hp1p.symm.trans hp0)
  subst p1p
  obtain ⟨p0m, p0mleaf, hp0m, hp0mleaf, hp0mx, hp0my⟩ := pPack 0 false
  have hroot0m : p0m = p0 := Option.some.inj (hp0m.symm.trans hp0)
  subst p0m
  have hdelta1p := OuterMixedOdometerGeometry.hdelta1p q p0 p1pleaf hp1px hp1py
  have hdelta0m := OuterMixedOdometerGeometry.hdelta0m q p0 p0mleaf hp0mx hp0my
  have hflip12pair := firstLaws.2.2.2.2 cfg.firstProper 1
  have hc1plus := OuterMixedOdometerGeometry.hc1plus q cfg C0 T cert h P r Q S u v g data
  have hc0minus : TileCentroid (P 0 false) - TileCentroid T = -cOff W := by
    simpa [cOff, Fin.add_def] using data.hPcent 0 false
  have hcent21 := OuterMixedOdometerGeometry.hcent21 q cfg T P hW
      (OuterMixedOdometerGeometry.hsumV12 q cfg (OuterMixedOdometerGeometry.hflip12 q cfg
      hflip12pair)) hc1plus hc0minus
  have hslope21 := OuterMixedOdometerGeometry.hslope21 q cfg hsumA12 p1pleaf p0mleaf
      (OuterMixedOdometerGeometry.hpair21base q hA p0 p1pleaf p0mleaf hdelta1p hdelta0m)
  have adj21 := OuterMixedOdometerGeometry.adj21 q cfg C0 T cert h P r Q S u v g data hpos2 hpos1
      p1pleaf hp1pleaf p0mleaf hp0mleaf hcent21 hslope21
  obtain ⟨p2p, p2pleaf, hp2p, hp2pleaf, hp2px, hp2py⟩ := pPack 2 true
  have hroot2p : p2p = p0 := Option.some.inj (hp2p.symm.trans hp0)
  subst p2p
  have hdelta2p := OuterMixedOdometerGeometry.hdelta2p q p0 p2pleaf hp2px hp2py
  have hc2plus : TileCentroid (P 2 true) - TileCentroid T = cOff U := by
    simpa [cOff, Fin.add_def, U] using data.hPcent 2 true
  have hcent31 := OuterMixedOdometerGeometry.hcent31 q cfg T P hsumV03 hc0minus hc2plus
  have hslope31 := OuterMixedOdometerGeometry.hslope31 q cfg hsumA03 p0mleaf p2pleaf
      (OuterMixedOdometerGeometry.hpair31base q p0 p0mleaf hdelta0m p2pleaf hdelta2p)
  have adj31 := OuterMixedOdometerGeometry.adj31 q cfg C0 T cert h P r Q S u v g data hpos3 hpos1
      p0mleaf hp0mleaf p2pleaf hp2pleaf hcent31 hslope31
  have hsumVsecond := OuterMixedOdometerGeometry.hsumVsecond q cfg hflipV
  have hsumAsecond := OuterMixedOdometerGeometry.hsumAsecond q cfg hflipA
  have hcent23 := OuterMixedOdometerGeometry.hcent23 q cfg T P hW hc2minus hc1plus hsumVsecond
  have hslope23 := OuterMixedOdometerGeometry.hslope23 q cfg p2leaf p1pleaf hsumAsecond
                (OuterMixedOdometerGeometry.hpair23base q hA p0 p2leaf hdelta2 p1pleaf hdelta1p)
  have hcent32 := OuterMixedOdometerGeometry.hcent32 q cfg T P hW hc1minus hc2plus hsumVsecond
  have hslope32 := OuterMixedOdometerGeometry.hslope32 q cfg p1leaf p2pleaf hsumAsecond
                (OuterMixedOdometerGeometry.hpair32base q hA p0 p1leaf hdelta1 p2pleaf hdelta2p)
  have adj23 := OuterMixedOdometerGeometry.adj23 q cfg C0 T cert h P r Q S u v g
          data hpos2 hpos3 p2leaf hp2leaf p1pleaf hp1pleaf hcent23 hslope23
  have adj32 := OuterMixedOdometerGeometry.adj32 q cfg C0 T cert h P r Q S u v g
          data hpos2 hpos3 p1leaf hp1leaf p2pleaf hp2pleaf hcent32 hslope32
  have translatedObs := OuterMixedOdometerGeometry.translatedObs q cfg C0 T cert h P r Q S u v g
      data
  have finish := OuterMixedOdometerGeometry.finish g x marked
  have outerMixedConclusion := OuterMixedOdometerConclusion.outerMixedConclusion q cfg C0 T cert
      h P r Q S u v g x marked data row outer hpos2 hpos3 hpos1 p0leaf hp0leaf p1leaf hp1leaf
      hcent12 hslope12 adj12 p2leaf hp2leaf hcent13 hslope13 adj13 p1pleaf hp1pleaf p0mleaf
      hp0mleaf hcent21 hslope21 adj21 p2pleaf hp2pleaf hcent31 hslope31 adj31 hcent23 hslope23
      hcent32 hslope32 adj23 adj32 translatedObs finish
  exact outerMixedConclusion


end ApollonianSuperharmonic

end
