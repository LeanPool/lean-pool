/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4250T1SlopeOffset
public import LeanPool.ApollonianSuperharmonic.BandOriginalOccurrenceIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.RightSubtileOdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent

-- [TABLET NODE: P4250T1OrdinaryCompatibility]

/-!
# P4250T1OrdinaryCompatibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OrdinaryCompatibilityGeometry

private theorem hImul :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        I * I = -1 ) := by
  classical
  intro I
  dsimp [I]
  decide

private theorem hI3 :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 2 = -1) → (I ^ 3 = -I) ) := by
  classical
  intro I hI2
  rw [pow_succ, hI2]
  simp

private theorem hX :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        let X := BandVectors.1 (q 1) (q 3)
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
            GaussianInt) * BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))))) → (X = -U - W) ) := by
  classical
  intro q U W X laws
  dsimp [X, U, W]
  linear_combination laws.1

private theorem hY :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
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
            GaussianInt) * BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))))) → (Y = -A - B) ) := by
  classical
  intro q A B Y laws
  dsimp [Y, A, B]
  linear_combination laws.2.1

private theorem hpos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (i : Fin 3),
            0 < (q i.succ).1) ) := by
  classical
  intro q cfg i
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 i
  have hne := cfg.noLine i.succ
  have hn' : 0 ≤ (q i.succ).1 := by simpa using hn
  omega

private theorem occCent :
    (by
      classical
      exact
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (P : ProtoTile), ∀ (Z : ProtoTile), ∀ (i : Fin 3), ∀
            (e : Bool), (BandSubtileOccurrence r P i e Z) → (TileCentroid Z - TileCentroid P =
            (if e then (1 : Real) else -1) • cOff (BandVectors.1 (r ((i + 2).succ)) (r ((i +
            1).succ)))) ) := by
  classical
  intro cOff r P Z i e ho
  change BandPrototile (r i.succ) Z ∧ _ ∧ _ at ho
  rcases ho with ⟨_, _, hc⟩
  exact hc

private theorem slope :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real ×
            Real), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), PartialOdometerSlope (h i s) = some (s0 +
            (if s = true then (1 : ℝ) else (-1 : ℝ)) • P4250T1SlopeOffset (BandVectors.2 (q (i
            + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (i : Fin 3), ∀ (e : Bool), PartialOdometerSlope (h i e) = some (s0 + (if e then (1 :
            Real) else -1) • sOff (BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))))) ) := by
  classical
  intro q h s0 hp sOff i e
  simpa [sOff] using hp i e

private theorem cadd :
    (by
      classical
      exact
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), cOff (a + b) = cOff a + cOff b ) := by
  classical
  intro cOff a b
  dsimp [cOff, GaussianRealPoint]
  ext <;> simp [] <;> ring

private theorem cneg :
    (by
      classical
      exact
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        ∀ (a : GaussianInt), cOff (-a) = -cOff a ) := by
  classical
  intro cOff a
  dsimp [cOff, GaussianRealPoint]
  ext <;> simp [] <;> ring

private theorem sY :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        (Y = -A - B) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), sOff (a + b) = sOff a + sOff
            b) → ((∀ (a : GaussianInt), sOff (-a) = -sOff a) → (sOff Y = -sOff A - sOff B))) ) := by
  classical
  intro q A B Y sOff hY sadd sneg
  rw [hY]
  have hneg : -A - B = -(A + B) := by abel
  rw [hneg, sneg, sadd]
  ext <;> simp <;> ring

private theorem gaussianPointNeg :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianRealPoint (-z) = -GaussianRealPoint z ) := by
  classical
  intro z
  ext <;> simp [GaussianRealPoint]

private theorem hV20 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let U := BandVectors.1 (q 2) (q 1)
        BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = U ) := by
  classical
  intro q cfg U
  simp [U, cfg.firstParentTwo, cfg.firstChild]

private theorem hV21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = U) → (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) ) := by
  classical
  intro q cfg I U W hV20
  have hr := (VectorRecursionLaws _
    (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.1
  have hrot : BandVectors.1 (cfg.firstPredecessor 2)
      (cfg.firstPredecessor 0) =
    BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) -
      I * W := by
    simpa [I, W, cfg.firstParentThree, cfg.firstParentTwo,
      cfg.firstChild] using hr
  rw [hV20] at hrot
  dsimp [U, I, W] at hrot ⊢
  linear_combination -hrot

private theorem hflip120 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = U) → ((BandVectors.1
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (Fin.succ (1 : Fin (3
            : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (cfg.firstPredecessor
            (Fin.succ (1 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) ∧
            BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (Fin.succ (1 : Fin (3 : ℕ)))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (cfg.firstPredecessor (Fin.succ (1 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ)))) → (BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = I * U))
            ) := by
  classical
  intro q cfg I U hV20 hflip12
  have hf := hflip12.1
  change BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) =
    I * BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) at hf
  rw [hV20] at hf
  simpa [I, U] using hf

private theorem hsumV12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = U) → ((BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = I * U) → (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = (1 + I) * U)) ) := by
  classical
  intro q cfg I U hV20 hflip120
  rw [hV20, hflip120]
  ring

private theorem hV30 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        (I * I = -1) → ((BandVectors.1 (cfg.firstPredecessor (3 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) + BandVectors.1 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) + BandVectors.1
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) =
            (0 : GaussianInt) ∧ BandVectors.2 (cfg.firstPredecessor (3 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) + BandVectors.2 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) + BandVectors.2
            (cfg.firstPredecessor (2 : Fin (4 : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) =
            (0 : GaussianInt) ∧ BandVectors.1 (cfg.firstPredecessor (1 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) = BandVectors.1 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (cfg.firstPredecessor (2 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ BandVectors.2 (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (0 : Fin (4 : ℕ))) = BandVectors.2
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))) +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor (2 : Fin (4
            : ℕ))) (cfg.firstPredecessor (1 : Fin (4 : ℕ))) ∧ (ProperBandQuadruple
            cfg.firstPredecessor → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (cfg.firstPredecessor (0 :
            Fin (4 : ℕ))) (cfg.firstPredecessor j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (cfg.firstPredecessor j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ)))
            ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor
            j.succ) (cfg.firstPredecessor (0 : Fin (4 : ℕ))))) → ((BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = U + I * W) → (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = I * (U + W)))) ) := by
  classical
  intro q cfg I U W hImul firstLaws hV21
  have hr : BandVectors.1 (cfg.firstPredecessor 3)
      (cfg.firstPredecessor 0) = BandVectors.1 (cfg.firstPredecessor 3)
      (cfg.firstPredecessor 2) - I * BandVectors.1
        (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) := by
    simpa [I] using (VectorRecursionLaws _
      (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.firstProper.1))).2.2.1
  have hv13 : BandVectors.1 (cfg.firstPredecessor 1)
      (cfg.firstPredecessor 3) = -U - (1 + I) * W := by
    have hsum : W + BandVectors.1 (cfg.firstPredecessor 1)
        (cfg.firstPredecessor 3) +
        BandVectors.1 (cfg.firstPredecessor 2)
          (cfg.firstPredecessor 1) = 0 := by
      simpa [W, cfg.firstParentThree, cfg.firstParentTwo] using firstLaws.1
    rw [hV21] at hsum
    dsimp [U, W, I] at hsum ⊢
    linear_combination hsum
  rw [hr, hv13, cfg.firstParentThree, cfg.firstParentTwo]
  dsimp [U, W, I]
  linear_combination hImul * W

private theorem hsumV03 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        (I * I = -1) → ((BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = I * (U
            + W)) → ((BandVectors.1 (cfg.firstPredecessor (0 : Fin (4 : ℕ)))
            (cfg.firstPredecessor (Fin.succ (2 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (cfg.firstPredecessor (Fin.succ (2 : Fin (3 : ℕ))))
            (cfg.firstPredecessor (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (cfg.firstPredecessor (0 :
            Fin (4 : ℕ))) (cfg.firstPredecessor (Fin.succ (2 : Fin (3 : ℕ)))) = -(⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.2 (cfg.firstPredecessor (Fin.succ (2 : Fin (3 :
            ℕ)))) (cfg.firstPredecessor (0 : Fin (4 : ℕ)))) → (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 + I) * (I * (U + W))))) ) := by
  classical
  intro q cfg I U W hImul hV30 hflip03
  have hf : BandVectors.1 (cfg.firstPredecessor 0)
      (cfg.firstPredecessor 3) = I * BandVectors.1
        (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) := by
    simpa [I] using hflip03.1
  calc
    _ = I * (U + W) + I * (I * (U + W)) := by rw [hV30, hf, hV30]
    _ = (1 + I) * (I * (U + W)) := by
      calc
        _ = I * (U + W) + (I * I) * (U + W) := by rw [← mul_assoc]
        _ = I * (U + W) + (-1) * (U + W) := by rw [hImul]
        _ = (-1 + I) * (U + W) := by ring
        _ = (1 + I) * (I * (U + W)) := by
          have hp : (1 + I) * I = -1 + I := by
            calc
              _ = I + I * I := by ring
              _ = I + (-1) := by rw [hImul]
              _ = -1 + I := by ring
          rw [← mul_assoc, hp]

private theorem hsumVsecond :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let W := BandVectors.1 (q 3) (q 2)
        (BandVectors.1 (cfg.secondPredecessor (0 : Fin (4 : ℕ))) (cfg.secondPredecessor (Fin.succ
            (0 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (cfg.secondPredecessor (Fin.succ (0 : Fin (3 : ℕ)))) (cfg.secondPredecessor (0 : Fin
            (4 : ℕ))) ∧ BandVectors.2 (cfg.secondPredecessor (0 : Fin (4 : ℕ)))
            (cfg.secondPredecessor (Fin.succ (0 : Fin (3 : ℕ)))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (cfg.secondPredecessor (Fin.succ (0 : Fin (3 : ℕ))))
            (cfg.secondPredecessor (0 : Fin (4 : ℕ)))) → (BandVectors.1 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 + I) * W) ) := by
  classical
  intro q cfg I W hflipSecond
  have hf : BandVectors.1 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = I * BandVectors.1
        (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) := by
    simpa [I] using hflipSecond.1
  calc
    _ = BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
        I * BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) := by rw [hf]
    _ = (1 + I) * W := by rw [cfg.secondVectorOne]; ring

private theorem hsumA12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        (BandVectors.1 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (Fin.succ
            (1 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (cfg.firstPredecessor (Fin.succ (1 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ))) ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (Fin.succ (1 : Fin (3 : ℕ)))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (cfg.firstPredecessor (Fin.succ (1 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ)))) → (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) +
            BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = (1 - I) * A) ) := by
  classical
  intro q cfg I A hflip12
  let B := BandVectors.2 (q 3) (q 2)
  have hf := hflip12.2
  change BandVectors.2 (cfg.firstPredecessor 0)
    (cfg.firstPredecessor 2) = -I * BandVectors.2
      (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) at hf
  have hrotA : BandVectors.2 (cfg.firstPredecessor 2)
      (cfg.firstPredecessor 0) = BandVectors.2 (cfg.firstPredecessor 2)
        (cfg.firstPredecessor 1) + I * B := by
    simpa [I, B, cfg.firstParentThree, cfg.firstParentTwo,
      cfg.firstChild] using
      (VectorRecursionLaws _
        (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.2.1
  have hA21 : BandVectors.2 (cfg.firstPredecessor 2)
      (cfg.firstPredecessor 1) = A - I * B := by
    have hbase : BandVectors.2 (cfg.firstPredecessor 2)
        (cfg.firstPredecessor 0) = A := by
      dsimp [A]
      rw [← cfg.firstParentTwo, ← cfg.firstChild]
    have heq : BandVectors.2 (cfg.firstPredecessor 2)
        (cfg.firstPredecessor 1) + I * B = A := by
      calc
        _ = BandVectors.2 (cfg.firstPredecessor 2)
              (cfg.firstPredecessor 0) := hrotA.symm
        _ = A := hbase
    linear_combination heq
  have hbase : BandVectors.2 (cfg.firstPredecessor 2)
      (cfg.firstPredecessor 0) = A := by
    rw [hrotA, hA21]
    dsimp [A, B, I]
    ring
  rw [hbase] at hf ⊢
  linear_combination hf

private theorem hsumAsecond :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B := BandVectors.2 (q 3) (q 2)
        (BandVectors.1 (cfg.secondPredecessor (0 : Fin (4 : ℕ))) (cfg.secondPredecessor (Fin.succ
            (0 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (cfg.secondPredecessor (Fin.succ (0 : Fin (3 : ℕ)))) (cfg.secondPredecessor (0 : Fin
            (4 : ℕ))) ∧ BandVectors.2 (cfg.secondPredecessor (0 : Fin (4 : ℕ)))
            (cfg.secondPredecessor (Fin.succ (0 : Fin (3 : ℕ)))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (cfg.secondPredecessor (Fin.succ (0 : Fin (3 : ℕ))))
            (cfg.secondPredecessor (0 : Fin (4 : ℕ)))) → (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 - I) * B) ) := by
  classical
  intro q cfg I B hflipSecond
  have hbase : BandVectors.2 (cfg.secondPredecessor 1)
      (cfg.secondPredecessor 0) = B := by
    simp [B, cfg.secondParentOne, cfg.secondChild]
  have hf : BandVectors.2 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = -I * B := by
    have hf := hflipSecond.2
    change BandVectors.2 (cfg.secondPredecessor 0)
      (cfg.secondPredecessor 1) = -I * BandVectors.2
        (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) at hf
    rw [hbase] at hf
    exact hf
  rw [hbase, hf]
  ring

private theorem hrot2A :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) + I * BandVectors.2
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) ) := by
  classical
  intro q cfg I
  simpa [I] using (VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.firstProper.1))).2.2.2.1

private theorem hrotAglobal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let B := BandVectors.2 (q 3) (q 2)
        BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) + I * B ) := by
  classical
  intro q cfg I B
  simpa [I, B, cfg.firstParentThree, cfg.firstParentTwo,
    cfg.firstChild] using (VectorRecursionLaws _
      (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.2.1

private theorem hA21global :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) + I * B) → (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = A - I * B) ) := by
  classical
  intro q cfg I A B hrotAglobal
  have hbase : BandVectors.2 (cfg.firstPredecessor 2)
      (cfg.firstPredecessor 0) = A := by
    dsimp [A]
    rw [← cfg.firstParentTwo, ← cfg.firstChild]
  have heq : BandVectors.2 (cfg.firstPredecessor 2)
      (cfg.firstPredecessor 1) + I * B = A := by
    calc
      _ = BandVectors.2 (cfg.firstPredecessor 2)
          (cfg.firstPredecessor 0) := hrotAglobal.symm
      _ = A := hbase
  linear_combination heq

private theorem hA13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
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
  intro q cfg I A B firstLaws hA21global
  have hsum : B + BandVectors.2 (cfg.firstPredecessor 1)
      (cfg.firstPredecessor 3) +
      BandVectors.2 (cfg.firstPredecessor 2)
        (cfg.firstPredecessor 1) = 0 := by
    simpa [B, cfg.firstParentThree, cfg.firstParentTwo] using firstLaws.2.1
  rw [hA21global] at hsum
  dsimp [A, B, I] at hsum ⊢
  linear_combination hsum

private theorem hA30 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        (I * I = -1) → ((BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) =
            BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) + I * BandVectors.2
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)) → ((BandVectors.2
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -A - (1 - I) * B) →
            (BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = -I * (A + B)))) )
            := by
  classical
  intro q cfg I A B hImul hrot2A hA13
  rw [hrot2A, hA13, cfg.firstParentThree, cfg.firstParentTwo]
  dsimp [A, B, I]
  linear_combination hImul * B

private theorem hflip03A :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        (BandVectors.1 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor (Fin.succ
            (2 : Fin (3 : ℕ)))) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1
            (cfg.firstPredecessor (Fin.succ (2 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ))) ∧ BandVectors.2 (cfg.firstPredecessor (0 : Fin (4 : ℕ))) (cfg.firstPredecessor
            (Fin.succ (2 : Fin (3 : ℕ)))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2
            (cfg.firstPredecessor (Fin.succ (2 : Fin (3 : ℕ)))) (cfg.firstPredecessor (0 : Fin (4
            : ℕ)))) → (BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = -I *
            BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)) ) := by
  classical
  intro q cfg I hflip03
  simpa [I] using hflip03.2

private theorem hsumA03 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        (I * I = -1) → ((BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) = -I *
            (A + B)) → ((BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = -I *
            BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0)) → (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 - I) * (-I * (A + B))))) ) := by
  classical
  intro q cfg I A B hImul hA30 hflip03A
  rw [hA30, hflip03A]
  rw [hA30]
  calc
    _ = -I * (A + B) + ((-I) * (-I)) * (A + B) := by rw [← mul_assoc]
    _ = -I * (A + B) + (-1) * (A + B) := by
      have hn : (-I : GaussianInt) * (-I) = -1 := by
        rw [neg_mul_neg, hImul]
      rw [hn]
    _ = (-1 - I) * (A + B) := by ring
    _ = (1 - I) * (-I * (A + B)) := by
      have hp : (1 - I) * (-I) = -1 - I := by
        calc
          _ = -(I - I * I) := by ring
          _ = -(I - (-1)) := by rw [hImul]
          _ = -1 - I := by ring
      rw [← mul_assoc, hp]

private theorem hC12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        let X := BandVectors.1 (q 1) (q 3)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (X = -U - W) → ((TileCentroid (cert.P 0 true) - TileCentroid T = cOff W) → ((TileCentroid
            (cert.P 1 false) - TileCentroid T = -cOff X) → ((BandVectors.1 (cfg.firstPredecessor
            2) (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 2) = (1 + I) * U) → (TileCentroid (cert.P 1 false) -
            TileCentroid (cert.P 0 true) = (1 / 2 : Real) • GaussianRealPoint (I ^ 3 *
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2))))))) ) := by
  classical
  intro q cfg C T cert I U W X cOff hX hc0p hc1m hsumV12
  have ha : TileCentroid (cert.P 1 false) - TileCentroid (cert.P 0 true) =
      -cOff X - cOff W := by
    calc
      _ = (TileCentroid (cert.P 1 false) - TileCentroid T) -
          (TileCentroid (cert.P 0 true) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc1m, hc0p]
  rw [ha, hX, hsumV12]
  dsimp [cOff, GaussianRealPoint, I, U, W]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hC21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        let X := BandVectors.1 (q 1) (q 3)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (X = -U - W) → ((TileCentroid (cert.P 0 false) - TileCentroid T = -cOff W) →
            ((TileCentroid (cert.P 1 true) - TileCentroid T = cOff X) → ((BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = (1 + I) * U) → (TileCentroid
            (cert.P 1 true) - TileCentroid (cert.P 0 false) = (1 / 2 : Real) • GaussianRealPoint
            (I ^ 1 * (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) +
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2))))))) ) := by
  classical
  intro q cfg C T cert I U W X cOff hX hc0m hc1p hsumV12
  have ha : TileCentroid (cert.P 1 true) - TileCentroid (cert.P 0 false) =
      cOff X + cOff W := by
    calc
      _ = (TileCentroid (cert.P 1 true) - TileCentroid T) -
          (TileCentroid (cert.P 0 false) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc1p, hc0m]; simp
  rw [ha, hX, hsumV12]
  dsimp [cOff, GaussianRealPoint, I, U, W]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hC13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (cert.P 0 true) - TileCentroid T = cOff W) → ((TileCentroid (cert.P 2
            false) - TileCentroid T = -cOff U) → ((BandVectors.1 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 3) = (1 + I) * (I * (U + W))) → (TileCentroid (cert.P 2 false)
            - TileCentroid (cert.P 0 true) = (1 / 2 : Real) • GaussianRealPoint (I ^ 0 *
            (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))))) ) := by
  classical
  intro q cfg C T cert I U W cOff hc0p hc2m hsumV03
  have ha : TileCentroid (cert.P 2 false) - TileCentroid (cert.P 0 true) =
      -cOff U - cOff W := by
    calc
      _ = (TileCentroid (cert.P 2 false) - TileCentroid T) -
          (TileCentroid (cert.P 0 true) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc2m, hc0p]
  rw [ha, hsumV03]
  dsimp [cOff, GaussianRealPoint, I, U, W]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hC31 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (TileCentroid (cert.P 0 false) - TileCentroid T = -cOff W) → ((TileCentroid (cert.P 2
            true) - TileCentroid T = cOff U) → ((BandVectors.1 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 0) + BandVectors.1 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 3) = (1 + I) * (I * (U + W))) → (TileCentroid (cert.P 2 true) -
            TileCentroid (cert.P 0 false) = (1 / 2 : Real) • GaussianRealPoint (I ^ 2 *
            (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))))) ) := by
  classical
  intro q cfg C T cert I U W cOff hc0m hc2p hsumV03
  have ha : TileCentroid (cert.P 2 true) - TileCentroid (cert.P 0 false) =
      cOff U + cOff W := by
    calc
      _ = (TileCentroid (cert.P 2 true) - TileCentroid T) -
          (TileCentroid (cert.P 0 false) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc2p, hc0m]; simp
  rw [ha, hsumV03]
  dsimp [cOff, GaussianRealPoint, I, U, W]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hC23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        let X := BandVectors.1 (q 1) (q 3)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (X = -U - W) → ((TileCentroid (cert.P 1 true) - TileCentroid T = cOff X) → ((TileCentroid
            (cert.P 2 false) - TileCentroid T = -cOff U) → ((BandVectors.1 (cfg.secondPredecessor
            1) (cfg.secondPredecessor 0) + BandVectors.1 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 + I) * W) → (TileCentroid (cert.P 2 false) -
            TileCentroid (cert.P 1 true) = (1 / 2 : Real) • GaussianRealPoint (I ^ 3 *
            (BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))))) ) := by
  classical
  intro q cfg C T cert I U W X cOff hX hc1p hc2m hsumVsecond
  have ha : TileCentroid (cert.P 2 false) - TileCentroid (cert.P 1 true) =
      -cOff U - cOff X := by
    calc
      _ = (TileCentroid (cert.P 2 false) - TileCentroid T) -
          (TileCentroid (cert.P 1 true) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc2m, hc1p]
  rw [ha, hX, hsumVsecond]
  dsimp [cOff, GaussianRealPoint, I, U, W]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem hC32 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let I : GaussianInt := ⟨0, 1⟩
        let U := BandVectors.1 (q 2) (q 1)
        let W := BandVectors.1 (q 3) (q 2)
        let X := BandVectors.1 (q 1) (q 3)
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (X = -U - W) → ((TileCentroid (cert.P 1 false) - TileCentroid T = -cOff X) →
            ((TileCentroid (cert.P 2 true) - TileCentroid T = cOff U) → ((BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = (1 + I) * W) → (TileCentroid
            (cert.P 2 true) - TileCentroid (cert.P 1 false) = (1 / 2 : Real) • GaussianRealPoint
            (I ^ 1 * (BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))))))) ) := by
  classical
  intro q cfg C T cert I U W X cOff hX hc1m hc2p hsumVsecond
  have ha : TileCentroid (cert.P 2 true) - TileCentroid (cert.P 1 false) =
      cOff U + cOff X := by
    calc
      _ = (TileCentroid (cert.P 2 true) - TileCentroid T) -
          (TileCentroid (cert.P 1 false) - TileCentroid T) := by
            ext <;> dsimp <;> ring
      _ = _ := by rw [hc2p, hc1m]; simp
  rw [ha, hX, hsumVsecond]
  dsimp [cOff, GaussianRealPoint, I, U, W]
  norm_num [I, GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def, pow_succ]; ring; trivial

private theorem slopeCoord :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (a : GaussianInt), sOff a = (1 / 2 : Real) • GaussianRealPoint ((1 + I) * a) ) := by
  classical
  intro I sOff a
  dsimp [sOff, P4250T1SlopeOffset, GaussianRealPoint, I]
  norm_num [GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]; ring; trivial

private theorem hnegI3 :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        (I ^ 3 = -I) → ((-I : GaussianInt) ^ 3 = I) ) := by
  classical
  intro I hI3
  rw [neg_pow, hI3]
  norm_num

private theorem hS12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        (I * I = -1) → ((sOff Y = -sOff A - sOff B) → ((BandVectors.2 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 0) + BandVectors.2 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 2) = (1 - I) * A) → ((∀ (a : GaussianInt), sOff a = (1 / 2 :
            Real) • GaussianRealPoint ((1 + I) * a)) → (((-I : GaussianInt) ^ 3 = I) → ((s0 -
            sOff Y) - (s0 + sOff B) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 3 *
            (BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))))))) ) := by
  classical
  intro q cfg s0 I A B Y sOff hImul sY hsumA12 slopeCoord hnegI3
  have hd : (s0 - sOff Y) - (s0 + sOff B) = sOff A := by
    rw [sY]
    ext <;> simp <;> ring
  rw [hd, hsumA12, slopeCoord]
  have hf : (-I) ^ 3 * ((1 - I) * A) = (1 + I) * A := by
    rw [hnegI3]
    rw [← mul_assoc, show I * (1 - I) = 1 + I by rw [mul_sub, hImul]; ring]
  rw [hf]

private theorem hS21 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        (I * I = -1) → ((sOff Y = -sOff A - sOff B) → ((∀ (z : GaussianInt), GaussianRealPoint
            (-z) = -GaussianRealPoint z) → ((BandVectors.2 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 0) + BandVectors.2 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 2) = (1 - I) * A) → ((∀ (a : GaussianInt), sOff a = (1 / 2 :
            Real) • GaussianRealPoint ((1 + I) * a)) → ((s0 + sOff Y) - (s0 - sOff B) = (1 / 2 :
            Real) • GaussianRealPoint ((-I) ^ 1 * (BandVectors.2 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 0) + BandVectors.2 (cfg.firstPredecessor 0)
            (cfg.firstPredecessor 2)))))))) ) := by
  classical
  intro q cfg s0 I A B Y sOff hImul sY gaussianPointNeg hsumA12 slopeCoord
  have hd : (s0 + sOff Y) - (s0 - sOff B) = -sOff A := by
    rw [sY]
    ext <;> simp
  rw [hd, hsumA12, slopeCoord]
  have hf : (-I : GaussianInt) ^ 1 * ((1 - I) * A) = -((1 + I) * A) := by
    simp only [pow_one, neg_mul]
    rw [← mul_assoc, show I * (1 - I) = 1 + I by rw [mul_sub, hImul]; ring]
  rw [hf]
  rw [gaussianPointNeg]
  simp only [smul_neg]

private theorem hS13 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), sOff (a + b) = sOff a + sOff b) →
            ((BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 - I) * (-I * (A + B))) → ((s0
            - sOff A) - (s0 + sOff B) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 0 *
            (BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3))))) ) := by
  classical
  intro q cfg s0 I A B sOff sadd hsumA03
  have hd : (s0 - sOff A) - (s0 + sOff B) = -sOff (A + B) := by
    rw [sadd]
    ext <;> simp <;> ring
  rw [hd, hsumA03]
  dsimp [sOff, P4250T1SlopeOffset, GaussianRealPoint, I]
  norm_num [GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]; ring; trivial

private theorem hS31 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        (I ^ 2 = -1) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), sOff (a + b) = sOff a + sOff
            b) → ((BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
            BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (1 - I) * (-I * (A
            + B))) → ((s0 + sOff A) - (s0 - sOff B) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^
            2 * (BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))))) ) := by
  classical
  intro q cfg s0 I A B sOff hI2 sadd hsumA03
  have hd : (s0 + sOff A) - (s0 - sOff B) = sOff (A + B) := by
    rw [sadd]
    ext <;> simp
  rw [hd, hsumA03]
  rw [show (-I : GaussianInt) ^ 2 = -1 by rw [neg_pow, hI2]; norm_num]
  dsimp [sOff, P4250T1SlopeOffset, GaussianRealPoint, I]
  norm_num [GaussianRealPoint, Prod.smul_mk, Prod.add_def,
    Prod.sub_def]; ring; trivial

private theorem hS23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        (I * I = -1) → ((sOff Y = -sOff A - sOff B) → ((BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 - I) * B) → ((∀ (a : GaussianInt), sOff a = (1 / 2 :
            Real) • GaussianRealPoint ((1 + I) * a)) → (((-I : GaussianInt) ^ 3 = I) → ((s0 -
            sOff A) - (s0 + sOff Y) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 3 *
            (BandVectors.2 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))))))) ) := by
  classical
  intro q cfg s0 I A B Y sOff hImul sY hsumAsecond slopeCoord hnegI3
  have hd : (s0 - sOff A) - (s0 + sOff Y) = sOff B := by
    rw [sY]
    ext <;> simp <;> ring
  rw [hd, hsumAsecond, slopeCoord]
  have hf : (-I) ^ 3 * ((1 - I) * B) = (1 + I) * B := by
    rw [hnegI3]
    rw [← mul_assoc, show I * (1 - I) = 1 + I by rw [mul_sub, hImul]; ring]
  rw [hf]

private theorem hS32 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s0 :
            Real × Real),
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        (I * I = -1) → ((sOff Y = -sOff A - sOff B) → ((∀ (z : GaussianInt), GaussianRealPoint
            (-z) = -GaussianRealPoint z) → ((BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1) = (1 - I) * B) → ((∀ (a : GaussianInt), sOff a = (1 / 2 :
            Real) • GaussianRealPoint ((1 + I) * a)) → ((s0 + sOff A) - (s0 - sOff Y) = (1 / 2 :
            Real) • GaussianRealPoint ((-I) ^ 1 * (BandVectors.2 (cfg.secondPredecessor 1)
            (cfg.secondPredecessor 0) + BandVectors.2 (cfg.secondPredecessor 0)
            (cfg.secondPredecessor 1)))))))) ) := by
  classical
  intro q cfg s0 I A B Y sOff hImul sY gaussianPointNeg hsumAsecond slopeCoord
  have hd : (s0 + sOff A) - (s0 - sOff Y) = -sOff B := by
    rw [sY]
    ext <;> simp <;> ring
  rw [hd, hsumAsecond, slopeCoord]
  have hf : (-I : GaussianInt) ^ 1 * ((1 - I) * B) = -((1 + I) * B) := by
    simp only [pow_one, neg_mul]
    rw [← mul_assoc, show I * (1 - I) = 1 + I by rw [mul_sub, hImul]; ring]
  rw [hf]
  rw [gaussianPointNeg]
  simp only [smul_neg]

private theorem adjAD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (hpos : ∀ (i : Fin 3), 0 < (q i.succ).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl (hpos 0), q, cfg.proper.1, 1, rfl⟩, hpos 0⟩
        let C2 : BandCircle := ⟨⟨q 2, Or.inl (hpos 1), q, cfg.proper.1, 2, rfl⟩, hpos 1⟩
        (PartialOdometerSlope (h 0 true) = some (s0 + sOff B)) → ((PartialOdometerSlope (h 1
            false) = some (s0 - sOff Y)) → ((TileCentroid (cert.P 1 false) - TileCentroid (cert.P
            0 true) = (1 / 2 : Real) • GaussianRealPoint (I ^ 3 * (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → (((s0 - sOff Y) - (s0 + sOff
            B) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 3 * (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → (SubtileLatticeAdjacent C1 C2
            (cert.P 0 true) (cert.P 1 false) (h 0 true) (h 1 false)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho I B Y sOff hpos C1 C2 hs0p hs1m hC12 hS12
  refine ⟨?_, ?_, ⟨s0 + sOff B, s0 - sOff Y, ?_, ?_, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using ho 0 true
  · simpa [C2, cfg.firstParentTwo] using ho 1 false
  · exact hs0p
  · exact hs1m
  refine ⟨cfg.firstPredecessor, 1, 3, cfg.firstProper, ?_, ?_, hC12, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C2] using cfg.firstParentTwo
  · exact congrArg Prod.fst hS12
  · exact congrArg Prod.snd hS12

private theorem adjBC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let B := BandVectors.2 (q 3) (q 2)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (hpos : ∀ (i : Fin 3), 0 < (q i.succ).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl (hpos 0), q, cfg.proper.1, 1, rfl⟩, hpos 0⟩
        let C2 : BandCircle := ⟨⟨q 2, Or.inl (hpos 1), q, cfg.proper.1, 2, rfl⟩, hpos 1⟩
        (PartialOdometerSlope (h 0 false) = some (s0 - sOff B)) → ((PartialOdometerSlope (h 1
            true) = some (s0 + sOff Y)) → ((TileCentroid (cert.P 1 true) - TileCentroid (cert.P 0
            false) = (1 / 2 : Real) • GaussianRealPoint (I ^ 1 * (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → (((s0 + sOff Y) - (s0 - sOff
            B) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 1 * (BandVectors.2
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) → (SubtileLatticeAdjacent C1 C2
            (cert.P 0 false) (cert.P 1 true) (h 0 false) (h 1 true)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho I B Y sOff hpos C1 C2 hs0m hs1p hC21 hS21
  refine ⟨?_, ?_, ⟨s0 - sOff B, s0 + sOff Y, ?_, ?_, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using ho 0 false
  · simpa [C2, cfg.firstParentTwo] using ho 1 true
  · exact hs0m
  · exact hs1p
  refine ⟨cfg.firstPredecessor, 1, 1, cfg.firstProper, ?_, ?_, hC21, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C2] using cfg.firstParentTwo
  · exact congrArg Prod.fst hS21
  · exact congrArg Prod.snd hS21

private theorem adjAF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (hpos : ∀ (i : Fin 3), 0 < (q i.succ).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl (hpos 0), q, cfg.proper.1, 1, rfl⟩, hpos 0⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl (hpos 2), q, cfg.proper.1, 3, rfl⟩, hpos 2⟩
        (PartialOdometerSlope (h 0 true) = some (s0 + sOff B)) → ((PartialOdometerSlope (h 2
            false) = some (s0 - sOff A)) → ((TileCentroid (cert.P 2 false) - TileCentroid (cert.P
            0 true) = (1 / 2 : Real) • GaussianRealPoint (I ^ 0 * (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) → (((s0 - sOff A) - (s0 + sOff
            B) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 0 * (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) → (SubtileLatticeAdjacent C1 C3
            (cert.P 0 true) (cert.P 2 false) (h 0 true) (h 2 false)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho I A B sOff hpos C1 C3 hs0p hs2m hC13 hS13
  refine ⟨?_, ?_, ⟨s0 + sOff B, s0 - sOff A, ?_, ?_, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using ho 0 true
  · simpa [C3, cfg.firstParentThree] using ho 2 false
  · exact hs0p
  · exact hs2m
  refine ⟨cfg.firstPredecessor, 2, 0, cfg.firstProper, ?_, ?_, hC13, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C3] using cfg.firstParentThree
  · exact congrArg Prod.fst hS13
  · exact congrArg Prod.snd hS13

private theorem adjBE :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let B := BandVectors.2 (q 3) (q 2)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (hpos : ∀ (i : Fin 3), 0 < (q i.succ).1),
        let C1 : BandCircle := ⟨⟨q 1, Or.inl (hpos 0), q, cfg.proper.1, 1, rfl⟩, hpos 0⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl (hpos 2), q, cfg.proper.1, 3, rfl⟩, hpos 2⟩
        (PartialOdometerSlope (h 0 false) = some (s0 - sOff B)) → ((PartialOdometerSlope (h 2
            true) = some (s0 + sOff A)) → ((TileCentroid (cert.P 2 true) - TileCentroid (cert.P 0
            false) = (1 / 2 : Real) • GaussianRealPoint (I ^ 2 * (BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.1
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) → (((s0 + sOff A) - (s0 - sOff
            B) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 2 * (BandVectors.2
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) + BandVectors.2
            (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) → (SubtileLatticeAdjacent C1 C3
            (cert.P 0 false) (cert.P 2 true) (h 0 false) (h 2 true)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho I A B sOff hpos C1 C3 hs0m hs2p hC31 hS31
  refine ⟨?_, ?_, ⟨s0 - sOff B, s0 + sOff A, ?_, ?_, ?_⟩⟩
  · simpa [C1, cfg.firstChild] using ho 0 false
  · simpa [C3, cfg.firstParentThree] using ho 2 true
  · exact hs0m
  · exact hs2p
  refine ⟨cfg.firstPredecessor, 2, 2, cfg.firstProper, ?_, ?_, hC31, ?_, ?_⟩
  · simpa [C1] using cfg.firstChild
  · simpa [C3] using cfg.firstParentThree
  · exact congrArg Prod.fst hS31
  · exact congrArg Prod.snd hS31

private theorem adjCF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (hpos : ∀ (i : Fin 3), 0 < (q i.succ).1),
        let C2 : BandCircle := ⟨⟨q 2, Or.inl (hpos 1), q, cfg.proper.1, 2, rfl⟩, hpos 1⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl (hpos 2), q, cfg.proper.1, 3, rfl⟩, hpos 2⟩
        (PartialOdometerSlope (h 1 true) = some (s0 + sOff Y)) → ((PartialOdometerSlope (h 2
            false) = some (s0 - sOff A)) → ((TileCentroid (cert.P 2 false) - TileCentroid (cert.P
            1 true) = (1 / 2 : Real) • GaussianRealPoint (I ^ 3 * (BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → (((s0 - sOff A) - (s0 + sOff
            Y) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 3 * (BandVectors.2
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → (SubtileLatticeAdjacent C2
            C3 (cert.P 1 true) (cert.P 2 false) (h 1 true) (h 2 false)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho I A Y sOff hpos C2 C3 hs1p hs2m hC23 hS23
  refine ⟨?_, ?_, ⟨s0 + sOff Y, s0 - sOff A, ?_, ?_, ?_⟩⟩
  · simpa [C2, cfg.firstParentTwo, cfg.secondChild] using ho 1 true
  · simpa [C3, cfg.firstParentThree, cfg.secondParentOne] using ho 2 false
  · exact hs1p
  · exact hs2m
  refine ⟨cfg.secondPredecessor, 0, 3, cfg.secondProper, ?_, ?_, hC23, ?_, ?_⟩
  · simpa [C2] using cfg.secondChild
  · simpa [C3] using cfg.secondParentOne
  · exact congrArg Prod.fst hS23
  · exact congrArg Prod.snd hS23

private theorem adjDE :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), ∀ (s0 : Real × Real), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (cert.P i s) (h i s)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let A := BandVectors.2 (q 2) (q 1)
        let Y := BandVectors.2 (q 1) (q 3)
        let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
        ∀ (hpos : ∀ (i : Fin 3), 0 < (q i.succ).1),
        let C2 : BandCircle := ⟨⟨q 2, Or.inl (hpos 1), q, cfg.proper.1, 2, rfl⟩, hpos 1⟩
        let C3 : BandCircle := ⟨⟨q 3, Or.inl (hpos 2), q, cfg.proper.1, 3, rfl⟩, hpos 2⟩
        (PartialOdometerSlope (h 1 false) = some (s0 - sOff Y)) → ((PartialOdometerSlope (h 2
            true) = some (s0 + sOff A)) → ((TileCentroid (cert.P 2 true) - TileCentroid (cert.P 1
            false) = (1 / 2 : Real) • GaussianRealPoint (I ^ 1 * (BandVectors.1
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.1
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → (((s0 + sOff A) - (s0 - sOff
            Y) = (1 / 2 : Real) • GaussianRealPoint ((-I) ^ 1 * (BandVectors.2
            (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) + BandVectors.2
            (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) → (SubtileLatticeAdjacent C2
            C3 (cert.P 1 false) (cert.P 2 true) (h 1 false) (h 2 true)))))) ) := by
  classical
  intro q cfg C T cert h s0 ho I A Y sOff hpos C2 C3 hs1m hs2p hC32 hS32
  refine ⟨?_, ?_, ⟨s0 - sOff Y, s0 + sOff A, ?_, ?_, ?_⟩⟩
  · simpa [C2, cfg.firstParentTwo, cfg.secondChild] using ho 1 false
  · simpa [C3, cfg.firstParentThree, cfg.secondParentOne] using ho 2 true
  · exact hs1m
  · exact hs2p
  refine ⟨cfg.secondPredecessor, 0, 1, cfg.secondProper, ?_, ?_, hC32, ?_, ?_⟩
  · simpa [C2] using cfg.secondChild
  · simpa [C3] using cfg.secondParentOne
  · exact congrArg Prod.fst hS32
  · exact congrArg Prod.snd hS32

private theorem compatSelf :
    (by
      classical
      exact
        ∀ (a : PartialOdometer), OdometerCompatibility a a ) := by
  classical
  intro a
  right
  refine ⟨0, ?_⟩
  intro x hx hx'
  simp

private theorem compatSymm :
    (by
      classical
      exact
        ∀ {a : PartialOdometer}, ∀ {b : PartialOdometer}, (OdometerCompatibility a b) →
            (OdometerCompatibility b a) ) := by
  classical
  intro a b hab
  rcases hab with hdis | ⟨c, hc⟩
  · exact Or.inl hdis.symm
  · right
    refine ⟨-c, ?_⟩
    intro x hx hx'
    have := hc x hx' hx
    linarith

private theorem smallCompat :
    (by
      classical
      exact
        ∀ (a : PartialOdometer), ∀ (b : PartialOdometer), (((a.domain : Set GaussianInt) ∩
            (b.domain : Set GaussianInt)).Subsingleton) → (OdometerCompatibility a b) ) := by
  classical
  intro a b hs
  by_cases hn : ((a.domain : Set GaussianInt) ∩ (b.domain : Set GaussianInt)).Nonempty
  · rcases hn with ⟨x, ha, hb⟩
    right
    refine ⟨b.value x - a.value x, ?_⟩
    intro y hy hy'
    have hxy : y = x := hs ⟨hy, hy'⟩ ⟨ha, hb⟩
    subst y
    rfl
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hn
    exact Set.disjoint_iff_inter_eq_empty.mpr hn

private theorem hraw :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ a b : PeriodicSubtileIndex, a ≠ b → (¬ AllowedSubtileIncidence a b →
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b)).Subsingleton) ) := by
  classical
  intro q cfg C T cert a b hab
  exact (BandOriginalOccurrenceIntersectionClassification q cfg C T cert a b hab).2

private theorem htransZero :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), TileTranslation Z 0 = Z ) := by
  classical
  intro Z
  cases Z with
  | mk cells anchor =>
    change ProtoTile.mk (cells.image (fun x => x + 0)) (GaussianTranslation 0 anchor) =
      ProtoTile.mk cells anchor
    apply congrArg₂ ProtoTile.mk
    · simp []
    · simp [GaussianTranslation]

private theorem noAE :
    (by
      classical
      exact
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b)
            → (¬ ((a = ia ∧ b = ie) ∨ (a = ie ∧ b = ia))) ) := by
  classical
  intro ia ie a b hab
  induction hab
  case symm hab ih =>
    intro hbad
    apply ih
    simpa [or_comm, and_comm] using hbad
  all_goals
    intro hbad
    simp [ia, ie] at hbad
    all_goals omega

private theorem noBF :
    (by
      classical
      exact
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b)
            → (¬ ((a = ib ∧ b = iff) ∨ (a = iff ∧ b = ib))) ) := by
  classical
  intro ib iff a b hab
  induction hab
  case symm hab ih =>
    intro hbad
    apply ih
    simpa [or_comm, and_comm] using hbad
  all_goals
    intro hbad
    simp [ib, iff] at hbad
    all_goals omega

private theorem noCD :
    (by
      classical
      exact
        let ic : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let id : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b)
            → (¬ ((a = ic ∧ b = id) ∨ (a = id ∧ b = ic))) ) := by
  classical
  intro ic id a b hab
  induction hab
  case symm hab ih =>
    intro hbad
    apply ih
    simpa [or_comm, and_comm] using hbad
  all_goals
    intro hbad
    simp [ic, id] at hbad
    all_goals omega

private theorem noEF :
    (by
      classical
      exact
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b)
            → (¬ ((a = ie ∧ b = iff) ∨ (a = iff ∧ b = ie))) ) := by
  classical
  intro ie iff a b hab
  induction hab
  case symm hab ih =>
    intro hbad
    apply ih
    simpa [or_comm, and_comm] using hbad
  all_goals
    intro hbad
    simp [ie, iff] at hbad

private theorem noCE :
    (by
      classical
      exact
        let ic : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b)
            → (¬ ((a = ic ∧ b = ie) ∨ (a = ie ∧ b = ic))) ) := by
  classical
  intro ic ie a b hab
  induction hab
  case symm hab ih =>
    intro hbad
    apply ih
    simpa [or_comm, and_comm] using hbad
  all_goals
    intro hbad
    simp [ic, ie] at hbad
    all_goals omega

private theorem noDF :
    (by
      classical
      exact
        let id : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a b)
            → (¬ ((a = id ∧ b = iff) ∨ (a = iff ∧ b = id))) ) := by
  classical
  intro id iff a b hab
  induction hab
  case symm hab ih =>
    intro hbad
    apply ih
    simpa [or_comm, and_comm] using hbad
  all_goals
    intro hbad
    simp [id, iff] at hbad
    all_goals omega

private theorem nAE :
    (by
      classical
      exact
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a
            b) → (¬ ((a = ia ∧ b = ie) ∨ (a = ie ∧ b = ia)))) → (¬ AllowedSubtileIncidence ia ie)
            ) := by
  classical
  intro ia ie noAE hab
  exact noAE ia ie hab (Or.inl ⟨rfl, rfl⟩)

private theorem nBF :
    (by
      classical
      exact
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a
            b) → (¬ ((a = ib ∧ b = iff) ∨ (a = iff ∧ b = ib)))) → (¬ AllowedSubtileIncidence ib
            iff) ) := by
  classical
  intro ib iff noBF hab
  exact noBF ib iff hab (Or.inl ⟨rfl, rfl⟩)

private theorem nCD :
    (by
      classical
      exact
        let ic : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let id : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a
            b) → (¬ ((a = ic ∧ b = id) ∨ (a = id ∧ b = ic)))) → (¬ AllowedSubtileIncidence ic id)
            ) := by
  classical
  intro ic id noCD hab
  exact noCD ic id hab (Or.inl ⟨rfl, rfl⟩)

private theorem nEF :
    (by
      classical
      exact
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a
            b) → (¬ ((a = ie ∧ b = iff) ∨ (a = iff ∧ b = ie)))) → (¬ AllowedSubtileIncidence ie
            iff) ) := by
  classical
  intro ie iff noEF hab
  exact noEF ie iff hab (Or.inl ⟨rfl, rfl⟩)

private theorem nCE :
    (by
      classical
      exact
        let ic : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a
            b) → (¬ ((a = ic ∧ b = ie) ∨ (a = ie ∧ b = ic)))) → (¬ AllowedSubtileIncidence ic ie)
            ) := by
  classical
  intro ic ie noCE hab
  exact noCE ic ie hab (Or.inl ⟨rfl, rfl⟩)

private theorem nDF :
    (by
      classical
      exact
        let id : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (AllowedSubtileIncidence a
            b) → (¬ ((a = id ∧ b = iff) ∨ (a = iff ∧ b = id)))) → (¬ AllowedSubtileIncidence id
            iff) ) := by
  classical
  intro id iff noDF hab
  exact noDF id iff hab (Or.inl ⟨rfl, rfl⟩)

private theorem smallAE :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (e : Bool), (h i
            e).domain = FootprintVertices (cert.P i e)) → (
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v ia = cert.P 0 true) →
            ((SubtileOccurrenceInterpretation cert.P cert.u cert.v ie = cert.P 2 true) →
            ((FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ia) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ie) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ia) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            ie)).Subsingleton) → ((((h 0 true).domain : Set GaussianInt) ∩ (h 2
            true).domain).Subsingleton)))) ) := by
  classical
  intro q cfg C T cert h hdomain ia ie occA occE rawAE
  rcases rawAE with he | hs
  · rw [occA, occE] at he
    rw [hdomain 0 true, hdomain 2 true, he]
    exact Set.subsingleton_empty
  · rw [occA, occE] at hs
    simpa [hdomain 0 true, hdomain 2 true] using hs

private theorem smallBF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (e : Bool), (h i
            e).domain = FootprintVertices (cert.P i e)) → (
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v ib = cert.P 0 false) →
            ((SubtileOccurrenceInterpretation cert.P cert.u cert.v iff = cert.P 2 false) →
            ((FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ib) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v iff) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ib) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            iff)).Subsingleton) → ((((h 0 false).domain : Set GaussianInt) ∩ (h 2
            false).domain).Subsingleton)))) ) := by
  classical
  intro q cfg C T cert h hdomain ib iff occB occF rawBF
  rcases rawBF with he | hs
  · rw [occB, occF] at he
    rw [hdomain 0 false, hdomain 2 false, he]
    exact Set.subsingleton_empty
  · rw [occB, occF] at hs
    simpa [hdomain 0 false, hdomain 2 false] using hs

private theorem smallCD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (e : Bool), (h i
            e).domain = FootprintVertices (cert.P i e)) → (
        let ic : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let id : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v ic = cert.P 1 true) →
            ((SubtileOccurrenceInterpretation cert.P cert.u cert.v id = cert.P 1 false) →
            ((FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ic) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v id) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ic) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            id)).Subsingleton) → ((((h 1 true).domain : Set GaussianInt) ∩ (h 1
            false).domain).Subsingleton)))) ) := by
  classical
  intro q cfg C T cert h hdomain ic id occC occD rawCD
  rcases rawCD with he | hs
  · rw [occC, occD] at he
    rw [hdomain 1 true, hdomain 1 false, he]
    exact Set.subsingleton_empty
  · rw [occC, occD] at hs
    simpa [hdomain 1 true, hdomain 1 false] using hs

private theorem smallEF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (e : Bool), (h i
            e).domain = FootprintVertices (cert.P i e)) → (
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v ie = cert.P 2 true) →
            ((SubtileOccurrenceInterpretation cert.P cert.u cert.v iff = cert.P 2 false) →
            ((FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ie) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v iff) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ie) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            iff)).Subsingleton) → ((((h 2 true).domain : Set GaussianInt) ∩ (h 2
            false).domain).Subsingleton)))) ) := by
  classical
  intro q cfg C T cert h hdomain ie iff occE occF rawEF
  rcases rawEF with he | hs
  · rw [occE, occF] at he
    rw [hdomain 2 true, hdomain 2 false, he]
    exact Set.subsingleton_empty
  · rw [occE, occF] at hs
    simpa [hdomain 2 true, hdomain 2 false] using hs

private theorem smallCE :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (e : Bool), (h i
            e).domain = FootprintVertices (cert.P i e)) → (
        let ic : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v ic = cert.P 1 true) →
            ((SubtileOccurrenceInterpretation cert.P cert.u cert.v ie = cert.P 2 true) →
            ((FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ic) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ie) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v ic) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            ie)).Subsingleton) → ((((h 1 true).domain : Set GaussianInt) ∩ (h 2
            true).domain).Subsingleton)))) ) := by
  classical
  intro q cfg C T cert h hdomain ic ie occC occE rawCE
  rcases rawCE with he | hs
  · rw [occC, occE] at he
    rw [hdomain 1 true, hdomain 2 true, he]
    exact Set.subsingleton_empty
  · rw [occC, occE] at hs
    simpa [hdomain 1 true, hdomain 2 true] using hs

private theorem smallDF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (h : Fin 3 → Bool → PartialOdometer), (∀ (i : Fin 3), ∀ (e : Bool), (h i
            e).domain = FootprintVertices (cert.P i e)) → (
        let id : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v id = cert.P 1 false) →
            ((SubtileOccurrenceInterpretation cert.P cert.u cert.v iff = cert.P 2 false) →
            ((FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v id) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v iff) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v id) ∩
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            iff)).Subsingleton) → ((((h 1 false).domain : Set GaussianInt) ∩ (h 2
            false).domain).Subsingleton)))) ) := by
  classical
  intro q cfg C T cert h hdomain id iff occD occF rawDF
  rcases rawDF with he | hs
  · rw [occD, occF] at he
    rw [hdomain 1 false, hdomain 2 false, he]
    exact Set.subsingleton_empty
  · rw [occD, occF] at hs
    simpa [hdomain 1 false, hdomain 2 false] using hs

end OrdinaryCompatibilityGeometry

theorem P4250T1OrdinaryCompatibility
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (h : Fin 3 → Bool → PartialOdometer) (s0 : Real × Real)
    (ho : ∀ i s, TileOdometer (q i.succ) (cert.P i s) (h i s))
    (hp : ∀ i s, PartialOdometerSlope (h i s) = some
      (s0 + (if s = true then (1 : Real) else -1) •
        P4250T1SlopeOffset
          (BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))))) :
    ∀ i s j t,
      ¬ ((i = 0 ∧ j = 0 ∧ s ≠ t) ∨
        (((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ∧ s = t)) →
      OdometerCompatibility (h i s) (h j t) := by
-- BODY
  classical
  let I : GaussianInt := ⟨0, 1⟩
  let U := BandVectors.1 (q 2) (q 1)
  let W := BandVectors.1 (q 3) (q 2)
  let A := BandVectors.2 (q 2) (q 1)
  let B := BandVectors.2 (q 3) (q 2)
  let X := BandVectors.1 (q 1) (q 3)
  let Y := BandVectors.2 (q 1) (q 3)
  let cOff (z : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint z -
      (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  let sOff (z : GaussianInt) : Real × Real := P4250T1SlopeOffset z
  have hImul : I * I = -1 := OrdinaryCompatibilityGeometry.hImul
  have hI2 : I ^ 2 = -1 := by rw [pow_two, hImul]
  have laws := VectorRecursionLaws q cfg.proper.1
  have firstLaws := VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1
  have secondLaws := VectorRecursionLaws cfg.secondPredecessor cfg.secondProper.1
  have hX := OrdinaryCompatibilityGeometry.hX q laws
  have hpos := OrdinaryCompatibilityGeometry.hpos q cfg
  let C1 : BandCircle := ⟨⟨q 1, Or.inl (hpos 0), q, cfg.proper.1, 1, rfl⟩, hpos 0⟩
  let C2 : BandCircle := ⟨⟨q 2, Or.inl (hpos 1), q, cfg.proper.1, 2, rfl⟩, hpos 1⟩
  let C3 : BandCircle := ⟨⟨q 3, Or.inl (hpos 2), q, cfg.proper.1, 3, rfl⟩, hpos 2⟩
  have cent (i : Fin 3) (e : Bool) :
      TileCentroid (cert.P i e) - TileCentroid T =
        (if e then (1 : Real) else -1) •
          cOff (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) :=
    (OrdinaryCompatibilityGeometry.occCent) q T (cert.P i e) i e (cert.outer_occurrence i e)
  have hc0p : TileCentroid (cert.P 0 true) - TileCentroid T = cOff W := by
    simpa [Fin.add_def, W] using cent 0 true
  have hc0m : TileCentroid (cert.P 0 false) - TileCentroid T = -cOff W := by
    simpa [Fin.add_def, W] using cent 0 false
  have hc1p : TileCentroid (cert.P 1 true) - TileCentroid T = cOff X := by
    simpa [Fin.add_def, X] using cent 1 true
  have hc1m : TileCentroid (cert.P 1 false) - TileCentroid T = -cOff X := by
    simpa [Fin.add_def, X] using cent 1 false
  have hc2p : TileCentroid (cert.P 2 true) - TileCentroid T = cOff U := by
    simpa [Fin.add_def, U] using cent 2 true
  have hc2m : TileCentroid (cert.P 2 false) - TileCentroid T = -cOff U := by
    simpa [Fin.add_def, U] using cent 2 false
  have slope (i : Fin 3) (e : Bool) :
      PartialOdometerSlope (h i e) = some
        (s0 + (if e then (1 : Real) else -1) •
          sOff (BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ)))) :=
              OrdinaryCompatibilityGeometry.slope q h s0 hp i e
  have hs0p : PartialOdometerSlope (h 0 true) = some (s0 + sOff B) := by
    simpa [Fin.add_def, B, sOff] using slope 0 true
  have hs0m : PartialOdometerSlope (h 0 false) = some (s0 - sOff B) := by
    simpa [Fin.add_def, B, sOff, sub_eq_add_neg, smul_eq_mul] using slope 0 false
  have hs1p : PartialOdometerSlope (h 1 true) = some (s0 + sOff Y) := by
    simpa [Fin.add_def, Y, sOff] using slope 1 true
  have hs1m : PartialOdometerSlope (h 1 false) = some (s0 - sOff Y) := by
    simpa [Fin.add_def, Y, sOff, sub_eq_add_neg, smul_eq_mul] using slope 1 false
  have hs2p : PartialOdometerSlope (h 2 true) = some (s0 + sOff A) := by
    simpa [Fin.add_def, A, sOff] using slope 2 true
  have hs2m : PartialOdometerSlope (h 2 false) = some (s0 - sOff A) := by
    simpa [Fin.add_def, A, sOff, sub_eq_add_neg, smul_eq_mul] using slope 2 false
  have cadd := OrdinaryCompatibilityGeometry.cadd
  have cneg := OrdinaryCompatibilityGeometry.cneg
  have sadd (a b : GaussianInt) : sOff (a + b) = sOff a + sOff b := by
    apply Prod.ext <;> simp [sOff, P4250T1SlopeOffset]  <;> ring
  have sneg (a : GaussianInt) : sOff (-a) = -sOff a := by
    apply Prod.ext <;> simp [sOff, P4250T1SlopeOffset]  <;> ring
  have sY := OrdinaryCompatibilityGeometry.sY q (OrdinaryCompatibilityGeometry.hY q laws) sadd sneg
  have gaussianPointNeg := OrdinaryCompatibilityGeometry.gaussianPointNeg
  have hV20 := OrdinaryCompatibilityGeometry.hV20 q cfg
  have hflip12 := firstLaws.2.2.2.2 cfg.firstProper 1
  have hsumV12 := OrdinaryCompatibilityGeometry.hsumV12 q cfg hV20
      (OrdinaryCompatibilityGeometry.hflip120 q cfg hV20 hflip12)
  have hflip03 := firstLaws.2.2.2.2 cfg.firstProper 2
  have hsumV03 := OrdinaryCompatibilityGeometry.hsumV03 q cfg hImul
      (OrdinaryCompatibilityGeometry.hV30 q cfg hImul firstLaws
      (OrdinaryCompatibilityGeometry.hV21 q cfg hV20)) hflip03
  have hflipSecond := secondLaws.2.2.2.2 cfg.secondProper 0
  have hsumVsecond := OrdinaryCompatibilityGeometry.hsumVsecond q cfg hflipSecond
  have hsumA12 := OrdinaryCompatibilityGeometry.hsumA12 q cfg hflip12
  have hsumAsecond := OrdinaryCompatibilityGeometry.hsumAsecond q cfg hflipSecond
  have hsumA03 := OrdinaryCompatibilityGeometry.hsumA03 q cfg hImul
      (OrdinaryCompatibilityGeometry.hA30 q cfg hImul (OrdinaryCompatibilityGeometry.hrot2A q
      cfg) (OrdinaryCompatibilityGeometry.hA13 q cfg firstLaws
      (OrdinaryCompatibilityGeometry.hA21global q cfg (OrdinaryCompatibilityGeometry.hrotAglobal
      q cfg)))) (OrdinaryCompatibilityGeometry.hflip03A q cfg hflip03)
  have slopeCoord := OrdinaryCompatibilityGeometry.slopeCoord
  have hnegI3 := OrdinaryCompatibilityGeometry.hnegI3 (OrdinaryCompatibilityGeometry.hI3 hI2)
  have dompos (i : Fin 3) : 0 < (q i.succ).1 := hpos i
  have circleEq1 : C1.1.1 = q 1 := rfl
  have circleEq2 : C2.1.1 = q 2 := rfl
  have circleEq3 : C3.1.1 = q 3 := rfl
  have compatSelf (a : PartialOdometer) : OdometerCompatibility a a :=
      OrdinaryCompatibilityGeometry.compatSelf a
  have compatSymm {a b : PartialOdometer} (hab : OdometerCompatibility a b) :=
      OrdinaryCompatibilityGeometry.compatSymm (a := a) (b := b) hab
  have smallCompat := OrdinaryCompatibilityGeometry.smallCompat
  have ord1 : OdometerCompatibility (h 0 true) (h 1 false) :=
    (RightSubtileOdometerCompatibility.2 C1 C2 (cert.P 0 true)
      (cert.P 1 false) (h 0 true) (h 1 false) (OrdinaryCompatibilityGeometry.adjAD q cfg C T cert
          h s0 ho hpos hs0p hs1m (OrdinaryCompatibilityGeometry.hC12 q cfg C T cert hX hc0p hc1m
          hsumV12) (OrdinaryCompatibilityGeometry.hS12 q cfg s0 hImul sY hsumA12 slopeCoord
          hnegI3)))
  have ord2 : OdometerCompatibility (h 0 false) (h 1 true) :=
    (RightSubtileOdometerCompatibility.2 C1 C2 (cert.P 0 false)
      (cert.P 1 true) (h 0 false) (h 1 true) (OrdinaryCompatibilityGeometry.adjBC q cfg C T cert
          h s0 ho hpos hs0m hs1p (OrdinaryCompatibilityGeometry.hC21 q cfg C T cert hX hc0m hc1p
          hsumV12) (OrdinaryCompatibilityGeometry.hS21 q cfg s0 hImul sY gaussianPointNeg hsumA12
          slopeCoord)))
  have ord3 : OdometerCompatibility (h 0 true) (h 2 false) :=
    (RightSubtileOdometerCompatibility.2 C1 C3 (cert.P 0 true)
      (cert.P 2 false) (h 0 true) (h 2 false) (OrdinaryCompatibilityGeometry.adjAF q cfg C T cert
          h s0 ho hpos hs0p hs2m (OrdinaryCompatibilityGeometry.hC13 q cfg C T cert hc0p hc2m
          hsumV03) (OrdinaryCompatibilityGeometry.hS13 q cfg s0 sadd hsumA03)))
  have ord4 : OdometerCompatibility (h 0 false) (h 2 true) :=
    (RightSubtileOdometerCompatibility.2 C1 C3 (cert.P 0 false)
      (cert.P 2 true) (h 0 false) (h 2 true) (OrdinaryCompatibilityGeometry.adjBE q cfg C T cert
          h s0 ho hpos hs0m hs2p (OrdinaryCompatibilityGeometry.hC31 q cfg C T cert hc0m hc2p
          hsumV03) (OrdinaryCompatibilityGeometry.hS31 q cfg s0 hI2 sadd hsumA03)))
  have ord5 : OdometerCompatibility (h 1 true) (h 2 false) :=
    (RightSubtileOdometerCompatibility.2 C2 C3 (cert.P 1 true)
      (cert.P 2 false) (h 1 true) (h 2 false) (OrdinaryCompatibilityGeometry.adjCF q cfg C T cert
          h s0 ho hpos hs1p hs2m (OrdinaryCompatibilityGeometry.hC23 q cfg C T cert hX hc1p hc2m
          hsumVsecond) (OrdinaryCompatibilityGeometry.hS23 q cfg s0 hImul sY hsumAsecond
          slopeCoord hnegI3)))
  have ord6 : OdometerCompatibility (h 1 false) (h 2 true) :=
    (RightSubtileOdometerCompatibility.2 C2 C3 (cert.P 1 false)
      (cert.P 2 true) (h 1 false) (h 2 true) (OrdinaryCompatibilityGeometry.adjDE q cfg C T cert
          h s0 ho hpos hs1m hs2p (OrdinaryCompatibilityGeometry.hC32 q cfg C T cert hX hc1m hc2p
          hsumVsecond) (OrdinaryCompatibilityGeometry.hS32 q cfg s0 hImul sY gaussianPointNeg
          hsumAsecond slopeCoord)))
  have ord1r : OdometerCompatibility (h 1 false) (h 0 true) := compatSymm ord1
  have ord2r : OdometerCompatibility (h 1 true) (h 0 false) := compatSymm ord2
  have ord3r : OdometerCompatibility (h 2 false) (h 0 true) := compatSymm ord3
  have ord4r : OdometerCompatibility (h 2 true) (h 0 false) := compatSymm ord4
  have ord5r : OdometerCompatibility (h 2 false) (h 1 true) := compatSymm ord5
  have ord6r : OdometerCompatibility (h 2 true) (h 1 false) := compatSymm ord6
  have hraw := OrdinaryCompatibilityGeometry.hraw q cfg C T cert
  have hdomain (i : Fin 3) (e : Bool) :
      (h i e).domain = FootprintVertices (cert.P i e) :=
    PositiveCurvatureTileOdometerDomain (q i.succ) (cert.P i e) (h i e) (hpos i)
      (ho i e)
  have htransZero (Z : ProtoTile) : TileTranslation Z 0 = Z :=
      OrdinaryCompatibilityGeometry.htransZero Z
  let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let ic : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let id : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  let ie : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
  let iff : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
  have occA : SubtileOccurrenceInterpretation cert.P cert.u cert.v ia = cert.P 0 true := by
    simp [SubtileOccurrenceInterpretation, ia, htransZero]
  have occB : SubtileOccurrenceInterpretation cert.P cert.u cert.v ib = cert.P 0 false := by
    simp [SubtileOccurrenceInterpretation, ib, htransZero]
  have occC : SubtileOccurrenceInterpretation cert.P cert.u cert.v ic = cert.P 1 true := by
    simp [SubtileOccurrenceInterpretation, ic, htransZero]
  have occD : SubtileOccurrenceInterpretation cert.P cert.u cert.v id = cert.P 1 false := by
    simp [SubtileOccurrenceInterpretation, id, htransZero]
  have occE : SubtileOccurrenceInterpretation cert.P cert.u cert.v ie = cert.P 2 true := by
    simp [SubtileOccurrenceInterpretation, ie, htransZero]
  have occF : SubtileOccurrenceInterpretation cert.P cert.u cert.v iff = cert.P 2 false := by
    simp [SubtileOccurrenceInterpretation, iff, htransZero]
  have rawAE := hraw ia ie (by decide) (OrdinaryCompatibilityGeometry.nAE
      (OrdinaryCompatibilityGeometry.noAE))
  have rawBF := hraw ib iff (by decide) (OrdinaryCompatibilityGeometry.nBF
      (OrdinaryCompatibilityGeometry.noBF))
  have rawCD := hraw ic id (by decide) (OrdinaryCompatibilityGeometry.nCD
      (OrdinaryCompatibilityGeometry.noCD))
  have rawEF := hraw ie iff (by decide) (OrdinaryCompatibilityGeometry.nEF
      (OrdinaryCompatibilityGeometry.noEF))
  have rawCE := hraw ic ie (by decide) (OrdinaryCompatibilityGeometry.nCE
      (OrdinaryCompatibilityGeometry.noCE))
  have rawDF := hraw id iff (by decide) (OrdinaryCompatibilityGeometry.nDF
      (OrdinaryCompatibilityGeometry.noDF))
  have compatAE := smallCompat (h 0 true) (h 2 true) (OrdinaryCompatibilityGeometry.smallAE q cfg
      C T cert h hdomain occA occE rawAE)
  have compatBF := smallCompat (h 0 false) (h 2 false) (OrdinaryCompatibilityGeometry.smallBF q
      cfg C T cert h hdomain occB occF rawBF)
  have compatCD := smallCompat (h 1 true) (h 1 false) (OrdinaryCompatibilityGeometry.smallCD q
      cfg C T cert h hdomain occC occD rawCD)
  have compatEF := smallCompat (h 2 true) (h 2 false) (OrdinaryCompatibilityGeometry.smallEF q
      cfg C T cert h hdomain occE occF rawEF)
  have compatCE := smallCompat (h 1 true) (h 2 true) (OrdinaryCompatibilityGeometry.smallCE q cfg
      C T cert h hdomain occC occE rawCE)
  have compatDF := smallCompat (h 1 false) (h 2 false) (OrdinaryCompatibilityGeometry.smallDF q
      cfg C T cert h hdomain occD occF rawDF)
  have compatAEr := compatSymm compatAE
  have compatBFr := compatSymm compatBF
  have compatCDr := compatSymm compatCD
  have compatEFr := compatSymm compatEF
  have compatCEr := compatSymm compatCE
  have compatDFr := compatSymm compatDF
  intro i s j t hnot
  fin_cases i <;> fin_cases j <;> cases s <;> cases t
  all_goals simp at hnot
  all_goals first | assumption | exact compatSelf _

end ApollonianSuperharmonic

end
