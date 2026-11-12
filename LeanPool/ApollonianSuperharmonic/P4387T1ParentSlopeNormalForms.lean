/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4387T1ParentSlopeNormalForms]

/-!
# P4387T1ParentSlopeNormalForms

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4387T1ParentSlopeNormalForms
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q) :
    let A := BandVectors.2
    let J : GaussianInt := -⟨0, 1⟩
    let U := A (q 2) (q 1)
    let W := A (q 3) (q 2)
    A (q 1) (q 3) = -U - W ∧
    A (q 1) (q 2) = J * U ∧
    A (q 3) (q 1) = J * (U + W) ∧
    A (q 2) (q 3) = J * W ∧
    A (q 0) (q 1) = U - J * (U + W) ∧
    A (q 0) (q 2) = W + J * U ∧
    A (q 0) (q 3) = -U - W + J * W ∧
    A (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) +
        A (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) = (1 + J) * U ∧
    A (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
        A (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) = (J - 1) * (U + W) ∧
    A (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
        A (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) = (1 + J) * W := by
-- BODY
  dsimp only
  obtain ⟨_, hsum, _, hin1, flip⟩ := VectorRecursionLaws q cfg.proper.1
  have laws2 := VectorRecursionLaws _ (SemiProperQuadruple.rotate cfg.proper.1)
  have laws3 := VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate cfg.proper.1))
  have hin2 : BandVectors.2 (q 2) (q 0) = BandVectors.2 (q 2) (q 1) +
      (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 3) (q 2) := by
    simpa using laws2.2.2.2.1
  have hin3 : BandVectors.2 (q 3) (q 0) = BandVectors.2 (q 3) (q 2) +
      (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 1) (q 3) := by
    simpa using laws3.2.2.2.1
  have h13 : BandVectors.2 (q 1) (q 3) =
      -BandVectors.2 (q 2) (q 1) - BandVectors.2 (q 3) (q 2) := by
    apply eq_of_sub_eq_zero
    calc
      _ = BandVectors.2 (q 3) (q 2) + BandVectors.2 (q 1) (q 3) +
          BandVectors.2 (q 2) (q 1) := by ring
      _ = 0 := hsum
  have firstFlip := (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).2.2.2.2
    cfg.firstProper
  have secondFlip := (VectorRecursionLaws cfg.secondPredecessor cfg.secondProper.1).2.2.2.2
    cfg.secondProper
  have h12 := (firstFlip 1).2
  have hf13 := (firstFlip 2).2
  have h23 := (secondFlip 0).2
  change BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2) =
    -(⟨0, 1⟩ : GaussianInt) *
      BandVectors.2 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) at h12
  change BandVectors.2 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3) =
    -(⟨0, 1⟩ : GaussianInt) *
      BandVectors.2 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) at hf13
  change BandVectors.2 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1) =
    -(⟨0, 1⟩ : GaussianInt) *
      BandVectors.2 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) at h23
  rw [cfg.firstChild, cfg.firstParentTwo] at h12
  rw [cfg.firstChild, cfg.firstParentThree] at hf13
  rw [cfg.secondChild, cfg.secondParentOne] at h23
  have h31 : BandVectors.2 (q 3) (q 1) =
      -(⟨0, 1⟩ : GaussianInt) *
        (BandVectors.2 (q 2) (q 1) + BandVectors.2 (q 3) (q 2)) := by
    calc
      _ = (⟨0, 1⟩ : GaussianInt) *
          (-(⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 3) (q 1)) := by
        ext <;> simp
      _ = (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 1) (q 3) := by rw [← hf13]
      _ = _ := by rw [h13]; ring
  have fout1 := (flip cfg.proper 0).2
  have fout2 := (flip cfg.proper 1).2
  have fout3 := (flip cfg.proper 2).2
  simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl] at fout1
  simp only [show (1 : Fin 3).succ = (2 : Fin 4) from rfl] at fout2
  simp only [show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at fout3
  refine ⟨h13, h12, h31, h23, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fout1, hin1, h13]
    ext <;> simp <;> ring
  · rw [fout2, hin2]
    ext <;> simp; ring
  · rw [fout3, hin3, h13]
    ext <;> simp <;> ring
  · rw [cfg.firstChild, cfg.firstParentTwo, h12]
    ring
  · rw [cfg.firstChild, cfg.firstParentThree, h13, h31]
    ring
  · rw [cfg.secondChild, cfg.secondParentOne, h23]
    ring

end ApollonianSuperharmonic

end
