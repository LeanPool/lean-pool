/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandRetainedBoundaryGenealogy
public import LeanPool.ApollonianSuperharmonic.DiamondCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.DiamondRegimeConverse
public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse

-- [TABLET NODE: BandRegimeClassification]

/-!
# BandRegimeClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandRegimeClassification (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    ∃ (r : Fin 3) (g : BandPackingSymmetry),
      let q' := BandPackingSymmetryQuadrupleAction g
        ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
      Xor
        (∃ P : FordFareyParameter,
          1 < P.q ∧ q' = FordRecursiveQuadruple P)
        (Xor
          (∃ K : DiamondParameter,
            1 < K.1 ∧ q' = DiamondRecursiveQuadruple K)
          (Nonempty (BandOrderedGeneralConfiguration q'))) := by
-- BODY
  classical
  by_cases hline : ∃ i : Fin 4, (q i).1 = 0
  · obtain ⟨r, g, P, hFord⟩ := FordRegimeConverse q hq hline
    have hP := hFord.1
    have heq := hFord.2.2.2.2
    refine ⟨r, g, ?_⟩
    dsimp
    apply Or.inl
    refine ⟨⟨P, hP, heq⟩, ?_⟩
    intro hright
    rcases hright with hdiamond | hgeneral
    · rcases hdiamond with ⟨⟨K, hK, hdiamond⟩, hnot⟩
      have hz :
          (BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] 3).1 = 0 := by
        rw [heq]
        simp [FordRecursiveQuadruple]
      rw [hdiamond] at hz
      simp [DiamondRecursiveQuadruple] at hz
      omega
    · rcases hgeneral with ⟨hconfig, hnot⟩
      rcases hconfig with ⟨configuration⟩
      apply configuration.noLine 3
      rw [heq]
      simp [FordRecursiveQuadruple]
  · have hnoLine : ∀ i : Fin 4, (q i).1 ≠ 0 := by
      intro i hi
      exact hline ⟨i, hi⟩
    by_cases htwoUnits : ∃ i j : Fin 4,
        i ≠ j ∧ (q i).1 = 1 ∧ (q j).1 = 1
    · obtain ⟨r, g, K, hK, _, _, heq⟩ :=
        DiamondRegimeConverse q hq hnoLine htwoUnits
      refine ⟨r, g, ?_⟩
      dsimp
      apply Or.inr
      refine ⟨?_, ?_⟩
      · apply Or.inl
        refine ⟨⟨K, hK, heq⟩, ?_⟩
        intro hgeneral
        rcases hgeneral with ⟨configuration⟩
        have hfirst :
            (BandPackingSymmetryQuadrupleAction g
              ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] 1).1 = 1 := by
          rw [heq]
          simp [DiamondRecursiveQuadruple]
        have hsecond :
            (BandPackingSymmetryQuadrupleAction g
              ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] 2).1 = 1 := by
          rw [heq]
          simp [DiamondRecursiveQuadruple]
        have indices := configuration.atMostOneUnit 1 2 hfirst hsecond
        omega
      · intro hford
        rcases hford with ⟨P, hP, hford⟩
        have hz :
            (BandPackingSymmetryQuadrupleAction g
              ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] 3).1 = 0 := by
          simp [hford, FordRecursiveQuadruple]
        rw [heq] at hz
        simp [DiamondRecursiveQuadruple] at hz
        omega
    · have hatMostOneUnit : ∀ i j : Fin 4,
          (q i).1 = 1 → (q j).1 = 1 → i = j := by
        intro i j hi hj
        apply Classical.byContradiction
        intro hne
        exact htwoUnits ⟨i, j, hne, hi, hj⟩
      obtain ⟨r, g, hgeneral⟩ :=
        BandRetainedBoundaryGenealogy q hq hnoLine hatMostOneUnit
      refine ⟨r, g, ?_⟩
      dsimp
      apply Or.inr
      refine ⟨?_, ?_⟩
      · apply Or.inr
        refine ⟨hgeneral, ?_⟩
        intro hdiamond
        rcases hgeneral with ⟨configuration⟩
        rcases hdiamond with ⟨K, hK, heq⟩
        have hfirst :
            (BandPackingSymmetryQuadrupleAction g
              ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] 1).1 = 1 := by
          rw [heq]
          simp [DiamondRecursiveQuadruple]
        have hsecond :
            (BandPackingSymmetryQuadrupleAction g
              ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] 2).1 = 1 := by
          rw [heq]
          simp [DiamondRecursiveQuadruple]
        have indices := configuration.atMostOneUnit 1 2 hfirst hsecond
        omega
      · intro hford
        rcases hgeneral with ⟨configuration⟩
        rcases hford with ⟨P, hP, heq⟩
        apply configuration.noLine 3
        rw [heq]
        simp [FordRecursiveQuadruple]

end ApollonianSuperharmonic

end
