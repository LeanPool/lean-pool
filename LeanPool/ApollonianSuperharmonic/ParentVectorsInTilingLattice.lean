/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.TilingLattice
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: ParentVectorsInTilingLattice]

/-!
# ParentVectorsInTilingLattice

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ParentVectorsInTilingLattice
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (i : Fin 3) (Cᵢ : BandCircle) (hCᵢ : q i.succ = Cᵢ.1.1) :
    BandVectors.1 (q ((i + 1).succ)) (q i.succ) ∈ TilingLattice Cᵢ ∧
    BandVectors.1 (q ((i + 2).succ)) (q i.succ) ∈ TilingLattice Cᵢ := by
-- BODY
  induction hq.1 generalizing i Cᵢ with
  | base z =>
      have positive := Cᵢ.2
      fin_cases i
      · have unit : Cᵢ.1.1.1 = 1 := by
          simpa using (congrArg (fun x => x.1) hCᵢ).symm
        simp [TilingLattice, unit]
      · rw [← hCᵢ] at positive
        have coordinate := congrArg (fun x => x.1) hCᵢ
        have contradiction : (0 : ℤ) < 0 := by simp at positive
        omega
      · rw [← hCᵢ] at positive
        have coordinate := congrArg (fun x => x.1) hCᵢ
        have contradiction : (0 : ℤ) < 0 := by simp at positive
        omega
  | @rotate predecessor semi ih =>
      have previous : ProperBandQuadruple predecessor := by
        refine ⟨semi, ?_⟩
        intro j
        fin_cases j
        · simpa using hq.2 ⟨2, by decide⟩
        · simpa using hq.2 ⟨0, by decide⟩
        · simpa using hq.2 ⟨1, by decide⟩
      fin_cases i
      · simpa using ih previous ⟨1, by decide⟩ Cᵢ (by simpa using hCᵢ)
      · simpa using ih previous ⟨2, by decide⟩ Cᵢ (by simpa using hCᵢ)
      · simpa using ih previous ⟨0, by decide⟩ Cᵢ (by simpa using hCᵢ)
  | @successor predecessor semi ih =>
      have successorSemi : SemiProperQuadruple _ :=
        SemiProperQuadruple.successor semi
      have systemLaw : RecursiveVectorSystem BandVectors :=
        by simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
      rcases systemLaw with ⟨zeroLaw, baseLaw, stepLaw, flipLaw⟩
      rcases SemiProperForestClassification predecessor semi with ⟨nonnegative, alternatives⟩
      rcases alternatives with root | root | root | previous
      · rcases root with ⟨z, rfl⟩
        have alternatives : Cᵢ.1.1.1 = 1 ∨ Cᵢ.1.1.1 = 0 := by
          have coordinate := congrArg (fun x => x.1) hCᵢ
          fin_cases i <;> simp at coordinate ⊢ <;> omega
        rcases alternatives with unit | zero
        · simp [TilingLattice, unit]
        · have positive := Cᵢ.2
          omega
      · rcases root with ⟨z, rfl⟩
        have alternatives : Cᵢ.1.1.1 = 1 ∨ Cᵢ.1.1.1 = 0 := by
          have coordinate := congrArg (fun x => x.1) hCᵢ
          fin_cases i <;> simp at coordinate ⊢ <;> omega
        rcases alternatives with unit | zero
        · simp [TilingLattice, unit]
        · have positive := Cᵢ.2
          omega
      · rcases root with ⟨z, rfl⟩
        have alternatives : Cᵢ.1.1.1 = 1 ∨ Cᵢ.1.1.1 = 0 := by
          have coordinate := congrArg (fun x => x.1) hCᵢ
          fin_cases i <;> simp at coordinate ⊢ <;> omega
        rcases alternatives with unit | zero
        · simp [TilingLattice, unit]
        · have positive := Cᵢ.2
          omega
      · have previousProper : ProperBandQuadruple predecessor := previous
        have childRelation : ∀ a b : CircleCoordinates, BandTangency a b →
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 b a = BandVectors.1 a b ∨
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 b a = -BandVectors.1 a b := by
          intro a b tangent
          have orientations := (PrimitiveVectorOrientationUnique a b).2 tangent
          rcases orientations with ⟨_, xor⟩
          unfold Xor at xor
          rcases xor with ⟨forward, _⟩ | ⟨backward, _⟩
          · rw [(flipLaw _ _ forward).1]
            right
            norm_num [Zsqrtd.ext_iff]
          · rw [(flipLaw _ _ backward).1]
            left
            norm_num [Zsqrtd.ext_iff]
        fin_cases i
        · have rootEquality : predecessor 0 = Cᵢ.1.1 := by simpa using hCᵢ
          by_cases unit : Cᵢ.1.1.1 = 1
          · simp [TilingLattice, unit]
          · unfold TilingLattice
            simp only [unit, ↓reduceIte]
            constructor
            · exact AddSubgroup.subset_closure ⟨predecessor, semi, rootEquality,
                by simpa [rootEquality] using previousProper.2, ⟨1, by simp⟩⟩
            · exact AddSubgroup.subset_closure ⟨predecessor, semi, rootEquality,
                by simpa [rootEquality] using previousProper.2, ⟨2, by simp⟩⟩
        · have hfirst := ih previousProper ⟨1, by decide⟩ Cᵢ (by simpa using hCᵢ)
          have step := (stepLaw predecessor semi).1
          have rootFlip := flipLaw _ _ (PrimitiveVectorOrientation.parentChild previousProper 1)
          have rootFlip' : BandVectors.1 (predecessor 0) (predecessor 2) =
              (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (predecessor 2) (predecessor 0) := by
            simpa using rootFlip.1
          have rel := childRelation (predecessor 1) (predecessor 2)
            ⟨predecessor, semi, 1, 2, by decide, rfl, rfl⟩
          have target : BandVectors.1 (predecessor 0) (predecessor 2) =
              BandVectors.1 (predecessor 3) (predecessor 2) +
                (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (predecessor 2) (predecessor 1) := by
            rw [rootFlip', step, mul_sub]
            norm_num [Zsqrtd.ext_iff]
            constructor <;> ring
          refine ⟨hfirst.1, ?_⟩
          change BandVectors.1 (predecessor 0) (predecessor 2) ∈ TilingLattice Cᵢ
          rw [target]
          rcases rel with rel | rel
          · rw [rel]
            exact (TilingLattice Cᵢ).add_mem hfirst.1 hfirst.2
          · rw [rel]
            exact (TilingLattice Cᵢ).sub_mem hfirst.1 hfirst.2
        · have hfirst := ih previousProper ⟨2, by decide⟩ Cᵢ (by simpa using hCᵢ)
          have step := (stepLaw predecessor semi).2.1
          have rel := childRelation (predecessor 2) (predecessor 3)
            ⟨predecessor, semi, 2, 3, by decide, rfl, rfl⟩
          have target : BandVectors.1 (predecessor 0) (predecessor 3) =
              BandVectors.1 (predecessor 1) (predecessor 3) +
                (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (predecessor 3) (predecessor 2) := by
            simpa using step
          refine ⟨?_, hfirst.2⟩
          change BandVectors.1 (predecessor 0) (predecessor 3) ∈ TilingLattice Cᵢ
          rw [target]
          rcases rel with rel | rel
          · rw [rel]
            exact (TilingLattice Cᵢ).add_mem hfirst.1 hfirst.2
          · rw [rel]
            exact (TilingLattice Cᵢ).sub_mem hfirst.1 hfirst.2

end ApollonianSuperharmonic

end
