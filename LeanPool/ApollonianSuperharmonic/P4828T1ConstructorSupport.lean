/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1RotationLaws
public import LeanPool.ApollonianSuperharmonic.P4828T1Step
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import Mathlib.Tactic.LinearCombination

-- [TABLET NODE: P4828T1ConstructorSupport]

/-!
# P4828T1ConstructorSupport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4828T1ConstructorSupport (L : Real)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q) (b : Fin 3) :
    ProperBandQuadruple (P4828T1Step (P4828T1Rotate q b)) ∧
      P4828T1LineSupport L (P4828T1Step (P4828T1Rotate q b)) := by
-- BODY
  let t := P4828T1Rotate q b
  have ht : ProperBandQuadruple t := P4828T1RotationLaws.2.2 q b hq
  let idx : Fin 4 → Fin 4 := Fin.cases 0 (fun j => (j + b).succ)
  have hidx : ∀ k, t k = q (idx k) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k <;> rfl
  have hsign : P4828T1LineSupport L t := by
    constructor
    · intro k hk
      simpa only [hidx] using hs.normals (idx k) (by simpa only [hidx] using hk)
    · intro k j hk hj
      simpa only [hidx] using hs.signed (idx k) (idx j)
        (by simpa only [hidx] using hk) (by simpa only [hidx] using hj)
  have facts := ProperBandCurvatureStructure t ht
  have p0 := facts.1
  have n0 := (SemiProperForestClassification t ht.1).1 (0 : Fin 4)
  have n1 := facts.2.1 (0 : Fin 3)
  have n2 := facts.2.1 (1 : Fin 3)
  have n3 := facts.2.1 (2 : Fin 3)
  have lt1 := ht.2 (0 : Fin 3)
  have lt2 := ht.2 (1 : Fin 3)
  have lt3 := ht.2 (2 : Fin 3)
  change (t 1).1 < (t 0).1 at lt1
  change (t 2).1 < (t 0).1 at lt2
  change (t 3).1 < (t 0).1 at lt3
  change 0 ≤ (t 1).1 at n1
  change 0 ≤ (t 2).1 at n2
  change 0 ≤ (t 3).1 at n3
  have dpos : 0 < (P4828T1Step t 0).1 := by
    dsimp [P4828T1Step]
    omega
  have proper : ProperBandQuadruple (P4828T1Step t) := by
    refine ⟨SemiProperQuadruple.successor ht.1, ?_⟩
    intro j
    fin_cases j <;> dsimp [P4828T1Step] <;> omega
  refine ⟨proper, ?_⟩
  change P4828T1LineSupport L (P4828T1Step t)
  constructor
  · intro k hk
    fin_cases k
    · exact (ne_of_gt dpos hk).elim
    · exact (ne_of_gt p0 hk).elim
    · exact hsign.normals 2 hk
    · exact hsign.normals 3 hk
  · intro k j hk hj
    fin_cases k
    · exact (ne_of_gt dpos hk).elim
    · exact (ne_of_gt p0 hk).elim
    · have hk' : (t 2).1 = 0 := hk
      have p1 : 0 < (t 1).1 := by
        have ne : (t 1).1 ≠ 0 := by
          intro hz
          have bad := facts.2.2 0 1 hz hk'
          exact (by decide : (0 : Fin 3) ≠ 1) bad
        omega
      have p3 : 0 < (t 3).1 := by
        have ne : (t 3).1 ≠ 0 := by
          intro hz
          have bad := facts.2.2 2 1 hz hk'
          exact (by decide : (2 : Fin 3) ≠ 1) bad
        omega
      fin_cases j
      · have h0 := hsign.signed 2 0 hk' p0
        have h1 := hsign.signed 2 1 hk' p1
        have h3 := hsign.signed 2 3 hk' p3
        rcases hsign.normals 2 hk' with hn | hn
        all_goals norm_num [P4828T1Step, hn, hk'] at h0 h1 h3 ⊢
        all_goals linear_combination 2 * h0 - h1 + 2 * h3
      · exact hsign.signed 2 0 hk' hj
      · exact hsign.signed 2 2 hk' hj
      · exact hsign.signed 2 3 hk' hj
    · have hk' : (t 3).1 = 0 := hk
      have p1 : 0 < (t 1).1 := by
        have ne : (t 1).1 ≠ 0 := by
          intro hz
          have bad := facts.2.2 0 2 hz hk'
          exact (by decide : (0 : Fin 3) ≠ 2) bad
        omega
      have p2 : 0 < (t 2).1 := by
        have ne : (t 2).1 ≠ 0 := by
          intro hz
          have bad := facts.2.2 1 2 hz hk'
          exact (by decide : (1 : Fin 3) ≠ 2) bad
        omega
      fin_cases j
      · have h0 := hsign.signed 3 0 hk' p0
        have h1 := hsign.signed 3 1 hk' p1
        have h2 := hsign.signed 3 2 hk' p2
        rcases hsign.normals 3 hk' with hn | hn
        all_goals norm_num [P4828T1Step, hn, hk'] at h0 h1 h2 ⊢
        all_goals linear_combination 2 * h0 - h1 + 2 * h2
      · exact hsign.signed 3 0 hk' hj
      · exact hsign.signed 3 2 hk' hj
      · exact hsign.signed 3 3 hk' hj

end ApollonianSuperharmonic

end
