/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondCellDomain
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

-- [TABLET NODE: P4194T1DiamondCellRows]

/-!
# P4194T1DiamondCellRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4194T1DiamondCellRows (m : Nat) (z : GaussianInt) :
    (z ∈ DiamondCellDomain m ↔
      0 ≤ z.im ∧ z.im < 2 * (m : Int) ∧
      -(z.im + 1) ≤ z.re ∧ z.re < z.im + 1 ∧
      -(2 * (m : Int) - z.im) ≤ z.re ∧ z.re < 2 * (m : Int) - z.im) ∧
    ((∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain m) ↔
      1 ≤ z.im ∧ z.im ≤ 2 * (m : Int) - 1 ∧
      -(z.im - 1) ≤ z.re ∧ z.re ≤ z.im - 1 ∧
      -(2 * (m : Int) - z.im - 1) ≤ z.re ∧
        z.re ≤ 2 * (m : Int) - z.im - 1) := by
-- BODY
  classical
  have cell_iff (w : GaussianInt) : w ∈ DiamondCellDomain m ↔
      0 ≤ w.im ∧ w.im < 2 * (m : Int) ∧
      -(w.im + 1) ≤ w.re ∧ w.re < w.im + 1 ∧
      -(2 * (m : Int) - w.im) ≤ w.re ∧ w.re < 2 * (m : Int) - w.im := by
    constructor
    · intro hz
      simp only [DiamondCellDomain, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image] at hz
      obtain ⟨b, hb, j, hj, heq⟩ := hz
      have hre : (j : Int) - (min (b + 1) (2 * m - b) : Nat) = w.re := by
        simpa using congrArg Zsqrtd.re heq
      have him : (b : Int) = w.im := by
        simpa using congrArg Zsqrtd.im heq
      have hjI : (j : Int) < 2 * (min (b + 1) (2 * m - b) : Nat) := by
        exact_mod_cast hj
      have hmin1I : ((min (b + 1) (2 * m - b) : Nat) : Int) ≤ (b : Int) + 1 := by
        exact_mod_cast (Nat.min_le_left (b + 1) (2 * m - b))
      have hmin2I : ((min (b + 1) (2 * m - b) : Nat) : Int) ≤
          ((2 * m - b : Nat) : Int) := by
        exact_mod_cast (Nat.min_le_right (b + 1) (2 * m - b))
      have hsubcast : ((2 * m - b : Nat) : Int) = 2 * (m : Int) - b := by omega
      omega
    · rintro ⟨hb0, hb, hlo1, hhi1, hlo2, hhi2⟩
      let b := w.im.toNat
      have hbc : (b : Int) = w.im := Int.toNat_of_nonneg hb0
      have hbn : b < 2 * m := by omega
      let r := min (b + 1) (2 * m - b)
      have hrc : (r : Int) = min (w.im + 1) (2 * (m : Int) - w.im) := by
        dsimp [r]
        rw [Nat.cast_min]
        congr 1 <;> omega
      have hrlo : -(r : Int) ≤ w.re := by omega
      have hrhi : w.re < (r : Int) := by omega
      let j := (w.re + r).toNat
      have hjc : (j : Int) = w.re + r := Int.toNat_of_nonneg (by omega)
      have hj : j < 2 * r := by omega
      simp only [DiamondCellDomain, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image]
      refine ⟨b, hbn, j, hj, ?_⟩
      apply Zsqrtd.ext
      · change (j : Int) - (r : Int) = w.re
        omega
      · exact hbc
  refine ⟨cell_iff z, ?_⟩
  have four : (∀ j : Fin 4, LatticeVertexIncidentCell z j ∈ DiamondCellDomain m) ↔
      z ∈ DiamondCellDomain m ∧ z - 1 ∈ DiamondCellDomain m ∧
      z - 1 - ⟨0, 1⟩ ∈ DiamondCellDomain m ∧ z - ⟨0, 1⟩ ∈ DiamondCellDomain m := by
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2, h 3⟩
    · rintro ⟨h0, h1, h2, h3⟩ j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact h3
  rw [four]
  simp only [cell_iff]
  norm_num
  omega

end ApollonianSuperharmonic

end
