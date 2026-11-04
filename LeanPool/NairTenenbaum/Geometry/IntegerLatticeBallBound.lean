/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
import Mathlib.Tactic.Positivity

/-! # Uniform bounds for integer lattice points in balls

The ambient norm on a finite product of real lines is the supremum norm.
Each coordinate lies in an integer interval of uniformly bounded length.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem card_integer_interval_le {a b R : ℝ} (_hR : 0 ≤ R) (hab : b - a ≤ R) :
    (Icc ⌈a⌉ ⌊b⌋).card ≤ ⌈R⌉₊ + 1 := by
  rw [Int.card_Icc]
  apply Int.toNat_le.mpr
  have hlo := Int.le_ceil a
  have hhi := Int.floor_le b
  have hceil := Nat.le_ceil R
  have H : (⌊b⌋ : ℝ) + 1 - ⌈a⌉ ≤ (⌈R⌉₊ : ℝ) + 1 := by linarith
  exact_mod_cast H

variable {ι : Type*} [Fintype ι]

/-- The ambient real point associated with integer lattice coordinates. -/
noncomputable def integerLatticePoint (m : ι → ℤ) : ι → ℝ := fun i => m i

theorem card_integerLattice_ball_le (S : Finset (ι → ℤ)) (c : ι → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hS : ∀ m ∈ S, dist (integerLatticePoint m) c ≤ R) :
    S.card ≤ (⌈2 * R⌉₊ + 1) ^ Fintype.card ι := by
  classical
  let B := Fintype.piFinset (fun i : ι => Icc ⌈c i - R⌉ ⌊c i + R⌋)
  have hsub : S ⊆ B := by
    intro m hm
    apply Fintype.mem_piFinset.mpr
    intro i
    have H := (dist_pi_le_iff hR).mp (hS m hm) i
    change dist (m i : ℝ) (c i) ≤ R at H
    rw [Real.dist_eq, abs_le] at H
    apply mem_Icc.mpr
    exact ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩
  calc
    S.card ≤ B.card := card_le_card hsub
    _ = ∏ i : ι, (Icc ⌈c i - R⌉ ⌊c i + R⌋).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : ι, (⌈2 * R⌉₊ + 1) := by
      apply prod_le_prod
      intro i _
      exact card_integer_interval_le (by positivity) (by linarith)
    _ = _ := by simp

theorem card_integerLattice_near_cover_le (A : Finset (ι → ℤ)) (S : Finset (ι → ℝ))
    {R : ℝ} (hR : 0 ≤ R)
    (hcover : ∀ m ∈ A, ∃ c ∈ S, dist (integerLatticePoint m) c ≤ R) :
    A.card ≤ S.card * (⌈2 * R⌉₊ + 1) ^ Fintype.card ι := by
  classical
  have hsub : A ⊆ S.biUnion (fun c => A.filter (fun m => dist (integerLatticePoint m) c ≤ R)) := by
    intro m hm
    obtain ⟨c, hc, hdist⟩ := hcover m hm
    exact mem_biUnion.mpr ⟨c, hc, mem_filter.mpr ⟨hm, hdist⟩⟩
  calc
    _ ≤ (S.biUnion (fun c => A.filter (fun m => dist (integerLatticePoint m) c ≤ R))).card :=
      card_le_card hsub
    _ ≤ ∑ c ∈ S, (A.filter (fun m => dist (integerLatticePoint m) c ≤ R)).card := card_biUnion_le
    _ ≤ ∑ _c ∈ S, (⌈2 * R⌉₊ + 1) ^ Fintype.card ι := by
      apply sum_le_sum
      intro c _
      exact card_integerLattice_ball_le _ c hR (fun m hm => (mem_filter.mp hm).2)
    _ = _ := by simp

end NairTenenbaum
