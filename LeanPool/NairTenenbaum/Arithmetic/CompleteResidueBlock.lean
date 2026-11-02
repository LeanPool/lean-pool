/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.CongruenceCount
public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem
public import Mathlib.Data.Int.Star

/-! # Complete residue blocks inside real short intervals -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem residue_count_complete_block (a v : ℕ) {q : ℕ} (hq : 0 < q) :
    ((Ioc a (a + q)).filter (fun n => Nat.ModEq q n v)).card = 1 := by
  have H := Nat.Ioc_filter_modEq_card a (a + q) hq v
  have hq₀ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have HE : (((a + q : ℕ) : ℚ) - v) / q = ((a : ℚ) - v) / q + 1 := by
    push_cast
    field_simp
    ring
  rw [HE, Int.floor_add_one] at H
  norm_num at H
  exact_mod_cast H

theorem polynomial_count_complete_block (Q : ℤ[X]) (a : ℕ) {q : ℕ} (hq : 0 < q) :
    ((Ioc a (a + q)).filter (fun n : ℕ => q ∣ (Q.eval (n : ℤ)).natAbs)).card = rootCount Q q := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have H := sum_card_fiberwise_eq_card_filter (Ioc a (a + q)) (residueRootSet Q q)
    (fun n : ℕ => (n : ZMod q))
  have Hmem (n : ℕ) : (n : ZMod q) ∈ residueRootSet Q q ↔ q ∣ (Q.eval (n : ℤ)).natAbs := by
    simpa only [Int.cast_natCast, Int.natCast_dvd] using cast_mem_residueRootSet Q q (n : ℤ)
  simp_rw [Hmem] at H
  rw [← H]
  calc
    _ = ∑ _r ∈ residueRootSet Q q, (1 : ℕ) := by
      apply sum_congr rfl
      intro r _
      have HE : ((Ioc a (a + q)).filter (fun n : ℕ => (n : ZMod q) = r)) =
          (Ioc a (a + q)).filter (fun n => Nat.ModEq q n r.val) := by
        apply filter_congr
        intro n _
        simpa only [ZMod.natCast_zmod_val] using ZMod.natCast_eq_natCast_iff n r.val q
      rw [HE, residue_count_complete_block a r.val hq]
    _ = _ := by simp [residueRootSet_card]

theorem shortInterval_polynomial_congruence_count_ge (Q : ℤ[X]) {x y : ℝ}
    (hx : 0 ≤ x) {q : ℕ} (hq : 0 < q) (hqy : (q : ℝ) ≤ y) :
    rootCount Q q ≤ ((shortInterval x y).filter (fun n : ℕ => q ∣ (Q.eval (n : ℤ)).natAbs)).card
        := by
  rw [← polynomial_count_complete_block Q ⌊x⌋₊ hq]
  apply card_le_card
  intro n hn
  obtain ⟨hnI, hnQ⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hnI).1, ?_⟩, hnQ⟩
  have hy : 0 ≤ y := (Nat.cast_nonneg q).trans hqy
  apply (mem_Ioc.mp hnI).2.trans
  apply (Nat.le_floor_iff (add_nonneg hx hy)).mpr
  have H := Nat.floor_le hx
  push_cast
  linarith

end NairTenenbaum
