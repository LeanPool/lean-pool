/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.Hooley
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-! # Absorbing a fixed factor in Hooley's function

The upper multiplication bound holds without a coprimality hypothesis;
divisor products can overlap, so the corresponding window formula is an inequality.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem divisorWindow_mul_le (m n : ℕ) (u : ℝ) :
    divisorWindow (m * n) u ≤ ∑ a ∈ m.divisors, divisorWindow n (u - log a) := by
  classical
  by_cases hzero : m * n = 0
  · simp only [hzero, divisorWindow, Nat.divisors_zero, filter_empty, card_empty]
    exact Nat.zero_le _
  have hm : m ≠ 0 := left_ne_zero_of_mul hzero
  have hn : n ≠ 0 := right_ne_zero_of_mul hzero
  let T (a : ℕ) := n.divisors.filter (fun b : ℕ => u - log a < log b ∧ log b ≤ u - log a + 1)
  have H : (m * n).divisors.filter (fun d : ℕ => u < log d ∧ log d ≤ u + 1) ⊆
      m.divisors.biUnion (fun a => (T a).image (fun b => a * b)) := by
    intro d hd
    obtain ⟨hd, hlow, hhigh⟩ := mem_filter.mp hd
    obtain ⟨a, b, ha, hb, hab⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hd)
    have ha₀ : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_zero_of_dvd_ne_zero hm ha)
    have hb₀ : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_zero_of_dvd_ne_zero hn hb)
    apply mem_biUnion.mpr
    refine ⟨a, Nat.mem_divisors.mpr ⟨ha, hm⟩, mem_image.mpr ⟨b, ?_, hab.symm⟩⟩
    apply mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hb, hn⟩, ?_, ?_⟩
    all_goals rw [hab, Nat.cast_mul, Real.log_mul ha₀ hb₀] at hlow hhigh; linarith
  calc
    _ ≤ (m.divisors.biUnion (fun a => (T a).image (fun b => a * b))).card := card_le_card H
    _ ≤ ∑ a ∈ m.divisors, ((T a).image (fun b => a * b)).card := card_biUnion_le
    _ ≤ ∑ a ∈ m.divisors, (T a).card := sum_le_sum (fun _ _ => card_image_le)
    _ = _ := rfl

theorem hooleyDelta_mul_le_without_coprime (m n : ℕ) :
    hooleyDelta (m * n) ≤ m.divisors.card * hooleyDelta n := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  apply (divisorWindow_mul_le m n u).trans
  calc
    _ ≤ ∑ _a ∈ m.divisors, hooleyDelta n := sum_le_sum (fun _ _ => divisorWindow_le_delta n _)
    _ = _ := by simp

end NairTenenbaum
