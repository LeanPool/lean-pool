/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeLogSums

/-! # Bounded prime mass on logarithmic intervals

Chebyshev's elementary upper bound gives a uniform bound for
`Σ (log p)/p` on every interval of logarithmic length two. This controls
sampling the Hooley windows at prime logarithms.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem prime_log_mass_exp_interval (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (L : ℝ) :
    (∑ p ∈ S.filter (fun p : ℕ => Real.exp L ≤ p ∧ (p : ℝ) ≤ Real.exp (L + 2)),
      Real.log p / p) ≤ Real.log 4 * Real.exp 2 := by
  let T := S.filter (fun p : ℕ => Real.exp L ≤ p ∧ (p : ℝ) ≤ Real.exp (L + 2))
  have hprime (p : ℕ) (hp : p ∈ T) : p.Prime := hS p (mem_filter.mp hp).1
  have hsub : T ⊆ (Icc 0 ⌊Real.exp (L + 2)⌋₊).filter Nat.Prime := by
    intro p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,
      (Nat.le_floor_iff (Real.exp_pos _).le).mpr (mem_filter.mp hp).2.2⟩, hprime p hp⟩
  have hsum : (∑ p ∈ T, Real.log p) ≤ Chebyshev.theta (Real.exp (L + 2)) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
  calc
    _ ≤ ∑ p ∈ T, Real.log p / Real.exp L := by
      apply sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_left
        (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le)) (Real.exp_pos L)
      exact (mem_filter.mp hp).2.1
    _ = (∑ p ∈ T, Real.log p) / Real.exp L := (sum_div _ _ _).symm
    _ ≤ Chebyshev.theta (Real.exp (L + 2)) / Real.exp L :=
      div_le_div_of_nonneg_right hsum (Real.exp_pos L).le
    _ ≤ (Real.log 4 * Real.exp (L + 2)) / Real.exp L :=
      div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Real.exp_pos _).le) (Real.exp_pos
          L).le
    _ = Real.log 4 * Real.exp 2 := by rw [Real.exp_add]; field_simp

theorem prime_log_mass_log_interval (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (L : ℝ) :
    (∑ p ∈ S.filter (fun p : ℕ => L ≤ Real.log p ∧ Real.log p ≤ L + 2),
      Real.log p / p) ≤ Real.log 4 * Real.exp 2 := by
  have Heq : S.filter (fun p : ℕ => L ≤ Real.log p ∧ Real.log p ≤ L + 2) =
      S.filter (fun p : ℕ => Real.exp L ≤ p ∧ (p : ℝ) ≤ Real.exp (L + 2)) := by
    apply filter_congr
    intro p hp
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    rw [Real.le_log_iff_exp_le hp₀, Real.log_le_iff_le_exp hp₀]
  rw [Heq]
  exact prime_log_mass_exp_interval S hS L

end NairTenenbaum
