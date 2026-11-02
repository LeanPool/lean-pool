/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.Hooley
public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem
public import Mathlib.Algebra.Order.Floor.Semifield

/-! # Divisor-sum rearrangement for Corollary 5

The difference of two floors counts multiples in the short interval. Swapping
the divisor and interval sums gives a sum of divisor-window counts, bounded
by Hooley's function. The estimate is uniform in the dyadic divisor cutoff.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem interval_multiples_card (a b d : ℕ) (hab : a ≤ b) :
    ((Ioc a b).filter (fun n => d ∣ n)).card = b / d - a / d := by
  have H : (Ioc a b).filter (fun n => d ∣ n) =
      ((Ioc 0 b).filter (fun n => d ∣ n)) \ ((Ioc 0 a).filter (fun n => d ∣ n)) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_sdiff]
    omega
  rw [H, card_sdiff_of_subset, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]
  intro n hn
  obtain ⟨hnI, hnd⟩ := mem_filter.mp hn
  obtain ⟨hn₀, hna⟩ := mem_Ioc.mp hnI
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn₀, hna.trans hab⟩, hnd⟩

/-- Floor differences count the positive multiples in a real interval,
including when an endpoint is an integer. -/
theorem shortInterval_multiples_card {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (d : ℕ) :
    (((shortInterval x y).filter (fun n => d ∣ n)).card : ℝ) =
      (⌊(x + y) / d⌋ : ℤ) - (⌊x / d⌋ : ℤ) := by
  rw [shortInterval, interval_multiples_card _ _ _ (Nat.floor_mono (by linarith)),
    ← Nat.floor_div_natCast, ← Nat.floor_div_natCast]
  rw [Nat.cast_sub (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg d)))]
  rw [natCast_floor_eq_intCast_floor (div_nonneg (by linarith) (Nat.cast_nonneg d)),
    natCast_floor_eq_intCast_floor (div_nonneg hx (Nat.cast_nonneg d))]

/-- Double counting a finite divisibility relation. -/
theorem sum_multiples_card_eq_sum_divisors_card (S T : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) :
    ∑ d ∈ T, (S.filter (fun n => d ∣ n)).card =
      ∑ n ∈ S, (n.divisors.filter (fun d => d ∈ T)).card := by
  classical
  calc
    _ = ∑ n ∈ S, (T.filter (fun d => d ∣ n)).card := by
      simp_rw [card_eq_sum_ones, sum_filter]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      congr 1
      ext d
      simp [Nat.mem_divisors, hS n hn, and_comm]

/-- The expression on the left of Corollary 5. -/
noncomputable def dyadicFloorSum (D x y : ℝ) : ℝ :=
  ∑ d ∈ shortInterval D D,
    (((⌊(x + y) / d⌋ : ℤ) : ℝ) - ((⌊x / d⌋ : ℤ) : ℝ))

theorem dyadicFloorSum_eq_divisor_sum {D x y : ℝ}
    (hD : 0 < D) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    dyadicFloorSum D x y = ∑ n ∈ shortInterval x y,
      ((n.divisors.filter (fun d : ℕ => D < d ∧ (d : ℝ) ≤ 2 * D)).card : ℝ) := by
  classical
  have H := sum_multiples_card_eq_sum_divisors_card (shortInterval x y) (shortInterval D D)
    (fun n hn => by have := (mem_Ioc.mp hn).1; omega)
  unfold dyadicFloorSum
  simp_rw [← shortInterval_multiples_card hx hy]
  rw [← Nat.cast_sum, H, Nat.cast_sum]
  apply sum_congr rfl
  intro n hn
  congr 2
  ext d
  simp only [mem_filter, shortInterval, mem_Ioc]
  rw [Nat.floor_lt hD.le, Nat.le_floor_iff (by linarith : 0 ≤ D + D)]
  rw [show D + D = 2 * D by ring]

/-- The uniform reduction used in Corollary 5, without any asymptotic
or unproved mean-value input. -/
theorem dyadicFloorSum_le_hooley_sum {D x y : ℝ}
    (hD : 0 < D) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    dyadicFloorSum D x y ≤ ∑ n ∈ shortInterval x y, (hooleyDelta n : ℝ) := by
  rw [dyadicFloorSum_eq_divisor_sum hD hx hy]
  exact sum_le_sum fun n _ => by exact_mod_cast dyadic_divisors_le_delta (n := n) hD

end NairTenenbaum
