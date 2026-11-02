/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.SieveCutoffComparison

/-! # Decay after paying the arithmetic and Euler-product costs -/

@[expose] public section

namespace NairTenenbaum

/-- A margin `v` in the smooth-tail moment leaves decay `exp(-v / α)` after
paying for the rough remainder and restoring the Euler product. -/
theorem primeBand_decay_of_margin {A c κ τ α x v : ℝ} {g : ℕ}
    (hA : 0 < A) (hα : 0 < α) (hx : 1 < x)
    (hκ : c * Real.log A + 4 * (g : ℝ) * Real.log 4 + v ≤ κ * τ / 2) :
    A ^ (c / α) * Real.exp (4 * (g : ℝ) * Real.log 4 / α) *
        Real.exp (-κ * Real.log (x ^ τ) / Real.log (x ^ (2 * α))) ≤
      Real.exp (-v / α) := by
  rw [Real.log_rpow (by linarith : 0 < x), Real.log_rpow (by linarith : 0 < x),
    Real.rpow_def_of_pos hA, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have heq : Real.log A * (c / α) + 4 * (g : ℝ) * Real.log 4 / α +
      -κ * (τ * Real.log x) / (2 * α * Real.log x) =
      (c * Real.log A + 4 * (g : ℝ) * Real.log 4 - κ * τ / 2) / α := by
    field_simp
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right (by linarith) hα.le

/-- For a band with upper cutoff `x^(2α)`, the smooth-tail moment can pay
both the rough remainder and the restoration of the Euler product. -/
theorem primeBand_decay {A c κ τ α x : ℝ} {g : ℕ}
    (hA : 0 < A) (hα : 0 < α) (hx : 1 < x)
    (hκ : c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 1 ≤ κ * τ / 2) :
    A ^ (c / α) * Real.exp (4 * (g : ℝ) * Real.log 4 / α) *
        Real.exp (-κ * Real.log (x ^ τ) / Real.log (x ^ (2 * α))) ≤
      Real.exp (-1 / α) := by
  exact primeBand_decay_of_margin hA hα hx hκ

/-- The dyadic logarithmic bands have a summable decay, uniformly in their
number. This deliberately uses the weaker geometric decay `exp(-j)`. -/
theorem dyadic_primeBand_decay {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (j : ℕ) :
    Real.exp (-1 / (a / 2 ^ (j + 1))) ≤ Real.exp (-1) ^ j := by
  have hj : (j : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    have H : j ≤ 2 ^ (j + 1) := by
      have : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
      omega
    exact_mod_cast H
  have H : (j : ℝ) ≤ 2 ^ (j + 1) / a :=
    (le_div_iff₀ ha).mpr ((mul_le_mul_of_nonneg_left ha₁ (Nat.cast_nonneg j)).trans (by
      simpa using hj))
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have heq : -1 / (a / 2 ^ (j + 1)) = -(2 ^ (j + 1) / a) := by
    rw [div_div_eq_mul_div]
    ring
  rw [heq]
  nlinarith

/-- Any finite collection of dyadic bands has a uniformly bounded total cost. -/
theorem sum_dyadic_primeBand_decay_le {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (J : Finset ℕ) :
    (∑ j ∈ J, Real.exp (-1 / (a / 2 ^ (j + 1)))) ≤ (1 - Real.exp (-1))⁻¹ := by
  have hq : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  calc
    _ ≤ ∑ j ∈ J, Real.exp (-1) ^ j := Finset.sum_le_sum (fun j _ => dyadic_primeBand_decay ha ha₁ j)
    _ ≤ ∑' j : ℕ, Real.exp (-1) ^ j := (summable_geometric_of_lt_one (Real.exp_nonneg _)
        hq).sum_le_tsum
      J (fun _ _ => pow_nonneg (Real.exp_nonneg _) _)
    _ = _ := tsum_geometric_of_lt_one (Real.exp_nonneg _) hq

/-- The doubled lower exponent of a dyadic band never exceeds its initial
upper exponent. -/
theorem dyadic_primeBand_exponent_le {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    2 * (a / 2 ^ (j + 1)) ≤ a := by
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have heq : 2 * (a / 2 ^ (j + 1)) = a / 2 ^ j := by
    rw [pow_succ]
    field_simp
  rw [heq]
  exact div_le_self ha hp

/-- Dyadic logarithmic intervals cover every positive exponent below the
initial cutoff, with a strict lower endpoint and a closed upper endpoint. -/
theorem exists_dyadic_exponent_band {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    ∃ j : ℕ, a / 2 ^ (j + 1) < b ∧ b ≤ 2 * (a / 2 ^ (j + 1)) := by
  have hex : ∃ n : ℕ, a / 2 ^ n < b := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a / b) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr ?_⟩
    nlinarith [(div_lt_iff₀ hb).mp hn]
  have hzero : Nat.find hex ≠ 0 := by
    intro h
    have H := Nat.find_spec hex
    rw [h] at H
    simp only [pow_zero, div_one] at H
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  refine ⟨j, by simpa only [hj, Nat.succ_eq_add_one] using Nat.find_spec hex, ?_⟩
  have H : b ≤ a / 2 ^ j := le_of_not_gt (Nat.find_min hex (by omega : j < Nat.find hex))
  have heq : 2 * (a / 2 ^ (j + 1)) = a / 2 ^ j := by
    rw [pow_succ]
    field_simp
  rwa [heq]

/-- Every prime cutoff between `1` and `x^a` belongs to a logarithmic band.
This is a statement for all real cutoffs, so it also covers ties at powers. -/
theorem exists_dyadic_primeBand {a x p : ℝ} (hx : 1 < x) (hp : 1 < p)
    (hpa : p ≤ x ^ a) :
    ∃ j : ℕ, x ^ (a / 2 ^ (j + 1)) < p ∧ p ≤ x ^ (2 * (a / 2 ^ (j + 1))) := by
  have hx₀ : 0 < x := by linarith
  have hp₀ : 0 < p := by linarith
  have hlx := Real.log_pos hx
  have hb : 0 < Real.log p / Real.log x := div_pos (Real.log_pos hp) hlx
  have hba : Real.log p / Real.log x ≤ a := by
    apply (div_le_iff₀ hlx).mpr
    simpa only [Real.log_rpow hx₀] using Real.log_le_log hp₀ hpa
  obtain ⟨j, hlo, hhi⟩ := exists_dyadic_exponent_band hb hba
  refine ⟨j, ?_, ?_⟩
  · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx₀ _) hp₀).mp
    rw [Real.log_rpow hx₀]
    exact (lt_div_iff₀ hlx).mp hlo
  · apply (Real.log_le_log_iff hp₀ (Real.rpow_pos_of_pos hx₀ _)).mp
    rw [Real.log_rpow hx₀]
    exact (div_le_iff₀ hlx).mp hhi

/-- Sum any nonnegative multiple of the common dyadic band decay. -/
theorem sum_le_dyadic_primeBand_bound {u C : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1)
    (J : Finset ℕ) (hC : 0 ≤ C) (f : ℕ → ℝ)
    (hf : ∀ j ∈ J, f j ≤ C * Real.exp (-1 / (u / 2 ^ (j + 1)))) :
    (∑ j ∈ J, f j) ≤ C * (1 - Real.exp (-1))⁻¹ := by
  calc
    _ ≤ ∑ j ∈ J, C * Real.exp (-1 / (u / 2 ^ (j + 1))) := Finset.sum_le_sum hf
    _ = C * ∑ j ∈ J, Real.exp (-1 / (u / 2 ^ (j + 1))) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_dyadic_primeBand_decay_le hu hu₁ J) hC

end NairTenenbaum
