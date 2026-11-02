/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ComparisonLocal
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Nat.Totient

/-! # The totient correction in the sieve estimate

The correction for omitted sieve factors is `(n/φ(n))^g`. This module proves
its multiplicativity, prime-power values, and the stronger weighted local
convergence needed to replace the invalid general Lemma 1.
-/

@[expose] public section

namespace NairTenenbaum

/-- The reciprocal-totient correction; the exponent is the polynomial degree. -/
noncomputable def totientTwist (g n : ℕ) : ℝ := ((n : ℝ) / n.totient) ^ g

@[simp] theorem totientTwist_one (g : ℕ) : totientTwist g 1 = 1 := by
  simp [totientTwist]

theorem totientTwist_nonneg (g n : ℕ) : 0 ≤ totientTwist g n := by
  unfold totientTwist
  positivity

theorem totientTwist_mul (g : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    totientTwist g (m * n) = totientTwist g m * totientTwist g n := by
  simp only [totientTwist, Nat.totient_mul hmn, Nat.cast_mul, mul_div_mul_comm, mul_pow]

theorem totientTwist_prime_pow (g : ℕ) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    totientTwist g (p ^ (ν + 1)) = ((p : ℝ) / ((p : ℝ) - 1)) ^ g := by
  have hp₀ : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [totientTwist, Nat.totient_prime_pow_succ hp]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one, pow_succ]
  rw [mul_div_mul_left _ _ (pow_ne_zero ν hp₀)]

theorem totientTwist_prime (g : ℕ) {p : ℕ} (hp : p.Prime) :
    totientTwist g p = ((p : ℝ) / ((p : ℝ) - 1)) ^ g := by
  simpa using totientTwist_prime_pow g hp 0

private theorem pow_sub_one_le {t : ℝ} (ht₁ : 1 ≤ t) (ht₂ : t ≤ 2) (g : ℕ) :
    t ^ g - 1 ≤ (t - 1) * ((2 : ℝ) ^ g - 1) := by
  induction g with
  | zero => simp
  | succ g ih =>
    have hnonneg : 0 ≤ t ^ g - 1 := sub_nonneg.mpr (one_le_pow₀ ht₁)
    calc
      t ^ (g + 1) - 1 = t * (t ^ g - 1) + (t - 1) := by rw [pow_succ]; ring
      _ ≤ 2 * ((t - 1) * ((2 : ℝ) ^ g - 1)) + (t - 1) :=
        add_le_add (mul_le_mul ht₂ ih hnonneg (by norm_num)) le_rfl
      _ = _ := by rw [pow_succ]; ring

/-- An explicit `O(1/p)` bound with a constant depending only on the degree. -/
theorem totientTwist_prime_sub_one_le (g : ℕ) {p : ℕ} (hp : p.Prime) :
    |totientTwist g p - 1| ≤ (2 * ((2 : ℝ) ^ g - 1)) / p := by
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp₀ : (0 : ℝ) < p := by linarith
  have hd : (0 : ℝ) < p - 1 := by linarith
  have ht₁ : 1 ≤ (p : ℝ) / (p - 1) := (le_div_iff₀ hd).mpr (by linarith)
  have ht₂ : (p : ℝ) / (p - 1) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
  have ht : (p : ℝ) / (p - 1) - 1 ≤ 2 / p := by
    apply (le_div_iff₀ hp₀).mpr
    have he : ((p : ℝ) / (p - 1) - 1) * p = (p : ℝ) / (p - 1) := by
      field_simp
      ring
    rw [he]
    exact ht₂
  rw [totientTwist_prime g hp, abs_of_nonneg (sub_nonneg.mpr (one_le_pow₀ ht₁))]
  calc
    _ ≤ ((p : ℝ) / (p - 1) - 1) * ((2 : ℝ) ^ g - 1) := pow_sub_one_le ht₁ ht₂ g
    _ ≤ (2 / p) * ((2 : ℝ) ^ g - 1) :=
      mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
    _ = _ := by ring

end NairTenenbaum
