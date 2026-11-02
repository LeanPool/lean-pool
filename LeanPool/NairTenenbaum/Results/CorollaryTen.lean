/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.DivisorSums.GoldbachScales

/-! # Corollary 10: Goldbach representations with one prime in a short interval -/

@[expose] public section

namespace NairTenenbaum

/-- Corollary 10, with the implicit constant quantified before `N,x,y`.
`goldbachCount` counts each choice of the first prime, as in the paper's sum. -/
def CorollaryTen : Prop :=
  ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 < N → ∀ (x y : ℝ),
      (N : ℝ) ^ δ < x → x ^ ε ≤ y → y ≤ x →
      (goldbachCount N x y : ℝ) ≤ C * (((N : ℝ) / N.totient) * y / (Real.log N) ^ 2)

theorem corollaryTen : CorollaryTen := by
  intro ε δ hε _ hδ _
  obtain ⟨C, hC, H⟩ := exists_goldbach_power_length_bound (mul_pos hδ hε)
  refine ⟨C, hC, ?_⟩
  intro N hN x y hx hy hyx
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx₀ : 0 ≤ x := (Real.rpow_nonneg hN₀.le δ).trans hx.le
  have hlength : (N : ℝ) ^ (δ * ε) ≤ y := by
    rw [Real.rpow_mul hN₀.le]
    exact (Real.rpow_le_rpow (Real.rpow_nonneg hN₀.le δ) hx.le hε.le).trans hy
  exact H N hN x y hx₀ hlength hyx

end NairTenenbaum
