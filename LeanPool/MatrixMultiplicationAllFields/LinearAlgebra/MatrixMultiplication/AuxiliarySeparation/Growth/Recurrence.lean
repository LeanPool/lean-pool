/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Product

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The scalar simultaneous induction in Section 6

The two diagonal inequalities imply, simultaneously, lower bounds for the
limiting row slopes and for the diagonal profile.  All profile properties
needed for this argument are expressed as hypotheses below.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

/-- One step of the Section 6 simultaneous induction, with a positive real
index. The proof uses the diagonal increment inequality to obtain the second
conclusion as well as the first. -/
theorem growthRecurrence_step_real
    {n Dprev Dnext gprev gnext Gprev : ℝ} (hn : 0 < n)
    (hupper : Dnext ≤ ((3 * (n + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * n - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * n)) * Gprev ≤ gnext ∧
      ((3 * (n + 1) - 1) / 2) * ((1 + 1 / (3 * n)) * Gprev) ≤ Dnext := by
  have hden : 0 < 3 * n := by positivity
  have hbound : (3 * n + 1) * Gprev ≤ (3 * n) * gnext := by
    nlinarith
  have hidentity : (1 + 1 / (3 * n)) * Gprev =
      ((3 * n + 1) * Gprev) / (3 * n) := by
    field_simp
  have hgnew : (1 + 1 / (3 * n)) * Gprev ≤ gnext := by
    rw [hidentity]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hbound)
  refine ⟨hgnew, ?_⟩
  have hdiagonal : ((3 * (n + 1) - 1) / 2) *
      ((1 + 1 / (3 * n)) * Gprev) =
      ((3 * n - 1) / 2) * Gprev + Gprev +
        (1 + 1 / (3 * n)) * Gprev := by
    field_simp
    ring
  rw [hdiagonal]
  linarith

/-- The natural-number form of the scalar induction step, indexed by `n + 1`
so that no truncated subtraction occurs in the recurrence. -/
theorem growthRecurrence_step
    {n : ℕ} (hn : 1 ≤ n) {Dprev Dnext gprev gnext Gprev : ℝ}
    (hupper : Dnext ≤ ((3 * ((n : ℝ) + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * (n : ℝ) - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * (n : ℝ))) * Gprev ≤ gnext ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) *
        ((1 + 1 / (3 * (n : ℝ))) * Gprev) ≤ Dnext := by
  apply growthRecurrence_step_real
  · exact_mod_cast (show 0 < n by omega)
  · exact hupper
  · exact hincrement
  · exact hgprev
  · exact hDprev

/-- The simultaneous slope and diagonal estimates, conditional only on the
initial values, the recurrence for `G`, and the two diagonal inequalities. -/
theorem growthRecurrence_induction
    (D g G : ℕ → ℝ)
    (hGbase : G 1 = 1)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hGstep : ∀ n : ℕ, 1 ≤ n →
      G (n + 1) = (1 + 1 / (3 * (n : ℝ))) * G n)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → G n ≤ g n ∧ ((3 * (n : ℝ) - 1) / 2) * G n ≤ D n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [hGbase]
      exact ⟨hgbase, hDbase⟩
  | succ n hn ih =>
      have hu : D (n + 1) ≤
          ((3 * ((n : ℝ) + 1) - 1) / 2) * g (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hupper (n + 1) (by omega)
      have hs := growthRecurrence_step hn hu (hincrement n hn) ih.1 ih.2
      simpa only [hGstep n hn, Nat.cast_add, Nat.cast_one] using hs

/-- A zero-indexed version of `growthRecurrence_induction`, convenient when the
initial term of the comparison sequence is stored at index zero. -/
theorem growthRecurrence_induction_shifted
    (D g H : ℕ → ℝ)
    (hHbase : H 0 = 1)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hHstep : ∀ n : ℕ,
      H (n + 1) = (1 + 1 / (3 * ((n : ℝ) + 1))) * H n)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, H n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * H n ≤ D (n + 1) := by
  intro n
  induction n with
  | zero =>
      norm_num [hHbase]
      exact ⟨hgbase, hDbase⟩
  | succ n ih =>
      have hn : 1 ≤ n + 1 := by omega
      have hu : D (n + 1 + 1) ≤
          ((3 * (((n + 1 : ℕ) : ℝ) + 1) - 1) / 2) * g (n + 1 + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hupper (n + 1 + 1) (by omega)
      have hp : ((3 * ((n + 1 : ℕ) : ℝ) - 1) / 2) * H n ≤ D (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      have hs := growthRecurrence_step hn hu (hincrement (n + 1) hn) ih.1 hp
      simpa only [hHstep, Nat.cast_add, Nat.cast_one] using hs

/-- The simultaneous bounds for the explicit comparison product from Section 6. -/
theorem growthProduct_le_slope_and_diagonal
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, growthProduct n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * growthProduct n ≤ D (n + 1) := by
  apply growthRecurrence_induction_shifted D g growthProduct
    growthProduct_zero hgbase hDbase
  · intro n
    rw [growthProduct_succ, mul_comm]
  · exact hupper
  · exact hincrement

/-- Combining the scalar induction with the elementary product estimate gives
an exact fourth-power lower bound on the cube of each diagonal value. -/
theorem diagonal_fourth_power_lower
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ D (n + 1) ^ 3 := by
  have hdiag := (growthProduct_le_slope_and_diagonal D g hgbase hDbase
    hupper hincrement n).2
  have hpositive := growthProduct_pos n
  have hlinear : ((n : ℝ) + 1) * growthProduct n ≤ D (n + 1) := by
    have hcoeff : (n : ℝ) + 1 ≤ (3 * ((n : ℝ) + 1) - 1) / 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hpositive)).trans hdiag
  calc
    ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) := by ring
    _ ≤ ((n : ℝ) + 1) ^ 3 * growthProduct n ^ 3 :=
      mul_le_mul_of_nonneg_left (growthProduct_cube_lower n) (by positivity)
    _ = (((n : ℝ) + 1) * growthProduct n) ^ 3 := by ring
    _ ≤ D (n + 1) ^ 3 := pow_le_pow_left₀ (by positivity) hlinear 3

/-- The diagonal fourth-power lower bound using the paper's positive indices. -/
theorem diagonal_fourth_power_lower_of_one_le
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ 4 ≤ D n ^ 3 := by
  cases n with
  | zero => omega
  | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        diagonal_fourth_power_lower D g hgbase hDbase hupper hincrement n

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
