/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Basic

/-!
# The scalar recurrence in Appendix A

The coefficients are defined recursively, rather than assumed to have a closed form.
The final theorem evaluates the sequence at every integral phase of the sine solution.
-/

@[expose] public section

namespace NoncommutativeAMGM

/-- The second-order coefficient recurrence for a distinct-index simplex product. -/
noncomputable def simplexRecurrence (a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | k + 2 => a * simplexRecurrence a b (k + 1) - b * simplexRecurrence a b k

@[simp] theorem simplexRecurrence_zero (a b : ℝ) : simplexRecurrence a b 0 = 1 := rfl

@[simp] theorem simplexRecurrence_one (a b : ℝ) : simplexRecurrence a b 1 = 1 := rfl

theorem simplexRecurrence_step (a b : ℝ) (k : ℕ) :
    simplexRecurrence a b (k + 2) =
      a * simplexRecurrence a b (k + 1) - b * simplexRecurrence a b k := rfl

/-- Sine addition in the form used by the coefficient recurrence. -/
theorem sine_recurrence (θ : ℝ) (k : ℕ) :
    Real.sin (((k + 2 : ℕ) : ℝ) * θ) =
      2 * Real.cos θ * Real.sin (((k + 1 : ℕ) : ℝ) * θ) -
        Real.sin ((k : ℝ) * θ) := by
  have h₁ : ((k + 2 : ℕ) : ℝ) * θ = ((k : ℝ) + 1) * θ + θ := by push_cast; ring
  have h₂ : (k : ℝ) * θ = ((k : ℝ) + 1) * θ - θ := by ring
  rw [h₁, h₂, Real.sin_add, Real.sin_sub]
  push_cast
  ring

/-- Closed form for the actual recursively defined coefficients, including `k=0`. -/
theorem simplexRecurrence_sine (q θ : ℝ) (hθ : Real.sin θ ≠ 0) (k : ℕ) :
    simplexRecurrence (2 * q * Real.cos θ) (q ^ 2) (k + 1) =
      q ^ k * (Real.sin (((k + 1 : ℕ) : ℝ) * θ) -
        q * Real.sin ((k : ℝ) * θ)) / Real.sin θ := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hθ]
  | one =>
    rw [simplexRecurrence_step]
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat, simplexRecurrence_one,
      simplexRecurrence_zero, mul_one, one_mul, pow_one]
    rw [Real.sin_two_mul]
    field_simp
  | more k hk hk1 =>
    rw [show k + 2 + 1 = (k + 1) + 2 by omega, simplexRecurrence_step, hk1, hk]
    rw [sine_recurrence θ (k + 1), sine_recurrence θ k]
    rw [pow_succ, pow_succ]
    field_simp
    ring

/-- At an integral phase, the sine solution is the signed power in equation (4). -/
theorem simplexRecurrence_integral_phase (q θ : ℝ) {m ℓ : ℕ}
    (hm : 1 ≤ m) (hθ : Real.sin θ ≠ 0)
    (hphase : ((m - 1 : ℕ) : ℝ) * θ = (ℓ : ℝ) * Real.pi) :
    simplexRecurrence (2 * q * Real.cos θ) (q ^ 2) m =
      (-1 : ℝ) ^ ℓ * q ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  change (k : ℝ) * θ = (ℓ : ℝ) * Real.pi at hphase
  change simplexRecurrence (2 * q * Real.cos θ) (q ^ 2) (k + 1) =
    (-1 : ℝ) ^ ℓ * q ^ k
  rw [simplexRecurrence_sine q θ hθ]
  have hs : Real.sin ((k : ℝ) * θ) = 0 := by
    rw [hphase, Real.sin_nat_mul_pi]
  have hs' : Real.sin (((k + 1 : ℕ) : ℝ) * θ) = (-1 : ℝ) ^ ℓ * Real.sin θ := by
    rw [show ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ by push_cast; ring,
      hphase, Real.sin_add]
    simp [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  rw [hs, hs']
  field_simp
  ring

end NoncommutativeAMGM
