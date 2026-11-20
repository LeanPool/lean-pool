/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic
public import Mathlib.Algebra.Group.ForwardDiff

/-! # Appendix C's finite binomial interpolation identity -/

@[expose] public section

namespace NoncommutativeAMGM
open scoped BigOperators

/-- The finite-difference coefficient of a function on the natural indices. -/
noncomputable def binomialDifference (φ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ v ∈ Finset.range (j + 1), (-1 : ℝ) ^ (j - v) * (j.choose v : ℝ) * φ v

/-- The alternating sum is the actual iterated forward difference. -/
theorem binomialDifference_eq_forwardDiff (φ : ℕ → ℝ) (j : ℕ) :
    binomialDifference φ j = (fwdDiff (1 : ℕ))^[j] φ 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) φ j 0
  simpa only [binomialDifference, nsmul_eq_mul, mul_one, zero_add, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_id, mul_assoc] using h.symm

/-- Newton's binomial expansion is exact for every function on every finite initial interval. -/
theorem binomial_interpolation (φ : ℕ → ℝ) (v : ℕ) :
    φ v = ∑ l ∈ Finset.range (v + 1), (v.choose l : ℝ) * binomialDifference φ l := by
  simp_rw [binomialDifference_eq_forwardDiff]
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) φ v 0
  simpa only [nsmul_eq_mul, mul_one, zero_add, Nat.cast_id] using h

/-- Alternating binomial sums isolate one coefficient of the binomial basis. -/
theorem alternating_choose_orthogonality (j l : ℕ) :
    (∑ v ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ (j - v) * (j.choose v : ℝ) * (v.choose l : ℝ)) =
        if j = l then 1 else 0 := by
  rw [show (∑ v ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ (j - v) * (j.choose v : ℝ) * (v.choose l : ℝ)) =
      binomialDifference (fun v ↦ (v.choose l : ℝ)) j by rfl,
    binomialDifference_eq_forwardDiff, fwdDiff_iter_choose_zero]

/-- Lemma C.3: the top binomial coefficient is the alternating finite-difference sum. -/
theorem binomial_interpolation_top {j : ℕ} (φ b : ℕ → ℝ)
    (hφ : ∀ v ≤ j, φ v = ∑ l ∈ Finset.range (j + 1), b l * (v.choose l : ℝ)) :
    b j = ∑ v ∈ Finset.range (j + 1), (-1 : ℝ) ^ (j - v) * (j.choose v : ℝ) * φ v := by
  have he : (∑ v ∈ Finset.range (j + 1), (-1 : ℝ) ^ (j - v) * (j.choose v : ℝ) * φ v) =
      ∑ l ∈ Finset.range (j + 1), b l *
        (∑ v ∈ Finset.range (j + 1),
          (-1 : ℝ) ^ (j - v) * (j.choose v : ℝ) * (v.choose l : ℝ)) := by
    calc
      _ = ∑ v ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1),
          b l * ((-1 : ℝ) ^ (j - v) * (j.choose v : ℝ) * (v.choose l : ℝ)) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hφ v (by have := Finset.mem_range.mp hv; omega), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  rw [he]
  simp_rw [alternating_choose_orthogonality, mul_ite, mul_one, mul_zero]
  simp

end NoncommutativeAMGM
