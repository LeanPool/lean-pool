/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ProductWeights
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-! Bernoulli weights for finite bit vectors and the distribution of their counts. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

/-- The mass of a single bit under a Bernoulli law of parameter `t`. -/
def bernoulliWeight (t : ℝ) (b : Bool) : ℝ := if b then t else 1 - t

/-- The number of true entries in a vector of bits. -/
def bitCount {m : ℕ} (x : Fin m → Bool) : ℕ := ∑ i, if x i then 1 else 0

/-- The product mass of a vector of independent Bernoulli bits. -/
def bernoulliVectorWeight (t : ℝ) (m : ℕ) (x : Fin m → Bool) : ℝ :=
  productWeight (fun _ => bernoulliWeight t) x

theorem bernoulliWeight_nonneg (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (b : Bool) :
    0 ≤ bernoulliWeight t b := by
  cases b <;> simp only [bernoulliWeight, Bool.false_eq_true, ite_false, ite_true] <;> linarith

theorem bernoulliWeight_sum (t : ℝ) : ∑ b, bernoulliWeight t b = 1 := by
  simp [bernoulliWeight]

theorem bernoulliVectorWeight_nonneg (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (m : ℕ) (x : Fin m → Bool) : 0 ≤ bernoulliVectorWeight t m x := by
  exact productWeight_nonneg _ (fun _ b => bernoulliWeight_nonneg t ht b) x

theorem bernoulliVectorWeight_sum (t : ℝ) (m : ℕ) :
    ∑ x, bernoulliVectorWeight t m x = 1 := by
  exact productWeight_sum _ (fun _ => bernoulliWeight_sum t)

theorem bitCount_cons {m : ℕ} (b : Bool) (x : Fin m → Bool) :
    bitCount (Fin.cons b x) = (if b then 1 else 0) + bitCount x := by
  simp only [bitCount, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem bernoulliVectorWeight_cons (t : ℝ) {m : ℕ} (b : Bool) (x : Fin m → Bool) :
    bernoulliVectorWeight t (m + 1) (Fin.cons b x) =
      bernoulliWeight t b * bernoulliVectorWeight t m x := by
  simp [bernoulliVectorWeight, productWeight, Fin.prod_univ_succ]

/-- Exact common-reference coupling for an extra Bernoulli position.
It applies to every function of the count, not just its first two moments. -/
theorem bernoulli_count_succ_mean (t : ℝ) (m : ℕ) (F : ℕ → ℝ) :
    mean (bernoulliVectorWeight t (m + 1)) (fun x => F (bitCount x)) =
      (1 - t) * mean (bernoulliVectorWeight t m) (fun x => F (bitCount x)) +
      t * mean (bernoulliVectorWeight t m) (fun x => F (bitCount x + 1)) := by
  unfold mean
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply,
    bernoulliVectorWeight_cons, bitCount_cons, Fintype.sum_bool,
    bernoulliWeight, Bool.false_eq_true, ite_false, ite_true, zero_add]
  simp only [Nat.add_comm 1, mul_assoc, ← Finset.mul_sum]
  ring

end Shellsort
