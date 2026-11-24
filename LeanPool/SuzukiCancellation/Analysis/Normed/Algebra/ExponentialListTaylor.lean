/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.RealScalar
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialCalculus
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialListSeries

/-!
# Taylor coefficients of ordered exponential products

The ordinary higher product rule identifies the algebraic Cauchy coefficients
with derivatives of the actual exponential product. No differentiation of an
asymptotic remainder is used.

## Main results

* `iteratedDeriv_prod_exp_smul_zero`: derivatives are factorials times coefficients.
-/

@[expose] public noncomputable section

open scoped RealScalar

namespace FQFP

open Finset Finset.Nat NormedSpace TrotterError
open scoped ContDiff

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The ordered product of exponential curves is smooth. -/
theorem contDiff_prod_exp_smul (l : List A) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (l.map fun a ↦ exp (t • a)).prod) :=
  TrotterError.List.contDiff_list_prod l (fun a t ↦ exp (t • a))
    (fun a _ ↦ contDiff_exp_smul_const a)

/-- Higher derivatives at zero agree with the finite formal coefficients. -/
theorem iteratedDeriv_prod_exp_smul_zero (l : List A) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ (l.map fun a ↦ exp (t • a)).prod) 0 =
      (Nat.factorial n : ℝ) • expListTerm l n := by
  induction l generalizing n with
  | nil => cases n <;> simp [expListTerm, iteratedDeriv_const]
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [iteratedDeriv_fun_mul (contDiffAt_exp_smul_const a n 0)
        ((contDiff_prod_exp_smul l).contDiffAt.of_le (by exact_mod_cast le_top)),
        expListTerm, sum_antidiagonal_eq_sum_range_succ_mk, smul_sum]
      apply sum_congr rfl
      intro i hi
      rw [ih, iteratedDeriv_exp_smul_const]
      simp only [zero_smul, exp_zero, mul_one, ← Rat.cast_smul_eq_qsmul ℝ,
        Rat.cast_inv, Rat.cast_natCast, smul_mul_assoc, smul_smul, mul_smul_comm]
      rw [← map_natCast (algebraMap ℝ A), ← Algebra.smul_def,
        smul_mul_assoc, smul_smul]
      congr 1
      have hchoose : (n.choose i : ℝ) * i.factorial * (n - i).factorial = n.factorial := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by
          have := mem_range.mp hi
          lia)
      have hf : (i.factorial : ℝ) ≠ 0 := by positivity
      rw [← div_eq_mul_inv]
      apply (eq_div_iff hf).mpr
      nlinarith only [hchoose]

/-- A finite Taylor expansion with a scalar exponential remainder, for every real time. -/
theorem norm_prod_exp_smul_sub_sum_le [NormOneClass A] (l : List A) (t : ℝ) (n : ℕ) :
    ‖(l.map fun a ↦ exp (t • a)).prod -
      ∑ k ∈ range n, t ^ k • expListTerm l k‖ ≤
        Real.exp ((l.map fun a ↦ ‖t • a‖).sum) -
          ∑ k ∈ range n, (l.map fun a ↦ ‖t • a‖).sum ^ k / Nat.factorial k := by
  simpa only [expListTerm_smul, List.map_map, Function.comp_def] using
    norm_prod_exp_sub_sum_le (l.map fun a ↦ t • a) n

end FQFP
