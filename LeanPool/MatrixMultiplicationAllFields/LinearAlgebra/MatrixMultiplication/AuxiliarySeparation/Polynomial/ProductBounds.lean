/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Optimization
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Combining the scalar sector bounds

Pointwise character bounds multiply over a finite family of leg orders. After
normalization by the sum of the singleton exponents, the entropy identity gives
the midpoint-concavity bound for the profile.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- Multiplying the entropy bounds and taking the positive normalization root
gives the midpoint-concavity inequality. -/
theorem finite_product_concavity {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i q, 0 ≤ q → q ≤ 1 →
      Real.exp (p i * Real.binEntropy q) * (B i) ^ q * (C i) ^ (1 - q) ≤
        (2 : ℝ) ^ (p i) * A i) :
    (∏ i, B i) ^ (1 / s) + (∏ i, C i) ^ (1 / s) ≤
      2 * (∏ i, A i) ^ (1 / s) := by
  have hprodA : 0 < ∏ i, A i := Finset.prod_pos (fun i _ => hA i)
  have hprodB : 0 < ∏ i, B i := Finset.prod_pos (fun i _ => hB i)
  have hprodC : 0 < ∏ i, C i := Finset.prod_pos (fun i _ => hC i)
  let a : ℝ := (∏ i, A i) ^ (1 / s)
  let b : ℝ := (∏ i, B i) ^ (1 / s)
  let c : ℝ := (∏ i, C i) ^ (1 / s)
  have ha : 0 < a := Real.rpow_pos_of_pos hprodA _
  have hb : 0 < b := Real.rpow_pos_of_pos hprodB _
  have hc : 0 < c := Real.rpow_pos_of_pos hprodC _
  let q : ℝ := b / (b + c)
  have hq0 : 0 ≤ q := le_of_lt (div_pos hb (add_pos hb hc))
  have hq1 : q ≤ 1 := (div_le_one (add_pos hb hc)).mpr (le_of_lt (lt_add_of_pos_right b hc))
  have hlog : ∀ i, p i * Real.binEntropy q + q * Real.log (B i) +
      (1 - q) * Real.log (C i) ≤ p i * Real.log 2 + Real.log (A i) := by
    intro i
    have hleft1 : 0 < Real.exp (p i * Real.binEntropy q) * (B i) ^ q :=
      mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (hB i) _)
    have h := Real.log_le_log
      (mul_pos hleft1 (Real.rpow_pos_of_pos (hC i) _)) (hbound i q hq0 hq1)
    rw [Real.log_mul hleft1.ne' (Real.rpow_pos_of_pos (hC i) _).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (hB i) _).ne',
      Real.log_exp, Real.log_rpow (hB i), Real.log_rpow (hC i),
      Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
        (hA i).ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h
    simpa only [mul_comm (Real.log 2) (p i)] using h
  have hlogs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlog i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hsum, ← Real.log_prod (fun i _ => (hA i).ne'),
    ← Real.log_prod (fun i _ => (hB i).ne'),
    ← Real.log_prod (fun i _ => (hC i).ne')] at hlogs
  have hnormalized : Real.binEntropy q + Real.log b * q + Real.log c * (1 - q) ≤
      Real.log 2 + Real.log a := by
    dsimp only [a, b, c]
    rw [Real.log_rpow hprodA, Real.log_rpow hprodB, Real.log_rpow hprodC]
    convert div_le_div_of_nonneg_right hlogs hs.le using 1 <;> field_simp [hs.ne']
  change Real.binEntropy (b / (b + c)) + Real.log b * (b / (b + c)) +
      Real.log c * (1 - b / (b + c)) ≤ Real.log 2 + Real.log a at hnormalized
  rw [binary_entropy_log_partition hb hc,
    ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne'] at hnormalized
  exact (Real.log_le_log_iff (add_pos hb hc) (mul_pos (by norm_num) ha)).mp hnormalized

/-- Multiplying the cyclic bounds and taking the positive normalization root
gives the factor of three in the tripling inequality. -/
theorem finite_product_tripling {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (_hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i, (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ) ≤ A i)
    (hprod_eq : ∏ i, C i = ∏ i, B i) :
    3 * (∏ i, B i) ^ (1 / s) ≤ (∏ i, A i) ^ (1 / s) := by
  have hBprod : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  have hprod : (3 : ℝ) ^ s * (∏ i, B i) ≤ ∏ i, A i := by
    have hmul := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i => (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ))
      (g := A)
      (fun i _ => mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (hB i).le _))
        (Real.rpow_nonneg (hC i).le _))
      (fun i _ => hbound i)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3) p Finset.univ, hsum,
      Real.finsetProd_rpow Finset.univ B (fun i _ => (hB i).le),
      Real.finsetProd_rpow Finset.univ C (fun i _ => (hC i).le), hprod_eq,
      mul_assoc, ← Real.rpow_add hBprod] at hmul
    norm_num at hmul
    exact hmul
  have hmean := Real.rpow_le_rpow (by positivity) hprod (by positivity : (0 : ℝ) ≤ 1 / s)
  rw [Real.mul_rpow (by positivity) hBprod.le,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_one_div_cancel hs.ne',
    Real.rpow_one] at hmean
  exact hmean

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
