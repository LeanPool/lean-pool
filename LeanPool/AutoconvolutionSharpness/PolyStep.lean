/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.Interpolation
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# From a polynomial to a step function

Mathlib's `Polynomial.toFn` and `Polynomial.ofFn` identify a finite coefficient
vector with its polynomial. This identifies the coefficients used by the real
convolution formula with those of the polynomial square.
-/

@[expose] public section

open Finset Polynomial
noncomputable section

namespace Autoconvolutions

theorem convCoeff_eq_ofFn_sq (d : ℕ) (p : Fin (d + 1) → ℝ) (k : ℕ) :
    convCoeff d p (k : ℤ) = (Polynomial.ofFn (d + 1) p ^ 2).coeff k := by
  classical
  simp only [convCoeff, pow_two, Polynomial.ofFn_eq_sum_monomial,
    Finset.sum_mul, Finset.mul_sum, Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial, Polynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  norm_cast
  rw [Nat.add_comm i.val j.val, mul_comm (p i) (p j)]

theorem convCoeff_eq_poly_sq (F : Polynomial ℝ) (k : ℕ) :
    convCoeff F.natDegree (Polynomial.toFn (F.natDegree + 1) F) (k : ℤ) = (F ^ 2).coeff k := by
  rw [convCoeff_eq_ofFn_sq, Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]

theorem convCoeff_of_neg (d : ℕ) (p : Fin (d + 1) → ℝ) {k : ℤ} (hk : k < 0) :
    convCoeff d p k = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact ite_eq_right (by omega)

theorem poly_sum_eq_eval_one (F : Polynomial ℝ) :
    (∑ i : Fin (F.natDegree + 1), Polynomial.toFn (F.natDegree + 1) F i) = F.eval 1 := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range]
  simp [Polynomial.toFn]

theorem exists_pos_coeff_of_eval_pos (F : Polynomial ℝ) (hF : 0 < F.eval 1) :
    ∃ i : Fin (F.natDegree + 1), 0 < Polynomial.toFn (F.natDegree + 1) F i := by
  by_contra! h
  rw [← poly_sum_eq_eval_one] at hF
  exact (not_lt_of_ge (Finset.sum_nonpos (fun i _ => h i))) hF

end Autoconvolutions
