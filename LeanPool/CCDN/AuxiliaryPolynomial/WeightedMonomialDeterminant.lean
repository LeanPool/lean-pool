/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Int.AbsoluteValue

/-! Archimedean determinant bounds retaining each monomial's own degree.
Their exponent is the sum of column degrees, not rank times the cutoff. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Matrix

private theorem abs_det_le_factorial_mul_column_bounds {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ)
    (hA : ∀ i j, |A i j| ≤ b j) :
    |A.det| ≤ (s.factorial : ℝ) * ∏ j, b j := by
  classical
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  calc
    |A.det| ≤ ∑ σ : Equiv.Perm (Fin s),
        abv (Equiv.Perm.sign σ • ∏ j, A (σ j) j) := by
      rw [Matrix.det_apply]
      exact abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin s), ∏ j, |A (σ j) j| := by
      apply sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ _σ : Equiv.Perm (Fin s), ∏ j, b j := by
      apply sum_le_sum
      intro σ _
      exact prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hA (σ j) j)
    _ = _ := by simp [Fintype.card_perm]

private theorem weighted_evaluation_det_bound {n s : ℕ}
    (mon : Fin s → (Fin n →₀ ℕ)) (z : Fin s → (Fin n → ℤ))
    {B : ℝ} (hB : 1 ≤ B) (hz : ∀ i, InBox (z i) B) :
    |((evaluationMatrix mon z).det : ℝ)| ≤
      (s.factorial : ℝ) * B ^ (∑ j, Finsupp.degree (mon j)) := by
  have hh := abs_det_le_factorial_mul_column_bounds
    ((evaluationMatrix mon z).map (Int.castRingHom ℝ))
    (fun j => B ^ Finsupp.degree (mon j))
    (fun i j => abs_monomial_value_le (mon j) (z i) hB (hz i) le_rfl)
  have he : ((evaluationMatrix mon z).map (Int.castRingHom ℝ)).det =
      ((evaluationMatrix mon z).det : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [he, prod_pow_eq_pow_sum] at hh
  exact hh

/-- A nonzero integer determinant has the sharp sum-of-degrees logarithmic
upper bound. -/
theorem weighted_evaluation_det_log_bound {n s : ℕ}
    (mon : Fin s → (Fin n →₀ ℕ)) (z : Fin s → (Fin n → ℤ))
    {B : ℝ} (hB : 1 ≤ B) (hz : ∀ i, InBox (z i) B)
    (hne : (evaluationMatrix mon z).det ≠ 0) :
    Real.log |((evaluationMatrix mon z).det : ℝ)| ≤
      Real.log (s.factorial : ℝ) +
        (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B := by
  have hB0 : 0 < B := by linarith
  have hdet : (0 : ℝ) < |((evaluationMatrix mon z).det : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast hne)
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hlog := Real.log_le_log hdet (weighted_evaluation_det_bound mon z hB hz)
  rw [Real.log_mul hfac.ne' (pow_pos hB0 _).ne', Real.log_pow] at hlog
  simpa only [Nat.cast_sum] using hlog

end
end CCDN
