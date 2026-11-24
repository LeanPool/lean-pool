/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialListBounds
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialProduct

/-!
# Logarithm of an ordered exponential product

On the quarter-radius ball, the logarithm is approximated by the sum of its homogeneous
coefficients. The error combines the logarithm series tail with the finite polynomial
estimate from `ExponentialListBounds`.
-/

@[expose] public noncomputable section

open Finset NormedSpace

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormOneClass A] [CompleteSpace A]

/-- The logarithm truncation error with the sum of the actual logarithm coefficient norms. -/
theorem norm_log_prod_exp_sub_sum_le_weighted (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (n : ℕ) :
    ‖log ((l.map exp).prod) - ∑ d ∈ range n, expListLogCoeff l d‖ ≤
      ((∑ k ∈ range n, ‖logCoeff k‖) * 2 ^ (n - 1) + 2 ^ (n + 1)) * (l.map norm).sum ^ n := by
  rw [sum_expListLogCoeff]
  let s := (l.map norm).sum
  let y := (l.map exp).prod - 1
  have hs : 0 ≤ s := list_sum_norm_nonneg l
  have hy : ‖y‖ ≤ 2 * s := norm_prod_exp_sub_one_le_two_mul l hl
  have htail : ‖log ((l.map exp).prod) - logPartialSum A n y‖ ≤
      2 ^ (n + 1) * s ^ n := by
    rw [show (l.map exp).prod = 1 + y by dsimp [y]; abel]
    exact norm_log_one_add_sub_logPartialSum_le_two_mul y n hs hl hy
  have hfinite := norm_logPartialSum_prod_exp_sub_sum_le_weighted l hl n
  calc
    _ ≤ ‖log ((l.map exp).prod) - logPartialSum A n y‖ +
        ‖logPartialSum A n y -
          ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expListTerm l) k n‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 ^ (n + 1) * s ^ n + (∑ k ∈ range n, ‖logCoeff k‖) * 2 ^ (n - 1) * s ^ n :=
      add_le_add htail hfinite
    _ = _ := by ring

/-- Every small finite exponential product has a uniform homogeneous logarithm approximation. -/
theorem norm_log_prod_exp_sub_sum_le (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (n : ℕ) :
    ‖log ((l.map exp).prod) - ∑ d ∈ range n, expListLogCoeff l d‖ ≤
      ((n : ℝ) * 2 ^ (n - 1) + 2 ^ (n + 1)) * (l.map norm).sum ^ n := by
  apply (norm_log_prod_exp_sub_sum_le_weighted l hl n).trans
  have hs := list_sum_norm_nonneg l
  gcongr
  exact sum_norm_logCoeff_le n

end FQFP
