/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.RealScalar
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiJet
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialListTaylor

/-!
# Taylor expansion and derivatives of the Suzuki product

The sixth-order formal jet is the jet of the actual Banach algebra exponential
product. Its Taylor remainder is bounded for every real time. The local
logarithm has a controlled seventh-order remainder.

## Main results

* `iteratedDeriv_fiveStageStrangProduct_zero`: derivatives of the actual product.
* `contDiff_fiveStageStrangProduct`: smoothness for every real parameter.
* `norm_fiveStageStrangProduct_sub_taylor_le`: the global finite Taylor remainder.
* `norm_fiveStageStrangLog_sub_quintic_le_septic`: the local logarithm remainder.
-/

@[expose] public noncomputable section

open scoped RealScalar ContDiff

namespace FQFP.BCH

open Finset NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The actual five-stage Strang product is smooth for every real composition parameter. -/
theorem contDiff_fiveStageStrangProduct (a b : A) (p : ℝ) :
    ContDiff ℝ ∞ (fiveStageStrangProduct a b p) := by
  convert contDiff_prod_exp_smul (fiveStageStrangArguments a b p 1) using 1
  funext t
  rw [fiveStageStrangProduct, fiveStageStrangArguments_smul]
  simp only [List.map_map, Function.comp_def]

/-- The actual Suzuki product has the factorial-scaled formal coefficients as derivatives. -/
theorem iteratedDeriv_fiveStageStrangProduct_zero (a b : A) (p : ℝ) (n : ℕ) :
    iteratedDeriv n (fiveStageStrangProduct a b p) 0 =
      (Nat.factorial n : ℝ) • expListTerm (fiveStageStrangArguments a b p 1) n := by
  have hf : fiveStageStrangProduct a b p = fun t : ℝ ↦
      ((fiveStageStrangArguments a b p 1).map fun x ↦ exp (t • x)).prod := by
    funext t
    rw [fiveStageStrangProduct, fiveStageStrangArguments_smul]
    simp only [List.map_map, Function.comp_def]
  rw [hf]
  exact iteratedDeriv_prod_exp_smul_zero (fiveStageStrangArguments a b p 1) n

/-- The controlled sixth-order Taylor jet, valid for all real times. -/
theorem norm_fiveStageStrangProduct_sub_taylor_le [NormOneClass A]
    (a b : A) (p t : ℝ) (hp : IsSuzukiCubic p) :
    ‖fiveStageStrangProduct a b p t -
      ((∑ k ∈ range 7, (t ^ k / Nat.factorial k : ℝ) • (a + b) ^ k) +
        t ^ 5 • suzukiQuinticTerm a b p + (t ^ 6 / 2) •
          ((a + b) * suzukiQuinticTerm a b p + suzukiQuinticTerm a b p * (a + b)))‖ ≤
      Real.exp (fiveStageStrangArgNormBound a b p t) -
        ∑ k ∈ range 7, fiveStageStrangArgNormBound a b p t ^ k / Nat.factorial k := by
  have hj : (∑ k ∈ range 7,
      expListTerm (fiveStageStrangArguments a b p t) k) =
      (∑ k ∈ range 7, (t ^ k / Nat.factorial k : ℝ) • (a + b) ^ k) +
        t ^ 5 • suzukiQuinticTerm a b p + (t ^ 6 / 2) •
          ((a + b) * suzukiQuinticTerm a b p + suzukiQuinticTerm a b p * (a + b)) := by
    rw [fiveStageStrangArguments_smul]
    simp only [expListTerm_smul]
    trans ∑ k ∈ range 7, t ^ k • ((Nat.factorial k : ℚ)⁻¹ • (a + b) ^ k +
      if k = 5 then suzukiQuinticTerm a b p else
      if k = 6 then (2 : ℚ)⁻¹ •
        ((a + b) * suzukiQuinticTerm a b p + suzukiQuinticTerm a b p * (a + b)) else 0)
    · apply sum_congr rfl
      intro k hk
      congr 1
      simpa [Fin.ext_iff] using
        expListTerm_fiveStageStrang_through_six a b p hp ⟨k, mem_range.mp hk⟩
    simp only [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_inv,
      Rat.cast_natCast, smul_add, smul_smul]
    norm_num [sum_range_succ, div_eq_mul_inv]
    module
  have h := norm_prod_exp_sub_sum_le (fiveStageStrangArguments a b p t) 7
  rwa [hj, sum_norm_fiveStageStrangArguments] at h

/-- The formal logarithm jet gives a seventh-order analytic remainder on the quarter ball. -/
theorem norm_fiveStageStrangLog_sub_quintic_le_septic [NormOneClass A]
    (a b : A) (p t : ℝ) (hp : IsSuzukiCubic p)
    (ht : fiveStageStrangArgNormBound a b p t < 1 / 4) :
    ‖fiveStageStrangLog a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p‖ ≤
      704 * fiveStageStrangArgNormBound a b p t ^ 7 := by
  have hj : (∑ k ∈ range 7, expListLogCoeff (fiveStageStrangArguments a b p t) k) =
      t • (a + b) + t ^ 5 • suzukiQuinticTerm a b p := by
    rw [fiveStageStrangArguments_smul]
    simp only [expListLogCoeff_smul]
    trans ∑ k ∈ range 7, t ^ k •
      (if k = 1 then a + b else if k = 5 then suzukiQuinticTerm a b p else 0)
    · apply sum_congr rfl
      intro k hk
      congr 1
      simpa [Fin.ext_iff] using
        expListLogCoeff_fiveStageStrang_through_six a b p hp ⟨k, mem_range.mp hk⟩
    norm_num [sum_range_succ]
  have h := norm_log_prod_exp_sub_sum_le (fiveStageStrangArguments a b p t)
    (by rwa [sum_norm_fiveStageStrangArguments]) 7
  rw [hj, sum_norm_fiveStageStrangArguments] at h
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow] at h
  simpa only [fiveStageStrangLog, fiveStageStrangProduct, sub_add_eq_sub_sub] using h

end FQFP.BCH
