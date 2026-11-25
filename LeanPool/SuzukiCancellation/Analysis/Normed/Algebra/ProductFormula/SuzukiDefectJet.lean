/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricDefect
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricDefectSeries
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiHalf
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiTaylor

/-!
# The leading even coefficients of the Suzuki half-defect

The previously certified product jet is transported into the symmetric moving
frame. Unit-constant transport preserves the leading residual coefficient, so
the constant and quadratic half-defect coefficients vanish and its quartic
coefficient is `5/2` times the quintic Lie polynomial.

## Main results

* `fiveStageStrangProduct_eq_symmetricExpProduct`: the actual symmetric factorization.
* `groupedConjCoeff_fiveStageStrang_even`: the three even coefficients through degree four.
-/

@[expose] public noncomputable section

open NormedSpace Finset PowerSeries TrotterError
open scoped RealScalar

namespace FQFP.BCH

variable {A : Type*} [Ring A] [Algebra ℝ A]

section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The actual Suzuki product is the symmetric product of its six half-generators. -/
theorem fiveStageStrangProduct_eq_symmetricExpProduct (a b : A) (p t : ℝ) :
    fiveStageStrangProduct a b p t =
      symmetricExpProduct (List.ofFn (fiveStageStrangHalfGenerator a b p)) t := by
  rw [fiveStageStrangProduct_eq_half_mul_reverse, symmetricExpProduct,
    fiveStageStrangHalfGenerator_ofFn, fiveStageStrangHalfProduct,
    fiveStageStrangReverseHalfProduct, fiveStageStrangHalfArguments_smul]
  simp [expListProduct, List.map_map, List.map_reverse, Function.comp_def]

/-- The formal symmetric half-product has the actual Suzuki product's certified jet. -/
lemma coeff_symmetricHalfSeries_fiveStageStrang (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 6) :
    coeff n (expListSeries (List.ofFn (fiveStageStrangHalfGenerator a b p)) *
      expListSeries (List.ofFn (fiveStageStrangHalfGenerator a b p)).reverse) =
      (Nat.factorial n : ℚ)⁻¹ • (a + b) ^ (n : ℕ) +
        if n = 5 then suzukiQuinticTerm a b p else 0 := by
  let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
  have hf : fiveStageStrangProduct a b p =
      fun t : ℝ ↦ ((l ++ l.reverse).map fun Z ↦ exp (t • Z)).prod := by
    funext t
    rw [fiveStageStrangProduct_eq_symmetricExpProduct]
    simp [symmetricExpProduct, expListProduct, l, mul_assoc]
  have hd := iteratedDeriv_fiveStageStrangProduct_zero a b p (n : ℕ)
  rw [hf, iteratedDeriv_prod_exp_smul_zero] at hd
  have he := (smul_right_injective A (by positivity : (Nat.factorial n : ℝ) ≠ 0)) hd
  rw [← expListSeries_append, coeff_expListSeries]
  rw [he]
  have hbound := n.isLt
  have hn : (n : ℕ) ≠ 6 := by lia
  simpa [Fin.ext_iff, hn] using
    expListTerm_fiveStageStrang_through_six a b p hp ⟨n, by lia⟩

/-- The symmetric residual has no terms below degree four, whose coefficient is `5 L₅`. -/
lemma coeff_symmetricResidualSeries_fiveStageStrang (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 5) :
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    coeff n (seriesDerivative (expListSeries l * expListSeries l.reverse) -
      (1 / 2 : ℝ) • (C (a + b) * (expListSeries l * expListSeries l.reverse) +
        (expListSeries l * expListSeries l.reverse) * C (a + b))) =
      if n = 4 then (5 : ℝ) • suzukiQuinticTerm a b p else 0 := by
  dsimp only
  have hbound := n.isLt
  rw [map_sub, coeff_seriesDerivative, coeff_smul, map_add, coeff_C_mul, coeff_mul_C]
  rw [coeff_symmetricHalfSeries_fiveStageStrang a b p hp
      ⟨n + 1, by lia⟩,
    coeff_symmetricHalfSeries_fiveStageStrang a b p hp ⟨n, by lia⟩]
  generalize a + b = G
  generalize suzukiQuinticTerm a b p = L
  fin_cases n <;> norm_num [Fin.ext_iff, pow_succ, mul_assoc,
    ← Rat.cast_smul_eq_qsmul ℝ, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc]
  all_goals module

/-- The constant and quadratic half-defect coefficients vanish; the quartic is `5 L₅ / 2`. -/
theorem groupedConjCoeff_fiveStageStrang_even (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 3) :
    groupedConjCoeff (fun i ↦ -fiveStageStrangHalfGenerator a b p i)
      (fiveStageStrangHalfGenerator a b p) (-(1 / 2 : ℝ) • (a + b)) (2 * (n : ℕ)) =
      if n = 2 then (5 / 2 : ℝ) • suzukiQuinticTerm a b p else 0 := by
  let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
  let T := halfDefectSeries l (a + b) - halfDefectSeries (l.map Neg.neg) (-(a + b))
  have hfactor := symmetricResidualSeries_eq_halfDefect l (a + b)
  have hd (k : Fin 5) :
      coeff k (expListSeries l * T * expListSeries l.reverse) =
        if k = 4 then (5 : ℝ) • suzukiQuinticTerm a b p else 0 := by
    rw [← hfactor]
    exact coeff_symmetricResidualSeries_fiveStageStrang a b p hp k
  have ht := coeff_middle_eq_of_lt_eq_zero (expListSeries l) T
    (expListSeries l.reverse) (by simp) (by simp) (2 * (n : ℕ)) (fun k hk ↦ by
      have hn := n.isLt
      have hk4 : k < 4 := by lia
      simpa [Fin.ext_iff, show k ≠ 4 by lia] using hd ⟨k, by lia⟩)
  have hbound := n.isLt
  rw [hd ⟨2 * (n : ℕ), by lia⟩] at ht
  dsimp only [T, l] at ht
  rw [map_sub, coeff_halfDefectSeries_neg, coeff_halfDefectSeries] at ht
  have hh := congrArg (fun v : A ↦ (1 / 2 : ℝ) • v) ht
  fin_cases n <;> norm_num [Fin.ext_iff] at hh ⊢
  all_goals convert hh using 1 <;> module

/-- Reflecting and adding the degree-five polynomial leaves exactly the quintic defect term. -/
theorem sum_groupedConjCoeff_fiveStageStrang_reflected (a b : A) (p x : ℝ)
    (hp : IsSuzukiCubic p) :
    let c := groupedConjCoeff (fun i ↦ -fiveStageStrangHalfGenerator a b p i)
      (fiveStageStrangHalfGenerator a b p) (-(1 / 2 : ℝ) • (a + b))
    (∑ k ∈ range 6, x ^ k • c k) + (∑ k ∈ range 6, (-x) ^ k • c k) =
      (5 * x ^ 4) • suzukiQuinticTerm a b p := by
  dsimp only
  have h0 := groupedConjCoeff_fiveStageStrang_even a b p hp 0
  have h2 := groupedConjCoeff_fiveStageStrang_even a b p hp 1
  have h4 := groupedConjCoeff_fiveStageStrang_even a b p hp 2
  norm_num only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceMul,
    Fin.reduceEq, ite_false, ite_true] at h0 h2 h4
  simp only [sum_range_succ, sum_range_zero, h0, h2, h4, smul_zero,
    add_zero, zero_add, smul_smul]
  module

end

end FQFP.BCH
