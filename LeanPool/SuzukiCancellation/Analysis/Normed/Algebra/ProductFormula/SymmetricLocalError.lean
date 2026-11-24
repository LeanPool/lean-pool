/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricDefect

/-!
# Local error from an even symmetric defect

The symmetric Duhamel formula transports the middle defect without norm growth.
Integrating a fourth-degree leading term and a sixth-degree remainder gives the
fifth- and seventh-degree local error bound for every real step.

## Main results

* `norm_symmetricExpProduct_sub_exp_le`: integrate a bound for the middle defect.
* `norm_halfDefect_add_sub_sum_le`: grouped remainder for the even middle defect.
* `norm_symmetricExpProduct_sub_exp_le_grouped`: the grouped seventh-degree constant.
-/

@[expose] public noncomputable section

open NormedSpace MeasureTheory TrotterError Finset
open scoped RealScalar

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- A product of exponentials with two-sided contraction bounds acts isometrically on the left. -/
lemma norm_expListProduct_mul_eq_of_le_one (l : List A) (B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (t : ℝ) :
    ‖expListProduct l t * B‖ = ‖B‖ := by
  induction l with
  | nil => simp
  | cons Z l ih =>
      rw [expListProduct_cons, mul_assoc,
        norm_exp_smul_mul_eq_of_le_one Z _ (hZ Z (by simp)) t]
      exact ih (fun Z hmem ↦ hZ Z (by simp [hmem]))

/-- A product of exponentials with two-sided contraction bounds acts isometrically on the right. -/
lemma norm_mul_expListProduct_eq_of_le_one (l : List A) (B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (t : ℝ) :
    ‖B * expListProduct l t‖ = ‖B‖ := by
  induction l generalizing B with
  | nil => simp
  | cons Z l ih =>
      rw [expListProduct_cons, ← mul_assoc,
        ih _ (fun Z hmem ↦ hZ Z (by simp [hmem])),
        norm_mul_exp_smul_eq_of_le_one Z B (hZ Z (by simp)) t]

/-- The two exterior half-products preserve the norm of the middle defect. -/
lemma norm_symmetricDefect_eq_of_le_one (l : List A) (G : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (x : ℝ) :
    ‖symmetricDefect l G x‖ = ‖halfDefect l G x + halfDefect l G (-x)‖ := by
  rw [symmetricDefect_eq_halfDefect_add,
    norm_mul_expListProduct_eq_of_le_one l.reverse _
      (fun Z hmem ↦ hZ Z (by simpa using hmem)),
    norm_expListProduct_mul_eq_of_le_one l _ hZ]

/-- Integrating the positive even polynomial gives the two local error powers,
with an absolute value accounting for either interval orientation. -/
lemma abs_integral_localError_polynomial_le (N C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (h : ℝ) :
    |∫ x in 0..h, 5 * |x| ^ 4 * N + 7 * C * |x| ^ 6| ≤ |h| ^ 5 * N + |h| ^ 7 * C := by
  have h4 : Even (4 : ℕ) := by decide
  have h6 : Even (6 : ℕ) := by decide
  simp_rw [h4.pow_abs, h6.pow_abs]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ ↦ 5 * x ^ 4 * N)).intervalIntegrable 0 h)
    ((by fun_prop : Continuous (fun x : ℝ ↦ 7 * C * x ^ 6)).intervalIntegrable 0 h),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num
  calc
    _ = |h ^ 5 * N + C * h ^ 7| := by
      congr 1
      ring
    _ ≤ |h ^ 5 * N| + |C * h ^ 7| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_pow, abs_of_nonneg hN,
      abs_mul, abs_pow, abs_of_nonneg hC, mul_comm C]

/-- **Local symmetric product error.** A fourth-degree middle defect with a
sixth-degree remainder gives the sharp unsplit fifth-degree coefficient. -/
theorem norm_symmetricExpProduct_sub_exp_le (l : List A) (G L : A) (C : ℝ)
    (hC : 0 ≤ C) (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hT : ∀ x : ℝ, ‖halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L‖ ≤
      7 * C * |x| ^ 6) (h : ℝ) :
    ‖symmetricExpProduct l h - exp (h • G)‖ ≤ |h| ^ 5 * ‖L‖ + |h| ^ 7 * C := by
  rw [symmetricExpProduct_sub_exp_eq_integral]
  calc
    _ ≤ |∫ x in 0..h, 5 * |x| ^ 4 * ‖L‖ + 7 * C * |x| ^ 6| := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      · rw [ae_restrict_iff' measurableSet_uIoc]
        filter_upwards with x _
        rw [norm_mul_exp_smul_eq_of_le_one G _ hG,
          norm_exp_smul_mul_eq_of_le_one G _ hG,
          norm_symmetricDefect_eq_of_le_one l G hZ]
        calc
          _ ≤ ‖halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L‖ +
              ‖(5 * x ^ 4) • L‖ := norm_le_norm_sub_add _ _
          _ ≤ 7 * C * |x| ^ 6 + 5 * |x| ^ 4 * ‖L‖ := by
            gcongr
            · exact hT x
            · simp [norm_smul, Real.norm_eq_abs]
          _ = _ := add_comm _ _
      · exact (by fun_prop : Continuous
          (fun x : ℝ ↦ 5 * |x| ^ 4 * ‖L‖ + 7 * C * |x| ^ 6)).intervalIntegrable 0 h
    _ ≤ _ := abs_integral_localError_polynomial_le ‖L‖ C (norm_nonneg _) hC h

/-- The grouped finite remainder controls the even middle defect without
splitting any recursively combined coefficient inside its norm. -/
theorem norm_halfDefect_add_sub_sum_le {s : ℕ} (Z : Fin s → A) (G : A)
    (hZ : ∀ (i : Fin s) (t : ℝ), ‖exp (t • Z i)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖halfDefect (List.ofFn Z) G x + halfDefect (List.ofFn Z) G (-x) -
      ∑ k ∈ range p, (x ^ k + (-x) ^ k) •
        groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) k‖ ≤
      2 * |x| ^ p * groupedConjBound (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) p := by
  let c := groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G)
  let B := groupedConjBound (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) p
  have hb (t : ℝ) :
      ‖halfDefect (List.ofFn Z) G t - ∑ k ∈ range p, t ^ k • c k‖ ≤ |t| ^ p * B := by
    rw [halfDefect_eq_groupedConj]
    exact norm_groupedConj_sub_sum_le _ _ _
      (fun i u ↦ by simpa only [smul_neg, neg_smul] using hZ i (-u)) p hp t
  change ‖_ + _ - ∑ k ∈ range p, (x ^ k + (-x) ^ k) • c k‖ ≤ 2 * |x| ^ p * B
  simp_rw [add_smul]
  rw [sum_add_distrib]
  rw [show halfDefect (List.ofFn Z) G x + halfDefect (List.ofFn Z) G (-x) -
      ((∑ k ∈ range p, x ^ k • c k) + ∑ k ∈ range p, (-x) ^ k • c k) =
      (halfDefect (List.ofFn Z) G x - ∑ k ∈ range p, x ^ k • c k) +
        (halfDefect (List.ofFn Z) G (-x) - ∑ k ∈ range p, (-x) ^ k • c k) by abel]
  calc
    _ ≤ ‖halfDefect (List.ofFn Z) G x - ∑ k ∈ range p, x ^ k • c k‖ +
        ‖halfDefect (List.ofFn Z) G (-x) - ∑ k ∈ range p, (-x) ^ k • c k‖ := norm_add_le _ _
    _ ≤ |x| ^ p * B + |-x| ^ p * B := add_le_add (hb x) (hb (-x))
    _ = _ := by
      rw [abs_neg]
      ring

/-- The even polynomial through degree five is determined by its three even coefficients. -/
lemma sum_even_pow_smul_eq_quartic {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : ℕ → E) (L : E)
    (h0 : c 0 = 0) (h2 : c 2 = 0) (h4 : c 4 = (5 / 2 : ℝ) • L) (x : ℝ) :
    (∑ k ∈ range 6, (x ^ k + (-x) ^ k) • c k) = (5 * x ^ 4) • L := by
  simp only [sum_range_succ, sum_range_zero, h0, h2, h4]
  module

/-- The grouped sixth-order defect remainder gives the local seventh-order
constant `2 * groupedConjBound / 7`, retaining the complete fifth-degree term. -/
theorem norm_symmetricExpProduct_sub_exp_le_grouped {s : ℕ} (Z : Fin s → A) (G L : A)
    (hZ : ∀ (i : Fin s) (t : ℝ), ‖exp (t • Z i)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (h0 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 0 = 0)
    (h2 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 2 = 0)
    (h4 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 4 = (5 / 2 : ℝ) • L)
    (h : ℝ) :
    ‖symmetricExpProduct (List.ofFn Z) h - exp (h • G)‖ ≤
      |h| ^ 5 * ‖L‖ + |h| ^ 7 *
        (2 * groupedConjBound (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 6 / 7) := by
  apply norm_symmetricExpProduct_sub_exp_le
  · exact div_nonneg (mul_nonneg (by norm_num) (groupedConjBound_nonneg ..)) (by norm_num)
  · intro z hz t
    rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩
    exact hZ i t
  · exact hG
  · intro x
    have hb := norm_halfDefect_add_sub_sum_le Z G hZ 6 (by norm_num) x
    rw [sum_even_pow_smul_eq_quartic _ L h0 h2 h4] at hb
    convert hb using 1
    ring

end FQFP
