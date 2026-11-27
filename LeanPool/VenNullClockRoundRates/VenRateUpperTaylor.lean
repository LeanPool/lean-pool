/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform factorial remainder for the exponential kernel on a unit height interval. -/

@[expose] public section
open Filter Finset MeasureTheory

namespace VenRateUpper

theorem abs_exp_sub_sum_le_factorial {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    |Real.exp t - ∑ j ∈ range n, t ^ j / (j.factorial : ℝ)| ≤
      t ^ n / (n.factorial : ℝ) * Real.exp t := by
  classical
  let term (j : ℕ) := t ^ j / (j.factorial : ℝ)
  have hs : HasSum term (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have hshift : Summable (fun j : ℕ => term (j + n)) :=
    (summable_nat_add_iff n).mpr hs.summable
  have hsplit : Real.exp t - (∑ j ∈ range n, term j) = ∑' j, term (j + n) := by
    linarith [hs.summable.sum_add_tsum_nat_add n, hs.tsum_eq]
  change |Real.exp t - (∑ j ∈ range n, term j)| ≤ term n * Real.exp t
  rw [hsplit, abs_of_nonneg (tsum_nonneg (fun j => by dsimp [term]; positivity)), ← hs.tsum_eq]
  rw [← tsum_mul_left]
  refine hshift.tsum_le_tsum (fun j => ?_) (hs.summable.mul_left (term n))
  have hd : (j.factorial * n.factorial : ℕ) ≤ (j + n).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add j n)
  have hdc : (j.factorial : ℝ) * (n.factorial : ℝ) ≤ ((j + n).factorial : ℝ) := by
    exact_mod_cast hd
  dsimp [term]
  rw [pow_add, div_mul_div_comm, mul_comm (t ^ n) (t ^ j),
    mul_comm (n.factorial : ℝ) (j.factorial : ℝ)]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdc

theorem exponential_integral_le_of_zero_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F p : Ω → ℝ)
    (hF : Measurable F) (rangeF : ∀ y, F y ∈ Set.Icc (0 : ℝ) 1)
    (hp : Integrable p μ) {A : ℝ} (hA : 0 ≤ A) (supP : ∀ y, |p y| ≤ A)
    (n : ℕ) (moments : ∀ j < n, (∫ y, p y * F y ^ j ∂μ) = 0)
    {x a : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) :
    |∫ y, p y * Real.exp (x * F y) ∂μ| ≤
      A * (a ^ n / (n.factorial : ℝ) * Real.exp a) := by
  let E (y : Ω) := Real.exp (x * F y)
  let T (j : ℕ) (y : Ω) := (x ^ j / (j.factorial : ℝ)) * (F y) ^ j
  have hE : Integrable (fun y => p y * E y) μ := by
    apply hp.mul_bdd (c := Real.exp a)
      (Real.continuous_exp.measurable.comp (measurable_const.mul hF)).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun y => ?_
    change ‖Real.exp (x * F y)‖ ≤ Real.exp a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (mul_le_of_le_one_right hx (rangeF y).2).trans hxa
  have hTi (j : ℕ) : Integrable (fun y => p y * T j y) μ := by
    have hPow : Integrable (fun y => p y * F y ^ j) μ := by
      apply hp.mul_bdd (c := 1) (hF.pow_const j).aestronglyMeasurable
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (rangeF y).1 _)]
      simpa only [one_pow] using pow_le_pow_left₀ (rangeF y).1 (rangeF y).2 j
    convert hPow.const_mul (x ^ j / (j.factorial : ℝ)) using 1
    ext y
    dsimp [T]
    ring
  have hTerms :
      Integrable (fun y => p y * ∑ j ∈ range n, T j y) μ := by
    simpa only [Finset.mul_sum] using integrable_finsetSum (range n) (fun j _ => hTi j)
  have hsum : (∫ y, p y * (∑ j ∈ range n, T j y) ∂μ) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ => hTi j)]
    apply Finset.sum_eq_zero
    intro j hj
    calc
      _ = (x ^ j / (j.factorial : ℝ)) * (∫ y, p y * F y ^ j ∂μ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        dsimp [T]
        ring
      _ = 0 := by rw [moments j (mem_range.mp hj), mul_zero]
  have difference :
      (∫ y, p y * (E y - ∑ j ∈ range n, T j y) ∂μ) = ∫ y, p y * E y ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub hE hTerms, hsum, sub_zero]
  rw [← difference]
  refine (abs_integral_le_integral_abs).trans ?_
  calc
    _ ≤ ∫ _ : Ω, A * (a ^ n / (n.factorial : ℝ) * Real.exp a) ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
      have hy0 : 0 ≤ x * F y := mul_nonneg hx (rangeF y).1
      have hyA := (mul_le_of_le_one_right hx (rangeF y).2).trans hxa
      have htail := abs_exp_sub_sum_le_factorial hy0 n
      have sumEq : (∑ j ∈ range n, T j y) = ∑ j ∈ range n, (x * F y) ^ j / (j.factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [T, mul_pow]
        ring
      change |p y * (Real.exp (x * F y) - ∑ j ∈ range n, T j y)| ≤ _
      rw [abs_mul, sumEq]
      refine mul_le_mul (supP y) (htail.trans ?_) (abs_nonneg _) hA
      have ha : 0 ≤ a := hx.trans hxa
      exact mul_le_mul
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hy0 hyA n) (by positivity))
        (Real.exp_le_exp.mpr hyA) (Real.exp_pos _).le
        (div_nonneg (pow_nonneg ha _) (by positivity))
    _ = _ := by simp

end VenRateUpper
