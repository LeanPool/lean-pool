/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.FiniteProbability
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring


/-!
# Scalar Chernoff bounds for geometric-product potentials

These finite-product inequalities are independent of a stochastic model.
`GeometricDomination` supplies the adaptive-process domination needed to
interpret the final bound as a failure probability.
-/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.GeometricTailBounds

open Finset

/-- A quadratic upper bound for a geometric-series factor. -/
theorem reciprocal_one_sub_le_quadratic (x : ℝ) (_hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
  have hden : 0 < 1 - x := by linarith
  rw [← one_div]
  apply (div_le_iff₀ hden).2
  have hproduct := mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)
  nlinarith

/-- The same reciprocal factor is bounded by a quadratic exponential. -/
theorem reciprocal_one_sub_le_exp (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (x + 2 * x ^ 2) := by
  calc
    _ ≤ 1 + x + 2 * x ^ 2 := reciprocal_one_sub_le_quadratic x hx hxhalf
    _ ≤ Real.exp (x + 2 * x ^ 2) := by
      have := Real.add_one_le_exp (x + 2 * x ^ 2)
      linarith

/-- Each geometric PGF factor has an exponential bound controlled by `1/p`. -/
theorem geometric_factor_le_exp (p lam : ℝ) (hp : (1 / 4 : ℝ) ≤ p)
    (hlam : 0 ≤ lam) (hlammax : lam ≤ 1 / 8) :
    (1 - lam / p)⁻¹ ≤ Real.exp ((lam + 8 * lam ^ 2) / p) := by
  have hpPos : 0 < p := by linarith
  have hx : 0 ≤ lam / p := div_nonneg hlam hpPos.le
  have hxhalf : lam / p ≤ 1 / 2 := by
    apply (div_le_iff₀ hpPos).2
    linarith
  have hexp : lam / p + 2 * (lam / p) ^ 2 ≤ (lam + 8 * lam ^ 2) / p := by
    have hinv : 1 / p ≤ 4 := by
      apply (div_le_iff₀ hpPos).2
      linarith
    have hsq : (1 / p) ^ 2 ≤ 4 / p := by
      have hmul := mul_le_mul_of_nonneg_right hinv
        (show 0 ≤ 1 / p by positivity)
      convert hmul using 1 <;> ring
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * lam ^ 2 by positivity)
    have hmuladd := add_le_add_left hmul (lam / p)
    convert hmuladd using 1 <;> ring
  exact (reciprocal_one_sub_le_exp _ hx hxhalf).trans (Real.exp_le_exp.mpr hexp)

/-- The product of the geometric factors is bounded using their reciprocal sum. -/
theorem product_le_exp {α : Type*} (indices : Finset α) (p : α → ℝ) (lam M : ℝ)
    (hp : ∀ i ∈ indices, (1 / 4 : ℝ) ≤ p i)
    (hlam : 0 ≤ lam) (hlammax : lam ≤ 1 / 8)
    (hmean : (∑ i ∈ indices, 1 / p i) ≤ M) :
    (∏ i ∈ indices, (1 - lam / p i)⁻¹) ≤ Real.exp ((lam + 8 * lam ^ 2) * M) := by
  have hprod : (∏ i ∈ indices, (1 - lam / p i)⁻¹) ≤
      ∏ i ∈ indices, Real.exp ((lam + 8 * lam ^ 2) / p i) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have hpPos : 0 < p i := by have := hp i hi; linarith
      have hratio : lam / p i ≤ 1 / 2 := by
        apply (div_le_iff₀ hpPos).2
        have := hp i hi
        linarith
      exact inv_nonneg.mpr (by linarith)
    · intro i hi
      exact geometric_factor_le_exp _ _ (hp i hi) hlam hlammax
  calc
    _ ≤ ∏ i ∈ indices, Real.exp ((lam + 8 * lam ^ 2) / p i) := hprod
    _ = Real.exp ((lam + 8 * lam ^ 2) * (∑ i ∈ indices, 1 / p i)) := by
      rw [← Real.exp_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ Real.exp ((lam + 8 * lam ^ 2) * M) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hmean (by positivity)

/-- The Bernoulli decay term is at most the corresponding exponential. -/
theorem decay_le_exp (lam : ℝ) (T : ℕ) (hlammax : lam ≤ 1) :
    (1 - lam) ^ T ≤ Real.exp (-lam * (T : ℝ)) := by
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1 - lam by linarith)
    (Real.one_sub_le_exp_neg lam) T
  calc
    _ ≤ Real.exp (-lam) ^ T := hpow
    _ = Real.exp (-lam * (T : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A finite-product Chernoff bound before choosing the exponential parameter. -/
theorem product_decay_le_exp {α : Type*} (indices : Finset α) (p : α → ℝ)
    (lam M : ℝ) (T : ℕ) (hp : ∀ i ∈ indices, (1 / 4 : ℝ) ≤ p i)
    (hlam : 0 ≤ lam) (hlammax : lam ≤ 1 / 8)
    (hmean : (∑ i ∈ indices, 1 / p i) ≤ M) :
    (∏ i ∈ indices, (1 - lam / p i)⁻¹) * (1 - lam) ^ T ≤
      Real.exp ((lam + 8 * lam ^ 2) * M - lam * (T : ℝ)) := by
  calc
    _ ≤ Real.exp ((lam + 8 * lam ^ 2) * M) * Real.exp (-lam * (T : ℝ)) := by
      apply mul_le_mul (product_le_exp indices p lam M hp hlam hlammax hmean)
        (decay_le_exp lam T (by linarith))
      · exact pow_nonneg (by linarith) _
      · exact (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Parameter used for a deviation `s` above the reciprocal-sum bound `M`. -/
def chosenTilt (M s : ℝ) : ℝ := s / (16 * (M + s))

theorem chosenTilt_bounds (M s : ℝ) (hM : 0 < M) (hs : 0 ≤ s) :
    0 ≤ chosenTilt M s ∧ chosenTilt M s ≤ 1 / 16 := by
  have hden : 0 < 16 * (M + s) := by positivity
  constructor
  · exact div_nonneg hs hden.le
  · apply (div_le_iff₀ hden).2
    linarith

/-- The chosen tilt is strictly below every permitted progress rate. -/
theorem chosenTilt_lt_rate (M s p : ℝ) (hM : 0 < M) (hs : 0 ≤ s)
    (hp : (1 / 4 : ℝ) ≤ p) : chosenTilt M s < p := by
  have := (chosenTilt_bounds M s hM hs).2
  linarith

/-- The chosen tilt gives a quadratic-over-linear deviation exponent. -/
theorem chosenTilt_exponent (M s T : ℝ) (hM : 0 < M) (hs : 0 ≤ s)
    (hT : M + s ≤ T) :
    (chosenTilt M s + 8 * (chosenTilt M s) ^ 2) * M - chosenTilt M s * T ≤
      -(s ^ 2 / (32 * (M + s))) := by
  have hden : 0 < M + s := by linarith
  have hlam := (chosenTilt_bounds M s hM hs).1
  have htime := mul_le_mul_of_nonneg_left hT hlam
  have hlocal : (chosenTilt M s + 8 * (chosenTilt M s) ^ 2) * M -
      chosenTilt M s * (M + s) + s ^ 2 / (32 * (M + s)) =
      -(s ^ 3 / (32 * (M + s) ^ 2)) := by
    unfold chosenTilt
    field_simp
    ring
  have hnonneg : 0 ≤ s ^ 3 / (32 * (M + s) ^ 2) := by positivity
  linarith

/-- Finite geometric-product Chernoff bound with leading term `M`. -/
theorem sharp_tail_bound {α : Type*} (indices : Finset α) (p : α → ℝ)
    (M s : ℝ) (T : ℕ) (hM : 0 < M) (hs : 0 ≤ s)
    (hp : ∀ i ∈ indices, (1 / 4 : ℝ) ≤ p i)
    (hmean : (∑ i ∈ indices, 1 / p i) ≤ M) (hT : M + s ≤ (T : ℝ)) :
    (∏ i ∈ indices, (1 - chosenTilt M s / p i)⁻¹) * (1 - chosenTilt M s) ^ T ≤
      Real.exp (-(s ^ 2 / (32 * (M + s)))) := by
  obtain ⟨hlam, hlammax⟩ := chosenTilt_bounds M s hM hs
  exact (product_decay_le_exp indices p _ M T hp hlam (by linarith) hmean).trans
    (Real.exp_le_exp.mpr (chosenTilt_exponent M s T hM hs hT))

/-- An explicit deviation of order `sqrt(M L) + L`. -/
def confidenceDeviation (M L : ℝ) : ℝ := 8 * Real.sqrt (M * L) + 64 * L

theorem confidenceDeviation_nonneg (M L : ℝ) (_hM : 0 ≤ M) (hL : 0 ≤ L) :
    0 ≤ confidenceDeviation M L := by
  unfold confidenceDeviation
  positivity

/-- The explicit deviation makes the quadratic-over-linear exponent at least `L`. -/
theorem confidenceDeviation_exponent (M L : ℝ) (hM : 0 < M) (hL : 0 ≤ L) :
    L ≤ (confidenceDeviation M L) ^ 2 / (32 * (M + confidenceDeviation M L)) := by
  have hs := confidenceDeviation_nonneg M L hM.le hL
  apply (le_div_iff₀ (show 0 < 32 * (M + confidenceDeviation M L) by positivity)).2
  have hroot := Real.sqrt_nonneg (M * L)
  have hsquare := Real.sq_sqrt (mul_nonneg hM.le hL)
  have hproduct := mul_nonneg hL hroot
  unfold confidenceDeviation
  nlinarith [sq_nonneg L, mul_nonneg hM.le hL]

/-- A square-root-plus-linear budget achieves tail `exp(-L)`. -/
theorem confidence_exp_bound {α : Type*} (indices : Finset α) (p : α → ℝ)
    (M L : ℝ) (T : ℕ) (hM : 0 < M) (hL : 0 ≤ L)
    (hp : ∀ i ∈ indices, (1 / 4 : ℝ) ≤ p i)
    (hmean : (∑ i ∈ indices, 1 / p i) ≤ M)
    (hT : M + confidenceDeviation M L ≤ (T : ℝ)) :
    (∏ i ∈ indices, (1 - chosenTilt M (confidenceDeviation M L) / p i)⁻¹) *
        (1 - chosenTilt M (confidenceDeviation M L)) ^ T ≤ Real.exp (-L) := by
  apply (sharp_tail_bound indices p M _ T hM
    (confidenceDeviation_nonneg M L hM.le hL) hp hmean hT).trans
  exact Real.exp_le_exp.mpr (neg_le_neg (confidenceDeviation_exponent M L hM hL))

/-- The numerical confidence guarantee with `L = log(1/δ)`. -/
theorem confidence_tail_bound {α : Type*} (indices : Finset α) (p : α → ℝ)
    (M δ : ℝ) (T : ℕ) (hM : 0 < M) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (hp : ∀ i ∈ indices, (1 / 4 : ℝ) ≤ p i)
    (hmean : (∑ i ∈ indices, 1 / p i) ≤ M)
    (hT : M + confidenceDeviation M (Real.log (1 / δ)) ≤ (T : ℝ)) :
    (∏ i ∈ indices, (1 - chosenTilt M (confidenceDeviation M (Real.log (1 / δ))) / p i)⁻¹) *
        (1 - chosenTilt M (confidenceDeviation M (Real.log (1 / δ)))) ^ T ≤ δ := by
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).2
    simpa using hδmax
  calc
    _ ≤ Real.exp (-Real.log (1 / δ)) :=
      confidence_exp_bound indices p M _ T hM hlog hp hmean hT
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; simp

/-- A natural-number budget with leading term `M`. -/
def confidenceBudget (M δ : ℝ) : ℕ :=
  ⌈M + confidenceDeviation M (Real.log (1 / δ))⌉₊

theorem confidenceBudget_sufficient {α : Type*} (indices : Finset α) (p : α → ℝ)
    (M δ : ℝ) (hM : 0 < M) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (hp : ∀ i ∈ indices, (1 / 4 : ℝ) ≤ p i)
    (hmean : (∑ i ∈ indices, 1 / p i) ≤ M) :
    (∏ i ∈ indices, (1 - chosenTilt M (confidenceDeviation M (Real.log (1 / δ))) / p i)⁻¹) *
        (1 - chosenTilt M (confidenceDeviation M (Real.log (1 / δ)))) ^
          confidenceBudget M δ ≤ δ := by
  apply confidence_tail_bound indices p M δ _ hM hδ hδmax hp hmean
  exact Nat.le_ceil _

/-- The exact learner's reciprocal progress sum is at most `2n + 4`, even
when its current rank `r` is smaller than the qubit count `n`. -/
theorem exact_rate_sum_bound (r n : ℕ) (hrn : r ≤ n) :
    (∑ j ∈ Finset.range r,
      1 / FiniteProbability.progressProbability (j + 1)) ≤ 2 * (n : ℝ) + 4 := by
  have hsum := FiniteProbability.reciprocal_sum_lt_two_n_add_four r
  have hrnReal : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hid : (∑ j ∈ Finset.range r,
      1 / FiniteProbability.progressProbability (j + 1)) =
      ∑ j ∈ Finset.range r, 2 / (1 - (1 / 2 : ℝ) ^ (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp [FiniteProbability.progressProbability]
  rw [hid]
  linarith

end LeanPool.SingleCopyStabilizer.GeometricTailBounds
