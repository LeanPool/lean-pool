/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeProgressionRearrangement
public import LeanPool.NairTenenbaum.Hooley.HooleyPrimeShortSum

/-! # Dyadic averages reduced to one reciprocal Hooley mean

The finite rearrangements and proved short-sum theorems reduce both
Corollaries 5 and 9 to `hooleyRootSum X 1 x`. No asymptotic estimate for that
mean is assumed in these bounds.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

@[simp] theorem hooleyPolynomialSum_X_one (x y : ℝ) :
    hooleyPolynomialSum (X : ℤ[X]) 1 x y =
      ∑ n ∈ shortInterval x y, (hooleyDelta n : ℝ) := by
  simp [hooleyPolynomialSum]

/-- The floor-sum average has a single reciprocal Hooley mean as its only
remaining analytic input, with a constant independent of the divisor cutoff. -/
theorem exists_dyadicFloorSum_root_bound {α : ℝ} (hα : 0 < α) :
    ∃ x₀ C : ℝ, 0 < x₀ ∧ 0 < C ∧ ∀ D x y : ℝ,
      0 < D → x₀ < x → x ^ α ≤ y → y ≤ x →
      dyadicFloorSum D x y ≤ C * (y / Real.log x * hooleyRootSum (X : ℤ[X]) 1 x) := by
  obtain ⟨x₀, C, hx₀, hC, H⟩ := exists_hooleyPolynomialSum_root_bound
    (X : ℤ[X]) noFixedPrimeDivisor_X (by simp) hα (t := 1) zero_lt_one
  refine ⟨max x₀ 2, C, lt_of_lt_of_le (by norm_num) (le_max_right _ _), hC, ?_⟩
  intro D x y hD hx hy hyx
  have hx₂ : 2 < x := (le_max_right _ _).trans_lt hx
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) α).trans hy
  have Hshort := H x y ((le_max_left _ _).trans_lt hx) hy hyx
  rw [hooleyPolynomialSum_X_one] at Hshort
  have hmean : 0 ≤ hooleyRootSum (X : ℤ[X]) 1 x := by
    unfold hooleyRootSum
    exact sum_nonneg fun n _ => by positivity
  calc
    _ ≤ ∑ n ∈ shortInterval x y, (hooleyDelta n : ℝ) :=
      dyadicFloorSum_le_hooley_sum hD (by linarith) hy₀
    _ ≤ C * (y * sieveProduct (X : ℤ[X]) x * hooleyRootSum (X : ℤ[X]) 1 x) := Hshort
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply mul_le_mul_of_nonneg_right _ hmean
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
        (sieveProduct_X_le_inv_log (by linarith : 1 < x)) hy₀

/-- The averaged progression count has the same reciprocal Hooley mean,
with an additional reciprocal logarithm and explicit residue dependence. -/
theorem exists_dyadicPrimeProgressionSum_root_bound {α : ℝ} (hα : 0 < α) :
    ∃ x₀ C : ℝ, 0 < x₀ ∧ 0 < C ∧ ∀ a : ℤ, a ≠ 0 → ∀ K x y : ℝ,
      0 < K → x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ α ≤ y → y ≤ x →
      dyadicPrimeProgressionSum K a x y ≤ C *
        (((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
          hooleyRootSum (X : ℤ[X]) 1 x) := by
  obtain ⟨x₀, C, hx₀, hC, H⟩ :=
    exists_hooleyPrimeSum_root_bound_uniform_shift hα (t := 1) zero_lt_one
  refine ⟨x₀, C, hx₀, hC, ?_⟩
  intro a ha K x y hK hx hax hy hyx
  have haabs : (a : ℝ) ≤ (a.natAbs : ℝ) := by
    have Hcast : (a : ℝ) ≤ ((a.natAbs : ℤ) : ℝ) :=
      Int.cast_le.mpr (Int.le_natAbs : a ≤ a.natAbs)
    simpa only [Int.cast_natCast] using Hcast
  have hx₁ : 0 ≤ x := hx₀.le.trans hx.le
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hx₁ α).trans hy
  have Hshort := H (-a) (neg_ne_zero.mpr ha) x y hx
    (by simpa only [Int.natAbs_neg] using hax) hy hyx
  have Hrearr := dyadicPrimeProgressionSum_le_hooley_sum a hK hx₁ hy₀ (haabs.trans hax)
  apply Hrearr.trans
  simpa only [hooleyPrimeSum, Real.rpow_one, Int.natAbs_neg, sub_eq_add_neg] using Hshort

end NairTenenbaum
