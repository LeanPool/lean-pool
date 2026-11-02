/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyShortSum
public import LeanPool.NairTenenbaum.Results.CorollarySeven

/-! # Hooley moments at shifted primes

The short-sum reduction for Corollary 8, with the shift dependence kept
explicit. The remaining mean is the ordinary reciprocal Hooley moment.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The sum of Hooley's function over the prescribed shifted prime values. -/
noncomputable def hooleyPrimeSum (a : ℤ) (t x y : ℝ) : ℝ :=
  ∑ p ∈ (shortInterval x y).filter Nat.Prime,
    (hooleyDelta ((p : ℤ) + a).natAbs : ℝ) ^ t

theorem shiftedPrimeSum_hooley_rpow (a : ℤ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    shiftedPrimeSum a (fun v => hooleyMap v ^ t) x y = hooleyPrimeSum a t x y := by
  unfold shiftedPrimeSum hooleyPrimeSum
  simp_rw [extend_hooley_rpow ht]

theorem hooleyRootSum_X (t x : ℝ) :
    hooleyRootSum (X : ℤ[X]) t x =
      ∑ n ∈ positiveUpTo x, (hooleyDelta n : ℝ) ^ t / (n : ℝ) := by
  simp only [hooleyRootSum, rootCount_X, Nat.cast_one, div_eq_mul_inv, one_mul]

/-- Uniform shifted-prime moment bound for an arbitrary positive interval
exponent. Both constants precede the nonzero integer shift. -/
theorem exists_hooleyPrimeSum_root_bound_with_height {α t δ : ℝ}
    (hα : 0 < α) (ht : 0 < t) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ a : ℤ, a ≠ 0 → ∀ x y : ℝ,
      c₀ * (a.natAbs : ℝ) ^ δ < x → x ^ α ≤ y → y ≤ x →
      hooleyPrimeSum a t x y ≤ C *
        (((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
          hooleyRootSum (X : ℤ[X]) t x) := by
  let ε : ℝ := min α 1 / 16
  have hε : 0 < ε := div_pos (lt_min hα zero_lt_one) (by norm_num)
  have hεsmall : ε < 1 / 8 := by dsimp [ε]; linarith [min_le_right α 1]
  have hεα : 4 * ε ≤ α := by dsimp [ε]; linarith [min_le_left α 1]
  obtain ⟨B, hB, hF⟩ := hooley_rpow_admissible
    (div_pos (mul_pos hε hδ) (by norm_num : (0 : ℝ) < 3)) ht
  obtain ⟨c, hc, C, hC, H⟩ := corollarySeven ((2 : ℝ) ^ t) B ε δ
    (Real.one_le_rpow (by norm_num) ht.le) hB hε hεsmall hδ hδ₁
  refine ⟨max c 2, C, lt_of_lt_of_le (by norm_num) (le_max_right _ _), hC, ?_⟩
  intro a ha x y hx hy hyx
  have ha₁ : (1 : ℝ) ≤ a.natAbs := by exact_mod_cast Int.natAbs_pos.mpr ha
  have haδ : 1 ≤ (a.natAbs : ℝ) ^ δ := Real.one_le_rpow ha₁ hδ.le
  have hx₁ : 1 ≤ x := by
    have Hx : 2 ≤ max c 2 * (a.natAbs : ℝ) ^ δ :=
      (le_max_right _ _).trans (le_mul_of_one_le_right (by positivity) haδ)
    linarith
  have hheight : c * (a.natAbs : ℝ) ^ δ < x := by
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans_lt hx
  have Hbound := H a ha (fun v => hooleyMap v ^ t) (by simpa using hF) x y hheight
    ((Real.rpow_le_rpow_of_exponent_le hx₁ hεα).trans hy) hyx
  rw [shiftedPrimeSum_hooley_rpow a ht] at Hbound
  simpa only [shiftedPrimeMainTerm, hooleyRootSum_X, hooleyMap] using Hbound

/-- The full shift range in Corollary 8: the threshold depends only on the
interval exponent and moment order, and every `1≤|a|≤x` is allowed. -/
theorem exists_hooleyPrimeSum_root_bound_uniform_shift {α t : ℝ}
    (hα : 0 < α) (ht : 0 < t) :
    ∃ x₀ C : ℝ, 0 < x₀ ∧ 0 < C ∧ ∀ a : ℤ, a ≠ 0 → ∀ x y : ℝ,
      x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ α ≤ y → y ≤ x →
      hooleyPrimeSum a t x y ≤ C *
        (((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
          hooleyRootSum (X : ℤ[X]) t x) := by
  obtain ⟨c, C, hc, hC, H⟩ := exists_hooleyPrimeSum_root_bound_with_height hα ht
    (δ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨c ^ 2 + 1, C, by positivity, hC, ?_⟩
  intro a ha x y hx hax hy hyx
  have hx₀ : 0 < x := by nlinarith [sq_nonneg c]
  have hsqrt : c < Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx₀.le, Real.sqrt_nonneg x]
  apply H a ha x y _ hy hyx
  rw [← Real.sqrt_eq_rpow]
  calc
    c * Real.sqrt (a.natAbs : ℝ) ≤ c * Real.sqrt x :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hax) hc.le
    _ < Real.sqrt x * Real.sqrt x := mul_lt_mul_of_pos_right hsqrt (Real.sqrt_pos.mpr hx₀)
    _ = x := Real.mul_self_sqrt hx₀.le

end NairTenenbaum
