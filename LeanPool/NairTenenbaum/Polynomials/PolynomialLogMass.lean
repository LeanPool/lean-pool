/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialHeight
public import Mathlib.Analysis.Polynomial.Basic

/-! # Quantitative lower logarithmic mass of polynomial values -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset Real Filter

/-- The sum of logarithms of absolute polynomial values on a short interval. -/
noncomputable def polynomialLogMass (Q : ℤ[X]) (x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, Real.log ((Q.eval (n : ℤ)).natAbs : ℝ)

theorem exists_power_le_mul_eval_natAbs {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ n : ℕ, x₀ < n →
      (n : ℝ) ^ Q.natDegree ≤ C * (Q.eval (n : ℤ)).natAbs := by
  let P := Q.map (Int.castRingHom ℝ)
  have hP : P ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hQ
  have hLC : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP)
  obtain ⟨C, hC, HC⟩ := P.isEquivalent_atTop_lead.symm.isBigO.exists_pos
  obtain ⟨z, hz⟩ := eventually_atTop.mp HC.bound
  refine ⟨max 2 z, C / ‖P.leadingCoeff‖, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    div_pos hC hLC, fun n hn => ?_⟩
  have H := hz (n : ℝ) ((le_max_right _ _).trans hn.le)
  have HPdeg : P.natDegree = Q.natDegree := natDegree_map_eq_of_injective (f := Int.castRingHom ℝ)
      Int.cast_injective Q
  have HE : P.eval (n : ℝ) = ((Q.eval (n : ℤ) : ℤ) : ℝ) := by
    simp only [P, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (Int.castRingHom ℝ) (n : ℤ)
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      HPdeg, HE,
    ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] at H
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hLC).mpr
  simpa only [Real.norm_eq_abs, mul_comm _ |P.leadingCoeff|] using H

theorem exists_polynomial_eval_log_lower_bound {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ n : ℕ, x₀ < n →
      Q.eval (n : ℤ) ≠ 0 ∧
        (Q.natDegree : ℝ) * Real.log n - B ≤ Real.log ((Q.eval (n : ℤ)).natAbs : ℝ) := by
  obtain ⟨x₀, C, hx₀, hC, HC⟩ := exists_power_le_mul_eval_natAbs hQ
  refine ⟨x₀, max 0 (Real.log C), hx₀, le_max_left _ _, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by linarith [hx₀.trans hn]
  have H := HC n hn
  have hval : (0 : ℝ) < (Q.eval (n : ℤ)).natAbs := by
    have := (pow_pos hnpos Q.natDegree).trans_le H
    exact (mul_pos_iff_of_pos_left hC).mp this
  have HL := Real.log_le_log (pow_pos hnpos Q.natDegree) H
  rw [Real.log_pow, Real.log_mul hC.ne' hval.ne'] at HL
  refine ⟨Int.natAbs_ne_zero.mp (by exact_mod_cast hval.ne'), ?_⟩
  linarith [le_max_right 0 (Real.log C)]

theorem exists_polynomialLogMass_card_lower_bound {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x y : ℝ, x₀ < x →
      (shortInterval x y).card * ((Q.natDegree : ℝ) * Real.log x - B) ≤ polynomialLogMass Q x y :=
          by
  obtain ⟨x₀, B, hx₀, hB, H⟩ := exists_polynomial_eval_log_lower_bound hQ
  refine ⟨x₀, B, hx₀, hB, fun x y hx => ?_⟩
  have hxpos : 0 < x := by linarith [hx₀.trans hx]
  calc
    _ = ∑ _n ∈ shortInterval x y, ((Q.natDegree : ℝ) * Real.log x - B) := by simp [mul_sub]
    _ ≤ polynomialLogMass Q x y := by
      apply sum_le_sum
      intro n hn
      have hnlo : x < (n : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp hn).1
      have Hn := (H n (hx.trans hnlo)).2
      have HL := mul_le_mul_of_nonneg_left (Real.log_le_log hxpos hnlo.le) (Nat.cast_nonneg
          Q.natDegree)
      linarith

end NairTenenbaum
