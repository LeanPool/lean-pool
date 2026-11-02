/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.DivisorSums.PolynomialDivisorWindowCount
public import LeanPool.NairTenenbaum.Smooth.SmoothLogHigherPowers

/-! # Small-prime logarithmic mass reduced to the weighted prime-root sum -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Real Finset

theorem exists_polynomialSmoothLogMass_prime_bound {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    (hD : Q.discr ≠ 0) {β C : ℝ} (hβ : 0 < β) (hC : 1 ≤ C) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x y : ℝ, x₀ < x → x ^ β ≤ y → y ≤ x →
      polynomialSmoothLogMass Q x y (C * y) ≤ (y + 1) * primeRootLogSum Q (C * y) + B * y := by
  let A : ℝ := max 1 ((polynomialHeight Q : ℝ) * (Q.natDegree + 1) * 2 ^ Q.natDegree)
  have hA : 1 ≤ A := le_max_left _ _
  obtain ⟨x₁, E, hx₁, hE, HE⟩ := exists_smoothLogRootError_linear_bound hQ hD hA hC hβ Q.natDegree
  obtain ⟨D, hD₀, HD⟩ := exists_smoothLogRootMain_le_prime_sum hQ hD
  obtain ⟨x₂, _, HQ⟩ := exists_polynomial_eval_nonzero_on_shortInterval hQ.ne_zero
  refine ⟨max x₁ x₂, 2 * D + E, hx₁.trans_le (le_max_left _ _), by
    positivity, fun x y hx hy hyx => ?_⟩
  have hx₁' := (le_max_left _ _).trans_lt hx
  have hx₂' := (le_max_right _ _).trans_lt hx
  have hxone : 1 < x := hx₁.trans hx₁'
  have hyone : 1 ≤ y := (Real.one_le_rpow hxone.le hβ.le).trans hy
  have hy₀ : 0 ≤ y := by linarith
  have hsize : ∀ n ∈ shortInterval x y, ((Q.eval (n : ℤ)).natAbs : ℝ) ≤ A * x ^ Q.natDegree := by
    intro n hn
    have hnhi : (n : ℝ) ≤ 2 * x := by
      have H := (Nat.le_floor_iff (by linarith : 0 ≤ x + y)).mp (mem_Ioc.mp hn).2
      linarith
    have H := eval_natAbs_le_height_real Q hxone.le (n := (n : ℤ)) (by
      simpa only [Int.natAbs_natCast] using hnhi)
    have HA := mul_le_mul_of_nonneg_right (le_max_right 1
      ((polynomialHeight Q : ℝ) * (Q.natDegree + 1) * 2 ^ Q.natDegree))
      (pow_nonneg (by linarith : 0 ≤ x) Q.natDegree)
    rw [mul_pow] at H
    apply H.trans
    convert HA using 1; ring
  have HS := polynomialSmoothLogMass_le_log_cutoff Q (by linarith : 0 ≤ x) hy₀
    (mul_nonneg (by linarith : 0 ≤ C) hy₀) (HQ x y hx₂') hsize
  have HM := mul_le_mul_of_nonneg_left (HD (C * y) (primePowerLogCutoff (A * x ^ Q.natDegree)))
    (show 0 ≤ y + 1 by linarith)
  have HER := HE x y hx₁' hy
  have HDy : D * (y + 1) ≤ 2 * D * y := by nlinarith
  nlinarith

end NairTenenbaum
