/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.PrimeRootMertens
public import LeanPool.NairTenenbaum.Polynomials.PolynomialSmoothPrimeBound

/-! # The small-prime logarithmic mass with a linear error -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Real

theorem exists_polynomialSmoothLogMass_linear_error {Q : ℤ[X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) {β C : ℝ} (hβ : 0 < β) (hC : 1 ≤ C) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x y : ℝ, x₀ < x → x ^ β ≤ y → y ≤ x →
      polynomialSmoothLogMass Q x y (C * y) ≤ y * Real.log y + B * y := by
  have hprim := hQ.isPrimitive hdeg.ne'
  have hirr := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hQ
  have hD : Q.discr ≠ 0 := discr_ne_zero_of_separable_map hirr.separable
  obtain ⟨x₀, E, hx₀, hE, HE⟩ := exists_polynomialSmoothLogMass_prime_bound hprim hD hβ hC
  obtain ⟨D, hD0, HD⟩ := exists_irreducible_primeRootLogSum_bound hQ hdeg
  have hlogC := Real.log_nonneg hC
  refine ⟨x₀, 1 + 2 * (Real.log C + D) + E, hx₀, by positivity, fun x y hx hy hyx => ?_⟩
  have hx1 : 1 < x := hx₀.trans hx
  have hy1 : 1 ≤ y := (Real.one_le_rpow hx1.le hβ.le).trans hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCy : 1 ≤ C * y := hy1.trans (le_mul_of_one_le_left hy0.le hC)
  have HS := HE x y hx hy hyx
  have HP := mul_le_mul_of_nonneg_left (HD (C * y) hCy) (show 0 ≤ y + 1 by linarith)
  rw [Real.log_mul hC0.ne' hy0.ne'] at HP
  have Hlog : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  have Hconst : (y + 1) * (Real.log C + D) ≤ 2 * y * (Real.log C + D) :=
    mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (Real.log_nonneg hC) hD0)
  nlinarith

end NairTenenbaum
