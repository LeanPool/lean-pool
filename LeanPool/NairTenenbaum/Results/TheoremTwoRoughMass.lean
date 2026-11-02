/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSmoothLogEstimate

/-! # Quantitative rough logarithmic mass in the Theorem 2 interval -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Real

theorem exists_theoremTwo_roughLogMass_lower_bound {Q : ℤ[X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) {k : ℕ} (hk : Q.natDegree < k) {C : ℝ} (hC : 1 ≤ C) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x : ℝ, x₀ < x →
      let y : ℝ := x ^ ((Q.natDegree : ℝ) / k)
      ((k : ℝ) - 1) * (shortInterval x y).card * Real.log y - B * y ≤
        polynomialRoughLogMass Q x y (C * y) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hdeg.trans hk
  have hk1 : 0 ≤ (k : ℝ) - 1 := by
    have H : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  let β : ℝ := (Q.natDegree : ℝ) / k
  have hβ : 0 < β := div_pos (by exact_mod_cast hdeg) hk0
  have hβ1 : β < 1 := (div_lt_one hk0).mpr (by exact_mod_cast hk)
  obtain ⟨x₁, D, hx₁, hD, HD⟩ := exists_polynomialSmoothLogMass_linear_error hQ hdeg hβ hC
  obtain ⟨x₂, E, hx₂, hE, HE⟩ := exists_polynomialRoughLogMass_lower_of_smooth_upper hQ.ne_zero hβ
  refine ⟨max x₁ x₂, E + D + ((k : ℝ) - 1), hx₁.trans_le (le_max_left _ _), by positivity,
    fun x hx => ?_⟩
  have hx₁' := (le_max_left _ _).trans_lt hx
  have hx₂' := (le_max_right _ _).trans_lt hx
  have hx1 : 1 < x := hx₁.trans hx₁'
  have hx0 : 0 < x := by linarith
  let y : ℝ := x ^ β
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1.le hβ.le
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hyx : y ≤ x := Real.rpow_le_self_of_one_le hx1.le hβ1.le
  have HS := HD x y hx₁' le_rfl hyx
  have HR := HE x y (C * y) (D * y) hx₂' le_rfl HS
  have Hlog : (Q.natDegree : ℝ) * Real.log x = (k : ℝ) * Real.log y := by
    rw [show y = x ^ β from rfl, Real.log_rpow hx0]
    dsimp [β]
    field_simp
  have Hmain : (Q.natDegree : ℝ) * y * Real.log x - y * Real.log y =
      ((k : ℝ) - 1) * y * Real.log y := by nlinarith [Hlog]
  rw [Hmain] at HR
  have Hcard := (shortInterval_card_bounds hx0.le hy0.le).2
  have Hcardlog := mul_le_mul_of_nonneg_right Hcard (mul_nonneg hk1 (Real.log_nonneg hy1))
  have Hlogy : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  have Hlogerr := mul_le_mul_of_nonneg_left Hlogy hk1
  change ((k : ℝ) - 1) * (shortInterval x y).card * Real.log y -
      (E + D + ((k : ℝ) - 1)) * y ≤ _
  nlinarith

end NairTenenbaum
