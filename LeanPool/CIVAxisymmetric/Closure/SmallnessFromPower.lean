/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Smallness From Power

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If `F r` is bounded by `K * r^γ` for small `r`, then `F r` can be made arbitrarily small.
This is the key analytic fact that smallness of `F` follows from a power‑law bound:
lemma `lem:aniso:closure` in arXiv:2609.20803. -/
theorem forall_eps_of_le_ofReal_rpow {F : ℝ → ℝ≥0∞} {K γ r₁ : ℝ} (hγ : 0 < γ) (hr₁ : 0 < r₁)
    (hF : ∀ r : ℝ, 0 < r → r ≤ r₁ → F r ≤ ENNReal.ofReal (K * r ^ γ)) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → F r ≤ ENNReal.ofReal ε := by
  intro ε hε
  by_cases hK : K ≤ 0
  · -- K ≤ 0: the bound is nonpositive, so F r ≤ 0 ≤ ε for all r.
    refine ⟨r₁, hr₁, fun r hr hlt => ?_⟩
    have hFr := hF r hr hlt.le
    have h_nonpos : K * r ^ γ ≤ 0 := by
      have h_rpow_pos : 0 < r ^ γ := Real.rpow_pos_of_pos hr γ
      nlinarith only [hK, h_rpow_pos]
    have h_ofReal : ENNReal.ofReal (K * r ^ γ) ≤ ENNReal.ofReal (0 : ℝ) :=
      ENNReal.ofReal_le_ofReal h_nonpos
    have h_ofReal_zero : ENNReal.ofReal (0 : ℝ) ≤ ENNReal.ofReal ε :=
      ENNReal.ofReal_le_ofReal (by linarith only [hε])
    exact le_trans hFr (le_trans h_ofReal h_ofReal_zero)
  · -- K > 0
    have hK_pos : 0 < K := by linarith only [hK]
    have h_div_pos : 0 < ε / K := div_pos hε hK_pos
    have h_div_nonneg : 0 ≤ ε / K := h_div_pos.le
    set r₀ : ℝ := min r₁ ((ε / K) ^ ((1 : ℝ) / γ)) with hr₀_def
    have hr₀_pos : 0 < r₀ := by
      refine lt_min_iff.mpr ⟨hr₁, Real.rpow_pos_of_pos h_div_pos _⟩
    refine ⟨r₀, hr₀_pos, fun r hr hlt => ?_⟩
    have hr_lt_r₁ : r < r₁ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hr_le_r₁ : r ≤ r₁ := hr_lt_r₁.le
    have hFr := hF r hr hr_le_r₁
    have h_ineq : K * r ^ γ ≤ ε := by
      have h_r_lt : r < (ε / K) ^ ((1 : ℝ) / γ) := lt_of_lt_of_le hlt (min_le_right _ _)
      have h_rpow_lt' : r ^ γ < ((ε / K) ^ ((1 : ℝ) / γ)) ^ γ :=
        Real.rpow_lt_rpow (by linarith only [hr]) h_r_lt hγ
      have h_rpow_simp : ((ε / K) ^ ((1 : ℝ) / γ)) ^ γ = ε / K := by
        calc
          ((ε / K) ^ ((1 : ℝ) / γ)) ^ γ = (ε / K) ^ (((1 : ℝ) / γ) * γ) := by
            rw [Real.rpow_mul h_div_nonneg]
          _ = (ε / K) ^ (1 : ℝ) := by
            field_simp [hγ.ne.symm]
          _ = ε / K := Real.rpow_one _
      have h_rpow_lt : r ^ γ < ε / K := by
        linarith only [h_rpow_lt', h_rpow_simp]
      calc
        K * r ^ γ ≤ K * (ε / K) :=
          mul_le_mul_of_nonneg_left (by linarith only [h_rpow_lt]) (by linarith only [hK_pos])
        _ = ε := by field_simp [hK_pos.ne.symm]
    have h_nonneg : 0 ≤ K * r ^ γ := by
      have h_rpow_nonneg : 0 ≤ r ^ γ := Real.rpow_nonneg (by linarith only [hr]) _
      nlinarith only [hK_pos, h_rpow_nonneg]
    have h_ofReal_ineq : ENNReal.ofReal (K * r ^ γ) ≤ ENNReal.ofReal ε :=
      ENNReal.ofReal_le_ofReal h_ineq
    exact le_trans hFr h_ofReal_ineq

end CIV
