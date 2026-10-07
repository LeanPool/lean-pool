/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Segment Quotient

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If `g` is differentiable on the interval between `0` and `x` with
`|deriv g| ≤ M` there, then `|g x / x| ≤ M` whenever `x ≠ 0`. -/
theorem abs_div_le_of_deriv_bound {g : ℝ → ℝ} {x M : ℝ} (hg0 : g 0 = 0)
    (hd : ∀ s ∈ uIcc (0 : ℝ) x, DifferentiableAt ℝ g s)
    (hM : ∀ s ∈ uIcc (0 : ℝ) x, |deriv g s| ≤ M) (hx : x ≠ 0) :
    |g x / x| ≤ M := by
  rcases lt_or_gt_of_ne hx with (hx_neg | hx_pos)
  · -- case x < 0: apply MVT on [x, 0]
    have h_cont : ContinuousOn g (Icc x 0) := by
      intro s hs
      have hs_mem : s ∈ uIcc (0 : ℝ) x := by
        rw [uIcc_comm, uIcc_of_le (le_of_lt hx_neg : x ≤ 0)]
        exact hs
      exact (hd s hs_mem).continuousAt.continuousWithinAt
    have h_diff : DifferentiableOn ℝ g (Ioo x 0) := by
      intro s hs
      have hs_mem : s ∈ uIcc (0 : ℝ) x := by
        rw [uIcc_comm, uIcc_of_le (le_of_lt hx_neg : x ≤ 0)]
        exact Ioo_subset_Icc_self hs
      exact (hd s hs_mem).differentiableWithinAt
    obtain ⟨c, hc, hc_eq⟩ := exists_deriv_eq_slope g hx_neg h_cont h_diff
    have hc_mem : c ∈ uIcc (0 : ℝ) x := by
      rw [uIcc_comm, uIcc_of_le (le_of_lt hx_neg : x ≤ 0)]
      exact Ioo_subset_Icc_self hc
    -- hc_eq: deriv g c = (g 0 - g x) / (0 - x)
    rw [hg0] at hc_eq
    have h_simp : (0 - g x) / (0 - x) = g x / x := by
      ring
    rw [h_simp] at hc_eq
    rw [← hc_eq]
    exact hM c hc_mem
  · -- case 0 < x: apply MVT on [0, x]
    have h_cont : ContinuousOn g (Icc (0 : ℝ) x) := by
      intro s hs
      have hs_mem : s ∈ uIcc (0 : ℝ) x :=
        uIcc_of_le (le_of_lt hx_pos : (0 : ℝ) ≤ x) ▸ hs
      exact (hd s hs_mem).continuousAt.continuousWithinAt
    have h_diff : DifferentiableOn ℝ g (Ioo (0 : ℝ) x) := by
      intro s hs
      have hs_mem : s ∈ uIcc (0 : ℝ) x :=
        uIcc_of_le (le_of_lt hx_pos : (0 : ℝ) ≤ x) ▸ Ioo_subset_Icc_self hs
      exact (hd s hs_mem).differentiableWithinAt
    obtain ⟨c, hc, hc_eq⟩ := exists_deriv_eq_slope g hx_pos h_cont h_diff
    have hc_mem : c ∈ uIcc (0 : ℝ) x :=
      uIcc_of_le (le_of_lt hx_pos : (0 : ℝ) ≤ x) ▸ Ioo_subset_Icc_self hc
    -- hc_eq: deriv g c = (g x - g 0) / (x - 0)
    rw [hg0, sub_zero, sub_zero] at hc_eq
    rw [← hc_eq]
    exact hM c hc_mem

/-- If `g` is differentiable on the interval between `0` and `x` with
`|deriv g| ≤ M` there, then `|g x| ≤ M * |x|`. -/
theorem abs_le_mul_of_deriv_bound {g : ℝ → ℝ} {x M : ℝ} (hg0 : g 0 = 0)
    (hd : ∀ s ∈ uIcc (0 : ℝ) x, DifferentiableAt ℝ g s)
    (hM : ∀ s ∈ uIcc (0 : ℝ) x, |deriv g s| ≤ M) :
    |g x| ≤ M * |x| := by
  by_cases hx : x = 0
  · subst x
    rw [hg0, abs_zero, mul_zero]
  · have h_div := abs_div_le_of_deriv_bound hg0 hd hM hx
    have h_eq : |g x| = |g x / x| * |x| := by
      calc
        |g x| = |(g x / x) * x| := by field_simp [hx]
        _ = |g x / x| * |x| := abs_mul _ _
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right h_div (abs_nonneg _)

end CIV
