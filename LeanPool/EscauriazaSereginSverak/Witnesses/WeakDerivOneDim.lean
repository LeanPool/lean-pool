/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Examples for one-dimensional weak derivatives

These examples witness the test-function and weak-derivative interfaces in
`def:sws` and `lem:ftc-small-time`.
-/

public section

open CKN

open MeasureTheory Set

noncomputable section

namespace ESS

/-- The zero function is a smooth compactly supported test on `(0,1)`. -/
theorem isIntervalTest_zero_witness :
    IsIntervalTest (Ioo (0 : ℝ) 1) (fun _ => 0) := by
  refine ⟨contDiff_const, HasCompactSupport.intro isCompact_empty (by simp), ?_⟩
  rw [show (fun _ : ℝ => 0) = (0 : ℝ → ℝ) from rfl, tsupport_zero]
  exact empty_subset _

/-- A nonzero smooth bump is a test function on `(0,1)`. -/
theorem IsIntervalTest_satisfiable :
    ∃ φ : ℝ → ℝ, φ (1 / 2) ≠ 0 ∧ IsIntervalTest (Ioo (0 : ℝ) 1) φ := by
  have hq : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨φ, hφsupport, hφcompact, hφsmooth, _, hφq⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (isOpen_Ioo.mem_nhds hq)
  refine ⟨φ, ?_, ⟨hφsmooth, hφcompact, hφsupport⟩⟩
  rw [hφq]
  norm_num

/-- The zero function has weak derivative zero on `(0,1)`. -/
theorem hasWeakDerivOn_zero_witness :
    HasWeakDerivOn (Ioo (0 : ℝ) 1) (fun _ => 0) (fun _ => 0) := by
  intro φ _
  simp

private theorem integral_deriv_eq_zero_of_intervalTest
    {φ : ℝ → ℝ} (hφ : IsIntervalTest (Ioo (0 : ℝ) 1) φ) :
    ∫ x, deriv φ x = 0 := by
  have hφzero : φ 0 = 0 := by
    by_contra hne
    have hmem : 0 ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hne)
    exact (lt_irrefl 0) (hφ.2.2 hmem).1
  have hderivSupport : Function.support (deriv φ) ⊆ Ioi (0 : ℝ) := by
    exact (support_deriv_subset.trans hφ.2.2).trans (by
      intro x hx
      exact hx.1)
  have hIoi : (∫ x in Ioi (0 : ℝ), deriv φ x) = ∫ x, deriv φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra hne
    have hsupport : x ∈ Function.support (deriv φ) := Function.mem_support.mpr hne
    exact hx (hderivSupport hsupport)
  have hFTC : (∫ x in Ioi (0 : ℝ), deriv φ x) = -φ 0 :=
    hφ.2.1.integral_Ioi_deriv_eq (hφ.1.of_le (by norm_num)) 0
  calc
    ∫ x, deriv φ x = ∫ x in Ioi (0 : ℝ), deriv φ x := hIoi.symm
    _ = -φ 0 := hFTC
    _ = 0 := by rw [hφzero]; simp

/-- A nonzero constant function has weak derivative zero on `(0,1)`. -/
theorem HasWeakDerivOn_satisfiable :
    (fun _ : ℝ => (1 : ℝ)) (1 / 2) ≠ 0 ∧
      HasWeakDerivOn (Ioo (0 : ℝ) 1) (fun _ => 1) (fun _ => 0) := by
  constructor
  · norm_num
  · intro φ hφ
    have hderiv : (∫ x in Ioo (0 : ℝ) 1, deriv φ x) = ∫ x, deriv φ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_contra hne
      have hsupport : x ∈ Function.support (deriv φ) := Function.mem_support.mpr hne
      exact hx ((support_deriv_subset.trans hφ.2.2) hsupport)
    change (∫ x in Ioo (0 : ℝ) 1, 1 * deriv φ x) =
      -(∫ x in Ioo (0 : ℝ) 1, (0 : ℝ) * φ x)
    calc
      (∫ x in Ioo (0 : ℝ) 1, 1 * deriv φ x) =
          ∫ x in Ioo (0 : ℝ) 1, deriv φ x := by simp
      _ = ∫ x, deriv φ x := hderiv
      _ = 0 := integral_deriv_eq_zero_of_intervalTest hφ
      _ = -(∫ x in Ioo (0 : ℝ) 1, (0 : ℝ) * φ x) := by simp

end ESS
