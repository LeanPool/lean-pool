/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalBoundaryWeightedSchurRows
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.WeightedNonnegativeKernelSchur

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalBoundaryWeightedSchur

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur bound for the fractional boundary kernel
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A globally positive version of the auxiliary boundary weight. It agrees
with the boundary weight on the restricted measure used by the Schur test. -/
@[expose]
noncomputable def fractionalBoundarySchurWeight
    (U : Set (Vec d)) (a : ℝ) (x : Vec d) : ℝ≥0∞ := by
  classical
  exact if x ∈ U then euclideanBoundaryWeight U a x else 1

theorem measurable_fractionalBoundarySchurWeight
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (a : ℝ) :
    Measurable (fractionalBoundarySchurWeight U a) := by
  classical
  have h : fractionalBoundarySchurWeight U a =
      fun x => if x ∈ U then euclideanBoundaryWeight U a x else 1 := by
    funext x
    by_cases hx : x ∈ U <;> simp [fractionalBoundarySchurWeight, hx]
  rw [h]
  exact Measurable.ite (measurableSet_of_isOpenBoundedConvexDomain hU)
    (measurable_euclideanBoundaryWeight U a) measurable_const

/-- The boundary-weighted fractional Riesz operator satisfies a squared
`L²` Schur bound for every auxiliary exponent `s<a<1-s`. -/
theorem exists_lintegral_fractionalBoundarySchurKernel_rpow_two_le
    (hd : 1 ≤ d) {rho Rad s a : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad) (hs : 0 < s)
    (hsa : s < a) (hsa1 : s + a < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad → ∀ (f : Vec d → ℝ≥0∞), Measurable f →
          (∫⁻ x in U,
            (∫⁻ y in U, fractionalBoundarySchurKernel U s x y * f y ∂volume) ^
              (2 : ℝ) ∂volume) ≤
            C * ∫⁻ y in U, f y ^ (2 : ℝ) ∂volume := by
  classical
  obtain ⟨A, B, hAtop, hBtop, hrows⟩ :=
    exists_fractionalBoundarySchur_row_column
      hd hrho hRad hs hsa hsa1
  refine ⟨A * B, ENNReal.mul_ne_top hAtop hBtop, ?_⟩
  intro U hU hsand f hf
  let : IsFiniteMeasure (volume.restrict U) :=
    hU.isFiniteMeasure_restrict_volume
  have hweightMeas := measurable_fractionalBoundarySchurWeight hU a
  have hweight0 : ∀ x, fractionalBoundarySchurWeight U a x ≠ 0 := by
    intro x
    by_cases hx : x ∈ U
    · rw [fractionalBoundarySchurWeight, ite_eq_left hx]
      unfold euclideanBoundaryWeight
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (Real.rpow_pos_of_pos (euclideanBoundaryDistance_pos hd hU hx) _)
    · rw [fractionalBoundarySchurWeight, ite_eq_right hx]
      norm_num
  have hweightTop : ∀ x, fractionalBoundarySchurWeight U a x ≠ ⊤ := by
    intro x
    by_cases hx : x ∈ U
    · rw [fractionalBoundarySchurWeight, ite_eq_left hx]
      exact ENNReal.ofReal_ne_top
    · rw [fractionalBoundarySchurWeight, ite_eq_right hx]
      norm_num
  have hrow : ∀ᵐ x ∂volume.restrict U,
      (∫⁻ y, fractionalBoundarySchurKernel U s x y *
          fractionalBoundarySchurWeight U a y ∂volume.restrict U) ≤
        A * fractionalBoundarySchurWeight U a x := by
    filter_upwards [self_mem_ae_restrict
      (measurableSet_of_isOpenBoundedConvexDomain hU)] with x hx
    rw [fractionalBoundarySchurWeight, ite_eq_left hx]
    calc
      (∫⁻ y, fractionalBoundarySchurKernel U s x y *
          fractionalBoundarySchurWeight U a y ∂volume.restrict U) =
          ∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
            euclideanBoundaryWeight U a y ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict
          (measurableSet_of_isOpenBoundedConvexDomain hU)] with y hy
        rw [fractionalBoundarySchurWeight, ite_eq_left hy]
      _ ≤ A * euclideanBoundaryWeight U a x := (hrows U hU hsand).1 x hx
  have hcol : ∀ᵐ y ∂volume.restrict U,
      (∫⁻ x, fractionalBoundarySchurKernel U s x y *
          fractionalBoundarySchurWeight U a x ∂volume.restrict U) ≤
        B * fractionalBoundarySchurWeight U a y := by
    filter_upwards [self_mem_ae_restrict
      (measurableSet_of_isOpenBoundedConvexDomain hU)] with y hy
    rw [fractionalBoundarySchurWeight, ite_eq_left hy]
    calc
      (∫⁻ x, fractionalBoundarySchurKernel U s x y *
          fractionalBoundarySchurWeight U a x ∂volume.restrict U) =
          ∫⁻ x in U, fractionalBoundarySchurKernel U s x y *
            euclideanBoundaryWeight U a x ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict
          (measurableSet_of_isOpenBoundedConvexDomain hU)] with x hx
        rw [fractionalBoundarySchurWeight, ite_eq_left hx]
      _ ≤ B * euclideanBoundaryWeight U a y := (hrows U hU hsand).2 y hy
  exact lintegral_weightedNonnegativeKernel_rpow_two_le
    (volume.restrict U) (volume.restrict U)
    (measurable_fractionalBoundarySchurKernel U s) hf
    hweightMeas hweightMeas hweight0 hweightTop hrow hcol

end

end HighContrast
end HCPolySupport
