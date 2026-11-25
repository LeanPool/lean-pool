/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorForms

/-!
# Smooth densities for Bedford–Taylor products

Wedging the integration current with a smooth form gives the current with that density.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothDensity

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalCurrentLebesgue ConstantFormProducts TopDegreeDensity

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The genuine integration current wedged with a smooth form has its literal density. -/
theorem wedgeForm_oneCurrent_apply {r k : ℕ} (h : r + k = n)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (hαS : ∀ x ∈ U, α x ∈ formSpan n k) (γ : formSpan n r) (φ : 𝓓(U, ℝ)) :
    wedgeForm h (oneCurrent U) hα γ φ =
      ∫ x, φ x * topDensity (wedgeTo (by omega : 2 * r + 2 * k = 2 * n)
        (γ : RealForm n (2 * r)) (α x)) := by
  classical
  rw [wedgeForm_apply]
  simp only [oneCurrent_apply]
  have hint : ∀ i, Integrable (fun x =>
      topDensity ((wedgeSpan n h γ (formBasis n k i) : formSpan n n) :
        RealForm n (2 * n)) * mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ x) volume :=
    fun i => ((mulSmoothOnCLM (contDiffOn_formCoeff hα i)
      φ).continuous.integrable_of_hasCompactSupport
      (mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ).hasCompactSupport).const_mul _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ U
  · have e := congrArg (topDensityLM n)
      (sum_mulSmoothOnCLM_smul_wedgeSpan h hα hαS γ φ (by omega) hx)
    simp only [map_sum, map_smul, smul_eq_mul, topDensityLM_apply] at e
    calc
      _ = ∑ i, mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ x *
          topDensity ((wedgeSpan n h γ (formBasis n k i) : formSpan n n) :
            RealForm n (2 * n)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = _ := e
  · simp only [LocalBedfordTaylorLocality.testFunction_eq_zero_of_notMem _ hx,
      mul_zero, zero_mul, Finset.sum_const_zero]

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothDensity
