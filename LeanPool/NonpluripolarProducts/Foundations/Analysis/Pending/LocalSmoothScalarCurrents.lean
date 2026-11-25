/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth

/-! # Actual local smooth potentials and scalar coefficient currents -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalSmoothScalarCurrents

open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorSmooth LocalBedfordTaylorCollar ScalarLeviPositiveCurrent

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The true regular-current identity needs smoothness only on the actual open set. -/
theorem scalarTopCurrent_regularDistribution_eq_mulBorel_of_contDiffOn
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    scalarTopCurrent (regularDistribution volume f
      (hf.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)) =
      mulBorel (oneCurrent U) ((U : Set (ComplexModel n)).indicator f) := by
  ext γ φ
  obtain ⟨χ, hχ, hχ1, hχU⟩ := exists_cutoff φ.hasCompactSupport U.isOpen φ.tsupport_subset
  let g : ComplexModel n → ℝ := fun x => χ x * f x
  have hg : ContDiff ℝ ∞ g := contDiff_mul_of_tsupport_subset U.isOpen hχ hχU hf
  have hfg : ∀ x, f x * φ x = g x * φ x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hχx : χ x = 1 := (hχ1 x hx).eq_of_nhds
      simp only [g, hχx, one_mul]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hφx, mul_zero, mul_zero]
  have hind : ∀ x, ((U : Set (ComplexModel n)).indicator f) x * φ x =
      ((U : Set (ComplexModel n)).indicator g) x * φ x := by
    intro x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
      exact hfg x
    · simp only [indicator_of_notMem hx, zero_mul]
  have h := congrArg (fun R : LocalProductCurrent n U n => R γ φ)
    (scalarTopCurrent_regularDistribution_eq_mulBorel hg)
  rw [scalarTopCurrent_apply, regularDistribution_apply,
    mulBorel_apply isPositive_oneCurrent
      (measurable_indicator_of_continuousOn hg.continuous.continuousOn)
      (isLocallyBoundedOn_indicator_of_continuousOn hg.continuous.continuousOn)] at h
  rw [scalarTopCurrent_apply, regularDistribution_apply,
    mulBorel_apply isPositive_oneCurrent
      (measurable_indicator_of_continuousOn hf.continuousOn)
      (isLocallyBoundedOn_indicator_of_continuousOn hf.continuousOn)]
  have hgf : ∀ x, φ x * f x = φ x * g x := fun x => by
    simpa only [mul_comm] using hfg x
  convert h using 1
  · congr 1
    exact integral_congr_ae (Eventually.of_forall hgf)
  · exact integral_congr_ae (Eventually.of_forall fun x => by
      by_cases hφ : φ x = 0
      · simp only [hφ, zero_mul]
      · dsimp only
        rw [mul_right_cancel₀ hφ (hind x)])

/-- The genuine local scalar smooth differential equals the actual unit-current wedge. -/
theorem ddc_scalarTopCurrent_regularDistribution_eq_ddcWedge
    {m : ℕ} {A : Opens (ComplexModel (m + 1))} {f : ComplexModel (m + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f A) :
    ddc (scalarTopCurrent (regularDistribution volume f
      (hf.continuousOn.locallyIntegrableOn A.isOpen.measurableSet))) =
      ddcWedge (oneCurrent A) hf := by
  rw [scalarTopCurrent_regularDistribution_eq_mulBorel_of_contDiffOn hf]
  change ddcMul (oneCurrent A) f = ddcWedge (oneCurrent A) hf
  exact ddcMul_eq_ddcWedge isPositive_oneCurrent (isClosedAny_oneCurrent (n := m + 1)) hf

end SGPT.Foundations.Analysis.Pending.LocalSmoothScalarCurrents
