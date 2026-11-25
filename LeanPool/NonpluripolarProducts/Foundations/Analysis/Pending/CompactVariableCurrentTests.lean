/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPositiveCurrentGluing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoChartLocalization

/-! # Actual scalar tests for compact variable forms and genuine positive-current pairing -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests

open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorForms
  LocalPositiveCurrentGluing ScalarLeviPositiveCurrent XiaoChartLocalization LocalCurrentLebesgue

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {U : Opens (ComplexModel n)}

/-- Genuine scalar tests from continuous coefficient postcomposition of the actual full test. -/
def coeffTest (α : 𝓓(U, RealForm n (2 * q)))
    (i : Fin (Module.finrank ℝ (formSpan n q))) : 𝓓(U, ℝ) :=
  TestFunction.postcompCLM (coeffCLM n q i) α

/-- The finite constant-form expansion is internally produced from the actual test. -/
theorem eq_sum_coeffTest (α : 𝓓(U, RealForm n (2 * q)))
    (hα : ∀ x, α x ∈ formSpan n q) (x : ComplexModel n) :
    α x = ∑ i, coeffTest α i x • ((formBasis n q i : formSpan n q) : RealForm n (2 * q)) := by
  exact eq_sum_formCoeff (hα x)

/-- Full variable-test positivity applies to genuine compact form coefficients. -/
theorem pairing_nonnegative (S : LocalProductCurrent n U q) (hS : IsPositive S)
    (α : 𝓓(U, RealForm n (2 * q))) (hα : ∀ x, α x ∈ spCone q) :
    0 ≤ ∑ i, S (formBasis n q i) (coeffTest α i) := by
  apply hS _ (formBasis n q) (coeffTest α)
  intro x
  rw [← eq_sum_coeffTest α (fun y => mem_formSpan_of_mem_spCone (hα y)) x]
  exact hα x

section Charts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The literal chart cutoff field is a genuine compact variable-form test inside `U`. -/
def chartTest (e : ComplexChart n M) (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (a : SmoothRealForm n M (2 * q)) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) (hU : e.val '' tsupport f ⊆ U) :
    𝓓(U, RealForm n (2 * q)) :=
  let h := localizedCoeff_smooth_compact e f hf a hc hs
  ⟨localizedCoeff e f a, h.1, h.2.1, h.2.2.trans hU⟩

/-- Genuine nonnegative cutoffs preserve full chart strong positivity, including outside-target
    zero. -/
theorem chartTest_mem_spCone (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (a : SmoothRealForm n M (2 * q))
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source)
    (hU : e.val '' tsupport f ⊆ U) (hfnonneg : ∀ x, 0 ≤ f x)
    (ha : ∀ z ∈ e.val.target, a.coeff e z ∈ spCone q) (z : ComplexModel n) :
    chartTest e f hf a hc hs hU z ∈ spCone q := by
  change localizedCoeff e f a z ∈ spCone q
  by_cases hz : z ∈ e.val.target
  · rw [localizedCoeff, indicator_of_mem hz]
    exact smul_mem_spCone (ha z hz) (hfnonneg _)
  · rw [localizedCoeff, indicator_of_notMem hz]
    exact (spCone q).zero_mem

end Charts

section Levi

variable {m : ℕ} {A : Opens (ComplexModel (m + 1))} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- Scalar Levi positivity pairs nonnegatively with every actual localized chart strong test. -/
theorem nonnegative_ddc_chartTest {T : 𝓓'(A, ℝ)} (hT : HasNonnegativeDistributionalLevi T)
    (e : ComplexChart (m + 1) M) (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (a : SmoothRealForm (m + 1) M (2 * m)) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) (hA : e.val '' tsupport f ⊆ A)
    (hfnonneg : ∀ x, 0 ≤ f x) (ha : ∀ z ∈ e.val.target, a.coeff e z ∈ spCone m) :
    0 ≤ ∑ i, LocalBedfordTaylorProducts.ddc (scalarTopCurrent T)
      (formBasis (m + 1) m i) (coeffTest (chartTest e f hf a hc hs hA) i) := by
  exact pairing_nonnegative _ (isPositive_ddc_scalarTopCurrent hT) _
    (chartTest_mem_spCone e f hf a hc hs hA hfnonneg ha)

end Levi

end SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
