/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoLocalComplexStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ProductTestForms

/-!
# True chart localization of arbitrary smooth forms

A scalar cutoff with compact support inside a chart localizes an arbitrary
actual smooth tensor field. Its chart coefficients extend by zero to genuine
smooth compactly supported fields on the whole model space. Both actual
exterior and normalized complex differentials agree on chart targets.
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoChartLocalization

open FirstPass StronglyPositiveForms ProductTestForms XiaoComplexDifferential
    XiaoLocalComplexStokes

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual localized coefficient field, extended by zero outside its chart target. -/
def localizedCoeff (e : ComplexChart n M) (f : M → ℝ) (a : SmoothRealForm n M k) :
    ComplexModel n → RealForm n k :=
  e.val.target.indicator fun z => f (e.val.symm z) • a.coeff e z

private theorem localizedCoeff_eventuallyEq (e : ComplexChart n M) (f : M → ℝ)
    (a : SmoothRealForm n M k) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    localizedCoeff e f a =ᶠ[𝓝 z] fun y => f (e.val.symm y) • a.coeff e y := by
  filter_upwards [e.val.open_target.mem_nhds hz] with y hy using indicator_of_mem hy _

/-- The true localized chart tensor is smooth, compactly supported, and supported in the
actual chart image of the scalar cutoff support. -/
theorem localizedCoeff_smooth_compact (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (a : SmoothRealForm n M k)
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source) :
    ContDiff ℝ ∞ (localizedCoeff e f a) ∧ HasCompactSupport (localizedCoeff e f a) ∧
      tsupport (localizedCoeff e f a) ⊆ e.val '' tsupport f := by
  let K : Set (ComplexModel n) := e.val '' tsupport f
  have hKc : IsCompact K := hc.image_of_continuousOn (e.val.continuousOn.mono hs)
  have hKt : K ⊆ e.val.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.val.map_source (hs hx)
  have hzero : ∀ z ∉ K, localizedCoeff e f a z = 0 := by
    intro z hz
    by_cases hzt : z ∈ e.val.target
    · rw [localizedCoeff, indicator_of_mem hzt]
      have hfzero : f (e.val.symm z) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hz ⟨_, h, e.val.right_inv hzt⟩
      rw [hfzero, zero_smul]
    · exact indicator_of_notMem hzt _
  have hsupp : Function.support (localizedCoeff e f a) ⊆ K := by
    intro z hz
    by_contra h
    exact hz (hzero z h)
  refine ⟨contDiff_iff_contDiffAt.2 fun z => ?_,
    HasCompactSupport.of_support_subset_isCompact hKc hsupp,
    closure_minimal hsupp hKc.isClosed⟩
  by_cases hzt : z ∈ e.val.target
  · exact (((hf e).smul (a.smooth e)).contDiffAt (e.val.open_target.mem_nhds
    hzt)).congr_of_eventuallyEq
      (localizedCoeff_eventuallyEq e f a hzt)
  · have hzK : z ∉ K := fun h => hzt (hKt h)
    have heq : localizedCoeff e f a =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hzK] with y hy using hzero y hy
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Localization preserves the actual exterior derivative on every chart target. -/
theorem extDeriv_localizedCoeff_eq (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (a : SmoothRealForm n M k) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    extDeriv (localizedCoeff e f a) z = (smulFun f hf a).exteriorDerivative.coeff e z :=
  (localizedCoeff_eventuallyEq e f a hz).extDeriv_eq

/-- Localization preserves the actual normalized complex differential on chart targets. -/
theorem localDc_localizedCoeff_eq (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (a : SmoothRealForm n M k) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    localDc (localizedCoeff e f a) z = (dc (smulFun f hf a)).coeff e z := by
  have heq : (fun y => (localizedCoeff e f a y).compContinuousLinearMap (modelComplexStructure n))
      =ᶠ[𝓝 z] fun y => ((smulFun f hf a).coeff e y).compContinuousLinearMap
        (modelComplexStructure n) :=
    (localizedCoeff_eventuallyEq e f a hz).mono fun y hy => congrArg
      (fun b : RealForm n k => b.compContinuousLinearMap (modelComplexStructure n)) hy
  change _ • (extDeriv _ z).compContinuousLinearMap _ = _
  rw [heq.extDeriv_eq]
  rfl

end

end SGPT.Foundations.Analysis.Pending.XiaoChartLocalization
