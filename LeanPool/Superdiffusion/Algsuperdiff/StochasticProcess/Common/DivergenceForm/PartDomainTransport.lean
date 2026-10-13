/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.CoefficientPairing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.DomainMaps
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ZeroTraceSobolev
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ZeroExtensionGraph

/-!
# PartDomainTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Transport between nested domains

This module records scalar restriction, zero extension for zero-trace Sobolev
elements, and the pairing identities used to move weak formulations between
nested domains.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter
open scoped RealInnerProductSpace

variable {d : ℕ} {V U : Set (Vec d)}

/-- The coefficient pairing is the integral of the pointwise inner product
of the coefficient image of the first field against the second. -/
theorem coefficientPairing_eq_integral_inner
    (a : CoeffField d) (W : Set (Vec d))
    (F G : HilbertVectorL2 W) :
    coefficientPairing a W F G =
      ∫ x in W, inner ℝ (HilbertVec.applyMat (a x) (F x)) (G x)
        ∂MeasureTheory.volume := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards
    [coeFn_hilbertVectorL2ToVectorL2 (U := W) F,
      coeFn_hilbertVectorL2ToVectorL2 (U := W) G]
      with x hF hG
  simp only [HilbertVec.applyMat_apply, HilbertVec.inner_def]
  rw [hF, hG, HilbertVec.toVec_ofVec]

theorem scalar_inner_zeroExtension_eq_restriction
    (hV : MeasurableSet V) (hU : MeasurableSet U)
    (hVU : V ⊆ U) (zU : ScalarL2 U) (zV : ScalarL2 V)
    (φU : ScalarL2 U) (φV : ScalarL2 V)
    (hz : zU =ᵐ[volumeMeasureOn U] V.indicator fun x => zV x)
    (hφ : φV =ᵐ[volumeMeasureOn V] φU) :
    inner ℝ zU φU = inner ℝ zV φV := by
  classical
  rw [scalarInner_eq_integral, scalarInner_eq_integral,
    ← MeasureTheory.integral_indicator hU,
    ← MeasureTheory.integral_indicator hV]
  apply MeasureTheory.integral_congr_ae
  filter_upwards
    [ae_restrict_iff' hU |>.mp hz,
      ae_restrict_iff' hV |>.mp hφ]
      with x hzx hφx
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hxV : x ∈ V
  · rw [ite_eq_left hxV, ite_eq_left (hVU hxV), hzx (hVU hxV),
      Set.indicator_of_mem hxV, hφx hxV]
  · rw [ite_eq_right hxV]
    by_cases hxU : x ∈ U
    · rw [ite_eq_left hxU, hzx hxU, Set.indicator_of_notMem hxV, zero_mul]
    · rw [ite_eq_right hxU]

theorem coefficientPairing_zeroExtension_eq_restriction
    (a : CoeffField d)
    (hV : MeasurableSet V) (hU : MeasurableSet U)
    (hVU : V ⊆ U) (FU : HilbertVectorL2 U) (FV : HilbertVectorL2 V)
    (GU : HilbertVectorL2 U) (GV : HilbertVectorL2 V)
    (hF : FU =ᵐ[volumeMeasureOn U] V.indicator fun x => FV x)
    (hG : GV =ᵐ[volumeMeasureOn V] GU) :
    coefficientPairing a U FU GU = coefficientPairing a V FV GV := by
  classical
  rw [coefficientPairing_eq_integral_inner,
    coefficientPairing_eq_integral_inner,
    ← MeasureTheory.integral_indicator hU,
    ← MeasureTheory.integral_indicator hV]
  apply MeasureTheory.integral_congr_ae
  filter_upwards
    [ae_restrict_iff' hU |>.mp hF,
      ae_restrict_iff' hV |>.mp hG]
      with x hFx hGx
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hxV : x ∈ V
  · rw [ite_eq_left hxV, ite_eq_left (hVU hxV), hFx (hVU hxV),
      Set.indicator_of_mem hxV, hGx hxV]
  · rw [ite_eq_right hxV]
    by_cases hxU : x ∈ U
    · rw [ite_eq_left hxU, hFx hxU, Set.indicator_of_notMem hxV,
        map_zero, inner_zero_left]
    · rw [ite_eq_right hxU]

theorem scalar_inner_restriction_le
    (hVU : V ⊆ U) (fU : ScalarL2 U) (fV : ScalarL2 V)
    (φU : ScalarL2 U) (φV : ScalarL2 V)
    (hfV : fV =ᵐ[volumeMeasureOn V] fU)
    (hφV : φV =ᵐ[volumeMeasureOn V] φU)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ fU x)
    (hφ : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ φU x) :
    inner ℝ fV φV ≤ inner ℝ fU φU := by
  rw [scalarInner_eq_integral, scalarInner_eq_integral]
  have hVeq : (∫ x in V, fV x * φV x ∂volume) =
      ∫ x in V, fU x * φU x ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hfV, hφV] with x hfx hφx
    rw [hfx, hφx]
  rw [hVeq]
  apply MeasureTheory.setIntegral_mono_set
  · exact (MeasureTheory.Lp.memLp fU).integrable_mul
      (MeasureTheory.Lp.memLp φU)
  · filter_upwards [hf, hφ] with x hfx hφx
    exact mul_nonneg hfx hφx
  · exact Filter.Eventually.of_forall fun _ hx => hVU hx

/-- Restriction of scalar `L²` data to a measurable part domain. -/
noncomputable def restrictScalarL2ToPart
    (hU : MeasurableSet U) (f : ScalarL2 U) : ScalarL2 V :=
  restrictToDomain V (zeroExtendFromDomain hU f)

/-- Almost-everywhere characterization of scalar `L²` restriction between
nested measurable domains. -/
theorem restrictScalarL2ToPart_coeFn
    (hV : MeasurableSet V) (hU : MeasurableSet U)
    (hVU : V ⊆ U) (f : ScalarL2 U) :
    restrictScalarL2ToPart (V := V) hU f =ᵐ[volumeMeasureOn V] f := by
  filter_upwards
    [restrictToDomain_coeFn V (zeroExtendFromDomain hU f),
      ae_restrict_of_ae (zeroExtendFromDomain_coeFn hU f),
      self_mem_ae_restrict hV]
      with x hrestrict hzero hxV
  change restrictToDomain V (zeroExtendFromDomain hU f) x = f x
  rw [hrestrict, hzero, Set.indicator_of_mem (hVU hxV)]

namespace ZeroTraceSobolev

/-- Canonical zero extension of a zero-trace Sobolev element from a bounded
open convex domain to an open superset. -/
noncomputable def extendByZeroToPartSuperset [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hU : IsOpen U)
    (hVU : V ⊆ U) (u : ZeroTraceSobolev V) : ZeroTraceSobolev U :=
  let w : H10Function V := Classical.choose (exists_h10Function hV u)
  ofH10Function
    (w.extendByZeroToOpenSuperset hV.isOpen.measurableSet hU hVU)

/-- The value of the canonical zero extension is the indicator extension. -/
theorem extendByZeroToPartSuperset_toL2 [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hU : IsOpen U)
    (hVU : V ⊆ U) (u : ZeroTraceSobolev V) :
    toL2 (extendByZeroToPartSuperset hV hU hVU u) =ᵐ[volumeMeasureOn U]
      V.indicator fun x => toL2 u x := by
  let w : H10Function V := Classical.choose (exists_h10Function hV u)
  have hw := Classical.choose_spec (exists_h10Function hV u)
  change
    (w.extendByZeroToOpenSuperset hV.isOpen.measurableSet hU hVU).toH1Function.toScalarL2
      =ᵐ[volumeMeasureOn U] V.indicator fun x => toL2 u x
  have hwcoe : ∀ᵐ x ∂volumeMeasureOn U,
      x ∈ V → w.toH1Function.toScalarL2 x = w.toH1Function.toFun x := by
    rw [ae_restrict_iff' hU.measurableSet]
    filter_upwards
      [ae_restrict_iff' hV.isOpen.measurableSet |>.mp
        w.toH1Function.coeFn_toScalarL2]
      with x hx
    exact fun _ hxV => hx hxV
  filter_upwards
    [(w.extendByZeroToOpenSuperset hV.isOpen.measurableSet hU hVU).toH1Function.coeFn_toScalarL2,
      hwcoe]
      with x hext hwcoe
  rw [hext]
  change w.zeroExtension x = _
  rw [H10Function.zeroExtension]
  by_cases hxV : x ∈ V
  · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem hxV, ← hwcoe hxV]
    have hwu : w.toH1Function.toScalarL2 = toL2 u := hw.1
    exact congrArg (fun z : ScalarL2 V => z x) hwu
  · rw [Set.indicator_of_notMem hxV, Set.indicator_of_notMem hxV]

/-- The weak gradient of the canonical zero extension is the indicator
extension of the original weak gradient. -/
theorem extendByZeroToPartSuperset_gradient [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hU : IsOpen U)
    (hVU : V ⊆ U) (u : ZeroTraceSobolev V) :
    gradient (extendByZeroToPartSuperset hV hU hVU u) =ᵐ[volumeMeasureOn U]
      V.indicator fun x => gradient u x := by
  let w : H10Function V := Classical.choose (exists_h10Function hV u)
  have hw := Classical.choose_spec (exists_h10Function hV u)
  change
    (w.extendByZeroToOpenSuperset hV.isOpen.measurableSet hU hVU).toH1Function.gradToHilbertVectorL2
      =ᵐ[volumeMeasureOn U] V.indicator fun x => gradient u x
  have hwcoe : ∀ᵐ x ∂volumeMeasureOn U,
      x ∈ V → w.toH1Function.gradToHilbertVectorL2 x =
        HilbertVec.ofVec (w.toH1Function.grad x) := by
    rw [ae_restrict_iff' hU.measurableSet]
    filter_upwards
      [ae_restrict_iff' hV.isOpen.measurableSet |>.mp
        w.toH1Function.coeFn_gradToHilbertVectorL2]
      with x hx
    exact fun _ hxV => hx hxV
  classical
  filter_upwards
    [(w.extendByZeroToOpenSuperset hV.isOpen.measurableSet hU
      hVU).toH1Function.coeFn_gradToHilbertVectorL2,
      hwcoe]
      with x hext hwcoe
  rw [hext]
  change HilbertVec.ofVec (w.zeroExtensionGrad x) = _
  rw [H10Function.zeroExtensionGrad, Set.indicator_apply, Set.indicator_apply]
  by_cases hxV : x ∈ V
  · rw [ite_eq_left hxV, ite_eq_left hxV, ← hwcoe hxV]
    have hwu : w.toH1Function.gradToHilbertVectorL2 = gradient u := hw.2
    rw [← congrArg (fun z : HilbertVectorL2 V => z x) hwu]
  · rw [ite_eq_right hxV, ite_eq_right hxV]
    rfl

end ZeroTraceSobolev

end DivergenceFormProcess.Form
