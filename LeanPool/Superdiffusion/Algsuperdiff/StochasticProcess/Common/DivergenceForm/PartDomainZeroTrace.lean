/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainTransport
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.InwardMollificationLp
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.InwardMollificationWeakGradient

/-!
# PartDomainZeroTrace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Zero trace from support in a convex part domain

This module identifies the closed subspace of `ZeroTraceSobolev U` whose
values vanish almost everywhere off a nonempty bounded open convex part
domain `V`.  The proof uses inward mollification of a literal zero extension.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {V U : Set (Vec d)}

private theorem tendsto_eLpNorm_restrict_of_tendsto_global
    {f : ℕ → Vec d → ℝ} {p : ENNReal} {W : Set (Vec d)}
    (h : Tendsto (fun n => eLpNorm (f n) p volume) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (f n) p (volume.restrict W)) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Filter.Eventually.of_forall fun _ => zero_le)
    (Filter.Eventually.of_forall fun n =>
      eLpNorm_mono_measure (f n) Measure.restrict_le_self)

/-- On a bounded open convex domain, a zero-trace graph element is determined
by its scalar `L²` component. -/
theorem ZeroTraceSobolev.eq_of_toL2_eq [NeZero d]
    (hU : IsOpenBoundedConvexDomain U) {u v : ZeroTraceSobolev U}
    (huv : ZeroTraceSobolev.toL2 u = ZeroTraceSobolev.toL2 v) :
    u = v := by
  obtain ⟨wu, hwuValue, hwuGradient⟩ :=
    ZeroTraceSobolev.exists_h10Function hU u
  obtain ⟨wv, hwvValue, hwvGradient⟩ :=
    ZeroTraceSobolev.exists_h10Function hU v
  have hvalue : wu.toH1Function.toFun =ᵐ[volumeMeasureOn U]
      wv.toH1Function.toFun := by
    filter_upwards [wu.toH1Function.coeFn_toScalarL2,
      wv.toH1Function.coeFn_toScalarL2] with x hux hvx
    rw [← hux, ← hvx, hwuValue, hwvValue, huv]
  have hgradCoord : ∀ i : Fin d,
      (fun x => wu.toH1Function.grad x i) =ᵐ[volumeMeasureOn U]
        fun x => wv.toH1Function.grad x i := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU.isOpen
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((wu.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((wv.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num)))
      (wu.toH1Function.hasWeakGradient i) ?_
    intro φ hφ hφc hφU
    have hvweak := wv.toH1Function.hasWeakGradient i φ hφ hφc hφU
    rw [← hvweak]
    apply integral_congr_ae
    filter_upwards [hvalue] with x hx
    rw [hx]
  have hgradRaw : wu.toH1Function.grad =ᵐ[volumeMeasureOn U]
      wv.toH1Function.grad := by
    have hall : ∀ᵐ x ∂volumeMeasureOn U, ∀ i : Fin d,
        wu.toH1Function.grad x i = wv.toH1Function.grad x i :=
      MeasureTheory.ae_all_iff.mpr hgradCoord
    filter_upwards [hall] with x hx
    ext i
    exact hx i
  have hgradient : ZeroTraceSobolev.gradient u =
      ZeroTraceSobolev.gradient v := by
    rw [← hwuGradient, ← hwvGradient]
    apply MeasureTheory.Lp.ext (p := (2 : ENNReal))
    filter_upwards [wu.toH1Function.coeFn_gradToHilbertVectorL2,
      wv.toH1Function.coeFn_gradToHilbertVectorL2, hgradRaw]
      with x hux hvx hx
    rw [hux, hvx]
    exact congrArg HilbertVec.ofVec hx
  exact ZeroTraceSobolev.ext huv hgradient

noncomputable def supportedRepresentative
    (w : H10Function U)
    (hzero : ∀ᵐ x ∂volumeMeasureOn U,
      x ∉ V → w.toH1Function.toFun x = 0) : H1Function U := by
  let g : Vec d → ℝ := V.indicator w.toH1Function.toFun
  have hg : g =ᵐ[volumeMeasureOn U] w.toH1Function.toFun := by
    filter_upwards [hzero] with x hx
    by_cases hxV : x ∈ V
    · change V.indicator w.toH1Function.toFun x = w.toH1Function.toFun x
      exact Set.indicator_of_mem (f := w.toH1Function.toFun) hxV
    · change V.indicator w.toH1Function.toFun x = w.toH1Function.toFun x
      rw [Set.indicator_of_notMem hxV, hx hxV]
  exact
    { toFun := g
      grad := w.toH1Function.grad
      memL2 := w.toH1Function.memL2.ae_eq hg.symm
      gradMemL2 := w.toH1Function.gradMemL2
      hasWeakGradient := by
        intro i φ hφ hφc hφU
        have hweak := w.toH1Function.hasWeakGradient i φ hφ hφc hφU
        rw [← hweak]
        apply integral_congr_ae
        filter_upwards [hg] with x hx
        rw [hx] }

noncomputable def supportedH10Representative
    (w : H10Function U)
    (hzero : ∀ᵐ x ∂volumeMeasureOn U,
      x ∉ V → w.toH1Function.toFun x = 0) : H10Function U := by
  let g := supportedRepresentative w hzero
  have hg : g.toFun =ᵐ[volumeMeasureOn U] w.toH1Function.toFun := by
    dsimp only [g, supportedRepresentative]
    filter_upwards [hzero] with x hx
    by_cases hxV : x ∈ V
    · exact Set.indicator_of_mem (f := w.toH1Function.toFun) hxV
    · rw [Set.indicator_of_notMem hxV, hx hxV]
  exact
    { toH1Function := g
      approx := w.approx
      approx_smooth := w.approx_smooth
      approx_hasCompactSupport := w.approx_hasCompactSupport
      approx_support_subset := w.approx_support_subset
      tendsto_approx := by
        refine w.tendsto_approx.congr fun n => ?_
        apply eLpNorm_congr_ae
        filter_upwards [hg] with x hx
        rw [hx]
      tendsto_approx_grad := w.tendsto_approx_grad }

noncomputable def inwardPartApproximation
    (w : H10Function U) (x0 : Vec d) (r : ℝ) (n : ℕ) : Vec d → ℝ :=
  inwardMollification (unitConvexApproxKernel (d := d)) w.zeroExtension
    x0 r (unitConvexApproxScale n)

private theorem unitConvexApproxScale_pos_local (n : ℕ) :
    0 < unitConvexApproxScale n := by
  dsimp only [unitConvexApproxScale]
  positivity

private theorem inwardPartApproximation_properties
    (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (w : H10Function U)
    (hsupport : tsupport w.zeroExtension ⊆ closure V)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ V)
    (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (inwardPartApproximation w x0 r n) ∧
      HasCompactSupport (inwardPartApproximation w x0 r n) ∧
      tsupport (inwardPartApproximation w x0 r n) ⊆ V := by
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hwMem : MemLp w.zeroExtension 2 volume :=
    w.memLp_zeroExtension hU.isOpen.measurableSet w.toH1Function.memL2
  have hwLocal : LocallyIntegrable w.zeroExtension volume :=
    hwMem.locallyIntegrable (by norm_num)
  exact ⟨
    contDiff_inwardMollification hρ hwLocal hr
      (unitConvexApproxScale_pos_local n),
    hasCompactSupport_inwardMollification hV hρ hsupport hball hr
      (unitConvexApproxScale_pos_local n),
    tsupport_inwardMollification_subset hV hρ hsupport hball hr
      (unitConvexApproxScale_pos_local n)⟩

private theorem exists_h10Function_part_of_supported [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hVne : V.Nonempty)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    (z : ZeroTraceSobolev U)
    (hzero : ∀ᵐ x ∂volumeMeasureOn U,
      x ∉ V → ZeroTraceSobolev.toL2 z x = 0) :
    ∃ w : H10Function V,
      ZeroTraceSobolev.toL2
          (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
            (ZeroTraceSobolev.ofH10Function w)) =
        ZeroTraceSobolev.toL2 z := by
  obtain ⟨u, huValue, -⟩ := ZeroTraceSobolev.exists_h10Function hU z
  have huZero : ∀ᵐ x ∂volumeMeasureOn U,
      x ∉ V → u.toH1Function.toFun x = 0 := by
    filter_upwards [u.toH1Function.coeFn_toScalarL2, hzero]
      with x hcoe hx
    intro hxV
    rw [← hcoe, huValue]
    exact hx hxV
  let u' : H10Function U := supportedH10Representative u huZero
  have hu'Value : u'.toH1Function.toFun =
      V.indicator u.toH1Function.toFun := rfl
  have hu'Support : tsupport u'.zeroExtension ⊆ closure V := by
    apply closure_minimal
    · intro x hx
      by_contra hxV
      apply hx
      rw [H10Function.zeroExtension, hu'Value]
      have hxV' : x ∉ V := fun hx => hxV (subset_closure hx)
      by_cases hxU : x ∈ U
      · rw [Set.indicator_of_mem hxU, Set.indicator_of_notMem hxV']
      · rw [Set.indicator_of_notMem hxU]
    · exact isClosed_closure
  let x0 : Vec d := Classical.choose hVne
  have hx0 : x0 ∈ V := Classical.choose_spec hVne
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.1
    (hV.isOpen.mem_nhds hx0)
  let r : ℝ := δ / 2
  have hr : 0 < r := by positivity
  have hball : Metric.closedBall x0 r ⊆ V := by
    intro y hy
    apply hδball
    have hyr : dist y x0 ≤ r := by
      simpa only [Metric.mem_closedBall] using hy
    have hrδ : r < δ := by
      dsimp only [r]
      linarith only [hδpos]
    simpa only [Metric.mem_ball] using lt_of_le_of_lt hyr hrδ
  let vH1 : H1Function V := u'.toH1Function.restrict hV.isOpen hVU
  have hvalueGlobal : Tendsto
      (fun n => eLpNorm
        (fun x => inwardPartApproximation u' x0 r n x - u'.zeroExtension x)
        2 volume) atTop (nhds 0) := by
    exact tendsto_eLpNorm_inwardMollification_sub_zero
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num) (by norm_num)
      (u'.memLp_zeroExtension hU.isOpen.measurableSet u'.toH1Function.memL2)
      x0 hr tendsto_unitConvexApproxScale_zero
      unitConvexApproxScale_nonneg
      (Filter.Eventually.of_forall unitConvexApproxScale_pos_local)
  have hvalue : Tendsto
      (fun n => eLpNorm
        (fun x => inwardPartApproximation u' x0 r n x - vH1.toFun x)
        2 (volumeMeasureOn V)) atTop (nhds 0) := by
    have hrestricted :=
      tendsto_eLpNorm_restrict_of_tendsto_global (W := V) hvalueGlobal
    refine hrestricted.congr fun n => ?_
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hxV
    rw [u'.zeroExtension_apply_of_mem (hVU hxV)]
    rfl
  have hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (inwardPartApproximation u' x0 r n) x)
            (basisVec i) - vH1.grad x i)
        2 (volumeMeasureOn V)) atTop (nhds 0) := by
    intro i
    have hcoordMem : MemLp (fun x => u'.zeroExtensionGrad x i) 2 volume := by
      have hmem := u'.gradMemLp_zeroExtensionGrad hU.isOpen.measurableSet
        u'.toH1Function.gradMemL2
      have hcoord := hmem i
      change MemLp (fun x => u'.zeroExtensionGrad x i) 2
        (volume.restrict Set.univ) at hcoord
      simpa only [Measure.restrict_univ] using hcoord
    have hglobal := tendsto_eLpNorm_one_add_mul_inwardMollification_sub_zero
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num) (by norm_num) hcoordMem x0 hr
      tendsto_unitConvexApproxScale_zero unitConvexApproxScale_nonneg
      (Filter.Eventually.of_forall unitConvexApproxScale_pos_local)
    have hderivGlobal : Tendsto
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (inwardPartApproximation u' x0 r n) x)
              (basisVec i) - u'.zeroExtensionGrad x i)
          2 volume) atTop (nhds 0) := by
      refine hglobal.congr fun n => ?_
      apply eLpNorm_congr_ae
      filter_upwards [u'.ae_eq_fderiv_inwardMollification_unit_apply_basisVec
        hU.isOpen.measurableSet (x0 := x0) hr
        (unitConvexApproxScale_pos_local n) i] with x hx
      simpa only [inwardPartApproximation, inwardMollification,
        globalAffineExpansion] using
          congrArg (fun y => y - u'.zeroExtensionGrad x i) hx.symm
    have hrestricted :=
      tendsto_eLpNorm_restrict_of_tendsto_global (W := V) hderivGlobal
    refine hrestricted.congr fun n => ?_
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hxV
    rw [u'.zeroExtensionGrad_apply_of_mem (hVU hxV)]
    rfl
  let w : H10Function V :=
    { toH1Function := vH1
      approx := inwardPartApproximation u' x0 r
      approx_smooth := fun n =>
        (inwardPartApproximation_properties hV hU u' hu'Support hball hr n).1
      approx_hasCompactSupport := fun n =>
        (inwardPartApproximation_properties hV hU u' hu'Support hball hr n).2.1
      approx_support_subset := fun n =>
        (inwardPartApproximation_properties hV hU u' hu'Support hball hr n).2.2
      tendsto_approx := hvalue
      tendsto_approx_grad := hgrad }
  refine ⟨w, ?_⟩
  have hwcoeU : ∀ᵐ x ∂volumeMeasureOn U,
      x ∈ V → w.toH1Function.toScalarL2 x = w.toH1Function.toFun x := by
    rw [ae_restrict_iff' hU.isOpen.measurableSet]
    filter_upwards
      [ae_restrict_iff' hV.isOpen.measurableSet |>.mp
        w.toH1Function.coeFn_toScalarL2]
      with x hx
    exact fun _ hxV => hx hxV
  apply MeasureTheory.Lp.ext (p := (2 : ENNReal))
  filter_upwards
    [ZeroTraceSobolev.extendByZeroToPartSuperset_toL2 hV hU.isOpen hVU
      (ZeroTraceSobolev.ofH10Function w),
      hwcoeU, u.toH1Function.coeFn_toScalarL2, hzero]
      with x hext hwcoe hucoe hxzero
  rw [hext]
  by_cases hxV : x ∈ V
  · rw [Set.indicator_of_mem hxV]
    change w.toH1Function.toScalarL2 x = ZeroTraceSobolev.toL2 z x
    rw [hwcoe hxV]
    change u'.toH1Function.toFun x = _
    rw [hu'Value, Set.indicator_of_mem hxV, ← hucoe, huValue]
  · rw [Set.indicator_of_notMem hxV]
    exact (hxzero hxV).symm

/-- A zero-trace Sobolev element on `U` which vanishes almost everywhere off
the nonempty bounded open convex part domain `V` is exactly the canonical zero
extension of an element of `ZeroTraceSobolev V`.  The carrier is the completed
value-gradient graph `ZeroTraceSobolev`; no assertion for a general open part
domain is made.

The hypothesis is a zero-trace element `z` of the ambient domain, not an
arbitrary element of `H¹(U)`.  That is exactly what the exterior penalization
limit supplies: the penalized solutions all lie in the Hilbert space
`ZeroTraceSobolev U`, are bounded there uniformly in the penalization
parameter, and the limit is extracted as a weak limit of that bounded
sequence, so it lies in the same space.  The zero-trace hypothesis also
suffices for the use made of the conclusion, which is only to rewrite the
limit as a zero extension from `V` before testing the weak equation against
zero-trace test functions on `V`. -/
theorem exists_eq_extendByZeroToPartSuperset_of_ae_zero [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hVne : V.Nonempty)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    (z : ZeroTraceSobolev U)
    (hzero : ∀ᵐ x ∂volumeMeasureOn U,
      x ∉ V → ZeroTraceSobolev.toL2 z x = 0) :
    ∃ w : ZeroTraceSobolev V,
      ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU w = z := by
  obtain ⟨w, hw⟩ := exists_h10Function_part_of_supported
    hV hVne hU hVU z hzero
  refine ⟨ZeroTraceSobolev.ofH10Function w, ?_⟩
  exact ZeroTraceSobolev.eq_of_toL2_eq hU hw

end DivergenceFormProcess.Form
