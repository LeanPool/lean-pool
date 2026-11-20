/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexCDF.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Order.MonotoneContinuity

/-! # Genuine cumulative-density calculus for quantile transport -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The cumulative distribution function `x ↦ ∫ t in Iic x, p t` of a density `p`. -/
def densityCDF (p : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Iic x, p t

theorem cdf_withDensity_eq_densityCDF (p : ℝ → ℝ) (hp : Measurable p)
    (hn : ∀ x, 0 ≤ p x)
    [IsProbabilityMeasure ((volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (p x)))]
    (x : ℝ) :
    cdf ((volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (p x))) x =
      densityCDF p x := by
  rw [cdf_eq_real, measureReal_def, withDensity_apply _ measurableSet_Iic]
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn)
    hp.aestronglyMeasurable).symm

theorem densityCDF_hasDerivAt (p : ℝ → ℝ) (hp : Continuous p)
    (hi : Integrable p volume) (x : ℝ) : HasDerivAt (densityCDF p) (p x) x := by
  have he : densityCDF p = fun y => densityCDF p 0 + ∫ t in (0 : ℝ)..y, p t := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic
      (a := (0 : ℝ)) (b := y) hi.integrableOn hi.integrableOn
    dsimp [densityCDF]
    linarith
  rw [he]
  convert (intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable 0 x)
    ⟨univ, Filter.univ_mem, hp.stronglyMeasurable.aestronglyMeasurable⟩ hp.continuousAt).const_add
    (densityCDF p 0) using 1

theorem densityCDF_continuous (p : ℝ → ℝ) (hp : Continuous p)
    (hi : Integrable p volume) : Continuous (densityCDF p) :=
  continuous_iff_continuousAt.mpr fun x => (densityCDF_hasDerivAt p hp hi x).continuousAt

theorem densityCDF_strictMonoOn (p : ℝ → ℝ) (hp : Continuous p)
    (hi : Integrable p volume) (a : ℝ) (hpos : ∀ x, a < x → 0 < p x) :
    StrictMonoOn (densityCDF p) (Ioi a) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi a) (densityCDF_continuous p hp hi).continuousOn
  intro x hx
  rw [(densityCDF_hasDerivAt p hp hi x).deriv]
  exact hpos x (interior_subset hx)

theorem strictly_increasing_CDF_image_univ (F : ℝ → ℝ)
    (hc : Continuous F) (hm : StrictMono F)
    (hbound : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (hbot : Tendsto F atBot (𝓝 0)) (htop : Tendsto F atTop (𝓝 1)) :
    F '' (univ : Set ℝ) = Ioo 0 1 := by
  apply Set.Subset.antisymm
  · rintro u ⟨x, _, rfl⟩
    exact ⟨(hbound (x - 1)).1.trans_lt (hm (by linarith)),
      (hm (by linarith : x < x + 1)).trans_le (hbound (x + 1)).2⟩
  · intro u hu
    have hl : ∀ᶠ x in atBot, F x ≤ u :=
      (hbot.eventually (gt_mem_nhds hu.1)).mono fun _ h => h.le
    have hr : ∀ᶠ x in atTop, u ≤ F x :=
      (htop.eventually (lt_mem_nhds hu.2)).mono fun _ h => h.le
    obtain ⟨x, hx⟩ := intermediate_value_univ₂_eventually₂ hc continuous_const hl hr
    exact ⟨x, mem_univ _, hx⟩

theorem strictly_increasing_CDF_image_Ioi (F : ℝ → ℝ) (a : ℝ)
    (hc : ContinuousOn F (Ici a)) (hm : StrictMonoOn F (Ici a))
    (ha : F a = 0) (hbound : ∀ x, F x ≤ 1)
    (htop : Tendsto F atTop (𝓝 1)) : F '' Ioi a = Ioo 0 1 := by
  apply Set.Subset.antisymm
  · rintro u ⟨x, hx, rfl⟩
    change a < x at hx
    refine ⟨?_, (hm (show x ∈ Ici a from hx.le) (show x + 1 ∈ Ici a by change a ≤ x + 1; linarith)
      (by linarith : x < x + 1)).trans_le (hbound (x + 1))⟩
    simpa [ha] using hm (self_mem_Ici : a ∈ Ici a) (show x ∈ Ici a from hx.le) hx
  · intro u hu
    have hr : ∀ᶠ x in atTop, u < F x ∧ a < x :=
      (htop.eventually (lt_mem_nhds hu.2)).and (eventually_gt_atTop a)
    obtain ⟨b, hb, hab⟩ := hr.exists
    obtain ⟨x, hx, he⟩ := intermediate_value_Icc hab.le
      (hc.mono fun y hy => hy.1) (show u ∈ Icc (F a) (F b) by rw [ha]; exact ⟨hu.1.le, hb.le⟩)
    have hax : a < x := by
      rcases hx.1.eq_or_lt with h | h
      · subst x; rw [ha] at he; linarith [hu.1]
      · exact h
    exact ⟨x, hax, he⟩

/-- A function strictly increasing on `Ioi a` with image `Ioo 0 1`, as an order isomorphism
`Ioi a ≃o Ioo 0 1`. -/
def increasingCDFOrderIso (F : ℝ → ℝ) (a : ℝ)
    (hm : StrictMonoOn F (Ioi a)) (hr : F '' Ioi a = Ioo 0 1) :
    Ioi a ≃o Ioo (0 : ℝ) 1 :=
  (hm.orderIso F (Ioi a)).trans (Set.orderIsoOfEq _ _ hr)

/-- The quantile function of `F` on `Ioi a`: the inverse of `increasingCDFOrderIso` on
`Ioo 0 1`, extended by `a` elsewhere. -/
def increasingCDFQuantile (F : ℝ → ℝ) (a : ℝ)
    (hm : StrictMonoOn F (Ioi a)) (hr : F '' Ioi a = Ioo 0 1) (u : ℝ) : ℝ :=
  if hu : u ∈ Ioo (0 : ℝ) 1 then
    ((increasingCDFOrderIso F a hm hr).symm ⟨u, hu⟩ : ℝ) else a

theorem increasingCDFQuantile_mem (F : ℝ → ℝ) (a : ℝ)
    (hm : StrictMonoOn F (Ioi a)) (hr : F '' Ioi a = Ioo 0 1)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    a < increasingCDFQuantile F a hm hr u := by
  rw [increasingCDFQuantile, dite_eq_left hu]
  exact ((increasingCDFOrderIso F a hm hr).symm ⟨u, hu⟩).property

theorem increasingCDFQuantile_right_inverse (F : ℝ → ℝ) (a : ℝ)
    (hm : StrictMonoOn F (Ioi a)) (hr : F '' Ioi a = Ioo 0 1)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    F (increasingCDFQuantile F a hm hr u) = u := by
  rw [increasingCDFQuantile, dite_eq_left hu]
  exact congrArg Subtype.val ((increasingCDFOrderIso F a hm hr).apply_symm_apply ⟨u, hu⟩)

theorem increasingCDFQuantile_continuousOn (F : ℝ → ℝ) (a : ℝ)
    (hm : StrictMonoOn F (Ioi a)) (hr : F '' Ioi a = Ioo 0 1) :
    ContinuousOn (increasingCDFQuantile F a hm hr) (Ioo 0 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := continuous_subtype_val.comp
    (increasingCDFOrderIso F a hm hr).toHomeomorph.symm.continuous
  convert hc using 1
  funext u
  simp [increasingCDFQuantile, u.property]

theorem increasingCDFQuantile_hasDerivAt (F p : ℝ → ℝ) (a : ℝ)
    (hm : StrictMonoOn F (Ioi a)) (hr : F '' Ioi a = Ioo 0 1)
    (hd : ∀ x, a < x → HasDerivAt F (p x) x)
    (hp : ∀ x, a < x → p x ≠ 0)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (increasingCDFQuantile F a hm hr)
      (p (increasingCDFQuantile F a hm hr u))⁻¹ u := by
  have hq := increasingCDFQuantile_mem F a hm hr u hu
  apply HasDerivAt.of_local_left_inverse
    ((increasingCDFQuantile_continuousOn F a hm hr).continuousAt (isOpen_Ioo.mem_nhds hu))
    (hd _ hq) (hp _ hq)
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact increasingCDFQuantile_right_inverse F a hm hr v hv

/-- A function strictly increasing on `s` with image `Ioo 0 1`, as an order isomorphism
`s ≃o Ioo 0 1`. -/
def increasingCDFOrderIsoOn (F : ℝ → ℝ) (s : Set ℝ)
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1) :
    s ≃o Ioo (0 : ℝ) 1 :=
  (hm.orderIso F s).trans (Set.orderIsoOfEq _ _ hr)

/-- The quantile function of `F` on `s`: the inverse of `increasingCDFOrderIsoOn` on
`Ioo 0 1`, extended by `0` elsewhere. -/
def increasingCDFQuantileOn (F : ℝ → ℝ) (s : Set ℝ)
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1) (u : ℝ) : ℝ :=
  if hu : u ∈ Ioo (0 : ℝ) 1 then
    ((increasingCDFOrderIsoOn F s hm hr).symm ⟨u, hu⟩ : ℝ) else 0

theorem increasingCDFQuantileOn_mem (F : ℝ → ℝ) (s : Set ℝ)
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    increasingCDFQuantileOn F s hm hr u ∈ s := by
  rw [increasingCDFQuantileOn, dite_eq_left hu]
  exact ((increasingCDFOrderIsoOn F s hm hr).symm ⟨u, hu⟩).property

theorem increasingCDFQuantileOn_right_inverse (F : ℝ → ℝ) (s : Set ℝ)
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    F (increasingCDFQuantileOn F s hm hr u) = u := by
  rw [increasingCDFQuantileOn, dite_eq_left hu]
  exact congrArg Subtype.val ((increasingCDFOrderIsoOn F s hm hr).apply_symm_apply ⟨u, hu⟩)

theorem increasingCDFQuantileOn_continuousOn (F : ℝ → ℝ) (s : Set ℝ) [OrdConnected s]
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1) :
    ContinuousOn (increasingCDFQuantileOn F s hm hr) (Ioo 0 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := continuous_subtype_val.comp
    (increasingCDFOrderIsoOn F s hm hr).toHomeomorph.symm.continuous
  convert hc using 1
  funext u
  simp [increasingCDFQuantileOn, u.property]

theorem increasingCDFQuantileOn_hasDerivAt (F p : ℝ → ℝ) (s : Set ℝ) [OrdConnected s]
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (hd : ∀ x ∈ s, HasDerivAt F (p x) x)
    (hp : ∀ x ∈ s, p x ≠ 0)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (increasingCDFQuantileOn F s hm hr)
      (p (increasingCDFQuantileOn F s hm hr u))⁻¹ u := by
  have hq := increasingCDFQuantileOn_mem F s hm hr u hu
  apply HasDerivAt.of_local_left_inverse
    ((increasingCDFQuantileOn_continuousOn F s hm hr).continuousAt (isOpen_Ioo.mem_nhds hu))
    (hd _ hq) (hp _ hq)
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact increasingCDFQuantileOn_right_inverse F s hm hr v hv

end
end GinibrePoincare
