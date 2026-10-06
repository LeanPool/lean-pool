/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Squared norms of absolutely continuous families

A family of real functions of time, indexed by a spatial variable, that are
absolutely continuous with a common square-integrable rate has an `L²` norm in
the spatial variable that is absolutely continuous as well, with the expected
derivative. This is the scalar time calculus behind the strong continuity and
the energy identities of `prop:lps-local-strong`.
-/

public section

open MeasureTheory Set Filter
open scoped Interval


noncomputable section

namespace ESS.LPS

/-- Cauchy–Schwarz for a finite measure in the form used for time
integrals. -/
theorem lps_sq_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {k : α → ℝ} (hk : Integrable k ν)
    (hk2 : Integrable (fun x => k x ^ 2) ν) :
    (∫ x, k x ∂ν) ^ 2 ≤ ν.real univ * ∫ x, k x ^ 2 ∂ν := by
  by_cases hm : ν.real univ = 0
  · have hν : ν = 0 := by
      rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hm
      rcases hm with hm | hm
      · exact Measure.measure_univ_eq_zero.mp hm
      · exact absurd hm (measure_ne_top ν univ)
    subst hν
    simp
  · have hmpos : 0 < ν.real univ := lt_of_le_of_ne measureReal_nonneg (Ne.symm hm)
    set m := ν.real univ with hmdef
    set c := (∫ x, k x ∂ν) / m with hc
    have hnonneg : 0 ≤ ∫ x, (c - k x) ^ 2 ∂ν :=
      integral_nonneg fun x => sq_nonneg _
    have hexp : ∫ x, (c - k x) ^ 2 ∂ν =
        c ^ 2 * m - 2 * c * (∫ x, k x ∂ν) + ∫ x, k x ^ 2 ∂ν := by
      have h1 : (fun x => (c - k x) ^ 2) =
          fun x => ((c ^ 2 - 2 * c * k x) + k x ^ 2) := by
        funext x; ring
      have hint1 : Integrable (fun x => c ^ 2 - 2 * c * k x) ν :=
        (integrable_const _).sub (hk.const_mul _)
      rw [h1, integral_add hint1 hk2,
        integral_sub (integrable_const _) (hk.const_mul _), integral_const,
        integral_const_mul]
      simp [hmdef, smul_eq_mul, mul_comm]
    rw [hexp] at hnonneg
    have hcm : c * m = ∫ x, k x ∂ν := by rw [hc]; field_simp
    have hkey : c ^ 2 * m - 2 * c * (∫ x, k x ∂ν) =
        -((∫ x, k x ∂ν) ^ 2 / m) := by
      have : c ^ 2 * m = c * (c * m) := by ring
      rw [this, hcm, hc]
      field_simp
      ring
    rw [hkey] at hnonneg
    have hle : (∫ x, k x ∂ν) ^ 2 / m ≤ ∫ x, k x ^ 2 ∂ν := by linarith only [hnonneg]
    have := (div_le_iff₀ hmpos).mp hle
    linarith only [this]

/-- A real function that is an interval integral of an integrable rate has
squared increments given by the integral of `2 F G`. -/
theorem lps_ac_sq_identity {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ℝ}
    (hG : IntervalIntegrable G volume a b)
    (hF : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F t - F s = ∫ r in s..t, G r) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t ^ 2 - F s ^ 2 = 2 * ∫ r in s..t, F r * G r := by
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hac : AbsolutelyContinuousOnInterval F a b := by
    have h := hG.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) (by simp [hab])
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => F a) a b :=
      (LipschitzWith.const (F a)).lipschitzOnWith.absolutelyContinuousOnInterval
    have h' := hc.add h
    refine h'.congr ?_
    intro x hx
    have hx' : x ∈ Icc a b := by simpa [hIcc] using hx
    have := hF a (left_mem_Icc.2 hab) x hx'
    simp only [Pi.add_apply]
    linarith only [this]
  have hderiv : ∀ᵐ x, x ∈ Ioo a b → deriv F x = G x := by
    filter_upwards [hG.ae_hasDerivAt_integral] with x hx hxI
    have hxu : x ∈ uIcc a b := by
      rw [hIcc]; exact Ioo_subset_Icc_self hxI
    have hd := (hx hxu a (by simp [hab])).const_add (F a)
    have heq : F =ᶠ[nhds x] fun y => F a + ∫ v in a..y, G v := by
      filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
      have := hF a (left_mem_Icc.2 hab) y (Ioo_subset_Icc_self hy)
      linarith only [this]
    exact (hd.congr_of_eventuallyEq heq).deriv
  intro s hs t ht
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [hIcc]
    exact uIcc_subset_Icc hs ht
  have hacst := hac.mono hsub
  have hmain := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hacst hacst
  have hcongr : ∫ x in s..t, deriv F x * F x + F x * deriv F x =
      ∫ x in s..t, 2 * (F x * G x) := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hderiv, hne] with x hx hxb hxI
    have hxI' : x ∈ Ioo a b := by
      have h1 : min s t < x := hxI.1
      have h2 : x ≤ max s t := hxI.2
      have hmin : a ≤ min s t := le_min hs.1 ht.1
      have hmax : max s t ≤ b := max_le hs.2 ht.2
      exact ⟨lt_of_le_of_lt hmin h1, lt_of_le_of_ne (h2.trans hmax) hxb⟩
    rw [hx hxI']
    ring
  rw [hcongr, intervalIntegral.integral_const_mul] at hmain
  nlinarith only [hmain]

/-- Slice and joint square integrability of an absolutely continuous family
with square-integrable rate and a square-integrable slice at one time `c`. -/
theorem lps_ac_family_sq_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {a b c : ℝ} (hab : a ≤ b) (hc : c ∈ Icc a b) {f g : X → ℝ → ℝ}
    (hfm : Measurable (fun p : X × ℝ => f p.1 p.2))
    (hgint : ∀ x, IntervalIntegrable (g x) volume a b)
    (hAC : ∀ x, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      f x t - f x s = ∫ r in s..t, g x r)
    (hg2 : Integrable (fun p : X × ℝ => g p.1 p.2 ^ 2)
      (μ.prod (volume.restrict (Ioc a b))))
    (hfc : Integrable (fun x => f x c ^ 2) μ) :
    (∀ t ∈ Icc a b, Integrable (fun x => f x t ^ 2) μ) ∧
      Integrable (fun p : X × ℝ => f p.1 p.2 ^ 2)
        (μ.prod (volume.restrict (Ioc a b))) := by
  let H : X → ℝ := fun x =>
    2 * f x c ^ 2 + 2 * (b - a) * ∫ r in Ioc a b, g x r ^ 2
  have hinner : Integrable (fun x => ∫ r in Ioc a b, g x r ^ 2) μ :=
    hg2.integral_prod_left
  have hH : Integrable H μ :=
    (hfc.const_mul 2).add (hinner.const_mul (2 * (b - a)))
  have hgood : ∀ᵐ x ∂μ,
      Integrable (fun r => g x r ^ 2) (volume.restrict (Ioc a b)) := hg2.prod_right_ae
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Icc a b, f x t ^ 2 ≤ H x := by
    filter_upwards [hgood] with x hx t ht
    have hgI : IntegrableOn (g x) (Ioc a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hgint x)
    have hCS : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
        (∫ r in Ioc u v, g x r) ^ 2 ≤ (b - a) * ∫ r in Ioc a b, g x r ^ 2 := by
      intro u v hu huv hv
      have hsub : Ioc u v ⊆ Ioc a b := Ioc_subset_Ioc hu hv
      have hgIt : IntegrableOn (g x) (Ioc u v) volume := hgI.mono_set hsub
      have hx' : IntegrableOn (fun r => g x r ^ 2) (Ioc u v) volume :=
        hx.mono_measure (Measure.restrict_mono hsub le_rfl)
      have hcs := lps_sq_integral_le (ν := volume.restrict (Ioc u v)) hgIt hx'
      have hreal : (volume.restrict (Ioc u v)).real univ = v - u := by
        simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 huv)]
      rw [hreal] at hcs
      have hmono : ∫ r in Ioc u v, g x r ^ 2 ≤ ∫ r in Ioc a b, g x r ^ 2 :=
        setIntegral_mono_set hx (ae_of_all _ fun r => sq_nonneg _) hsub.eventuallyLE
      have hnn : 0 ≤ ∫ r in Ioc u v, g x r ^ 2 :=
        integral_nonneg fun r => sq_nonneg _
      have hta : v - u ≤ b - a := by linarith only [hu, hv]
      calc
        (∫ r in Ioc u v, g x r) ^ 2 ≤ (v - u) * ∫ r in Ioc u v, g x r ^ 2 := hcs
        _ ≤ (b - a) * ∫ r in Ioc u v, g x r ^ 2 := mul_le_mul_of_nonneg_right hta hnn
        _ ≤ (b - a) * ∫ r in Ioc a b, g x r ^ 2 :=
          mul_le_mul_of_nonneg_left hmono (by linarith only [hu, hv, huv])
    have hdec : f x t = f x c + ∫ r in c..t, g x r := by
      have := hAC x c hc t ht
      linarith only [this]
    have hint2 : (∫ r in c..t, g x r) ^ 2 ≤ (b - a) * ∫ r in Ioc a b, g x r ^ 2 := by
      rcases le_total c t with hct | htc
      · rw [intervalIntegral.integral_of_le hct]
        exact hCS c t hc.1 hct ht.2
      · rw [intervalIntegral.integral_of_ge htc, neg_sq]
        exact hCS t c ht.1 htc hc.2
    rw [hdec]
    dsimp only [H]
    nlinarith only [hint2, sq_nonneg (f x c - ∫ r in c..t, g x r)]
  have hslice : ∀ t ∈ Icc a b, Integrable (fun x => f x t ^ 2) μ := by
    intro t ht
    refine Integrable.mono' hH ?_ ?_
    · exact ((hfm.comp (measurable_id.prodMk measurable_const)).pow_const 2
        ).aestronglyMeasurable
    · filter_upwards [hbound] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hx t ht
  refine ⟨hslice, ?_⟩
  have hF : AEStronglyMeasurable (fun p : X × ℝ => f p.1 p.2 ^ 2)
      (μ.prod (volume.restrict (Ioc a b))) :=
    (hfm.pow_const 2).aestronglyMeasurable
  rw [integrable_prod_iff hF]
  refine ⟨?_, ?_⟩
  · filter_upwards [hbound] with x hx
    refine Integrable.mono' (integrable_const (H x)) ?_ ?_
    · exact ((hfm.comp (measurable_const.prodMk measurable_id)).pow_const 2
        ).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun r hr => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hx r (Ioc_subset_Icc_self hr)
  · have hmeas : AEStronglyMeasurable
        (fun x => ∫ r, ‖f x r ^ 2‖ ∂(volume.restrict (Ioc a b))) μ :=
      hF.norm.integral_prod_right'
    refine Integrable.mono' (hH.const_mul (b - a)) hmeas ?_
    filter_upwards [hbound] with x hx
    have hnn : 0 ≤ ∫ r, ‖f x r ^ 2‖ ∂(volume.restrict (Ioc a b)) :=
      integral_nonneg fun r => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc
      ∫ r, ‖f x r ^ 2‖ ∂(volume.restrict (Ioc a b)) ≤
          ∫ r, H x ∂(volume.restrict (Ioc a b)) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun r => norm_nonneg _)
          (integrable_const _) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
        show ‖f x r ^ 2‖ ≤ H x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hx r (Ioc_subset_Icc_self hr)
      _ = (b - a) * H x := by
        rw [integral_const]
        simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

/-- The `L²` energy of an absolutely continuous family changes by the
integral of the pairing of the family with its rate: this is the chain rule
in time for `‖f(t)‖²`, in the spatial variable `x`, whenever the family and
the rate are jointly square integrable. -/
theorem lps_ac_family_energy_identity
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {a b : ℝ} (hab : a ≤ b) {f g : X → ℝ → ℝ}
    (hfm : Measurable (fun p : X × ℝ => f p.1 p.2))
    (hgm : Measurable (fun p : X × ℝ => g p.1 p.2))
    (hgint : ∀ x, IntervalIntegrable (g x) volume a b)
    (hAC : ∀ x, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      f x t - f x s = ∫ r in s..t, g x r)
    (hf2 : Integrable (fun p : X × ℝ => f p.1 p.2 ^ 2)
      (μ.prod (volume.restrict (Ioc a b))))
    (hg2 : Integrable (fun p : X × ℝ => g p.1 p.2 ^ 2)
      (μ.prod (volume.restrict (Ioc a b))))
    (hslice : ∀ t ∈ Icc a b, Integrable (fun x => f x t ^ 2) μ) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      (∫ x, f x t ^ 2 ∂μ) - ∫ x, f x s ^ 2 ∂μ =
        2 * ∫ r in s..t, ∫ x, f x r * g x r ∂μ := by
  intro s hs t ht hst
  have hmono : μ.prod (volume.restrict (Ioc s t)) ≤
      μ.prod (volume.restrict (Ioc a b)) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono
      (Ioc_subset_Ioc hs.1 ht.2) le_rfl)
  have hfg : Integrable (fun p : X × ℝ => f p.1 p.2 * g p.1 p.2)
      (μ.prod (volume.restrict (Ioc s t))) := by
    have hbound : Integrable (fun p : X × ℝ =>
        (f p.1 p.2 ^ 2 + g p.1 p.2 ^ 2) / 2)
        (μ.prod (volume.restrict (Ioc a b))) :=
      (hf2.add hg2).div_const 2
    refine Integrable.mono' (hbound.mono_measure hmono)
      (hfm.mul hgm).aestronglyMeasurable ?_
    refine Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith only [sq_nonneg (|f p.1 p.2| - |g p.1 p.2|),
      sq_abs (f p.1 p.2), sq_abs (g p.1 p.2)]
  have hpoint : ∀ x, f x t ^ 2 - f x s ^ 2 =
      2 * ∫ r in Ioc s t, f x r * g x r := by
    intro x
    have h := lps_ac_sq_identity hab (hgint x) (hAC x) s hs t ht
    rw [h, intervalIntegral.integral_of_le hst]
  have hsub : (∫ x, f x t ^ 2 ∂μ) - ∫ x, f x s ^ 2 ∂μ =
      ∫ x, (f x t ^ 2 - f x s ^ 2) ∂μ :=
    (integral_sub (hslice t ht) (hslice s hs)).symm
  rw [hsub, intervalIntegral.integral_of_le hst]
  have hswap := integral_integral_swap (μ := μ) (ν := volume.restrict (Ioc s t))
    (f := fun x r => f x r * g x r) hfg
  calc
    ∫ x, (f x t ^ 2 - f x s ^ 2) ∂μ =
        ∫ x, (2 * ∫ r in Ioc s t, f x r * g x r) ∂μ := by
      congr 1
      funext x
      exact hpoint x
    _ = 2 * ∫ x, (∫ r in Ioc s t, f x r * g x r) ∂μ :=
      integral_const_mul _ _
    _ = 2 * ∫ r in Ioc s t, ∫ x, f x r * g x r ∂μ := by rw [hswap]

end ESS.LPS

end
