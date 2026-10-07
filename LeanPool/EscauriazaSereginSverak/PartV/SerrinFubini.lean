/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exchanging a spatial cutoff integral with a time integral

A time-dependent density that agrees at almost every time with a jointly
strongly measurable density, and is dominated on the support of the spatial
cutoff by an integrable function of time, may be integrated first in space or
first in time. This is the exchange used for the mollified cross pairing in
`lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped Interval


noncomputable section

namespace ESS

private theorem serrin_ae_Ioc_of_ae_Ioo {T t : ℝ} (ht : t ∈ Icc 0 T) {P : ℝ → Prop}
    (h : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), P τ) :
    ∀ᵐ τ ∂volume, τ ∈ Ι (0 : ℝ) t → P τ := by
  have h' := (ae_restrict_iff' measurableSet_Ioo).mp h
  filter_upwards [h', Measure.ae_ne volume T] with τ hτ hτT hτI
  rw [uIoc_of_le ht.1] at hτI
  exact hτ ⟨hτI.1, lt_of_le_of_ne (hτI.2.trans ht.2) hτT⟩

/-- Fubini exchange for a cutoff-weighted density that is dominated by an
integrable function of time on the cutoff support. -/
theorem serrin_cutoff_fubini {T t : ℝ} (ht : t ∈ Icc 0 T)
    {η : Vec3 → ℝ} {K : Set Vec3} (hK : IsCompact K)
    (hηK : ∀ y, y ∉ K → η y = 0) (hηmeas : StronglyMeasurable η)
    {Cη : ℝ} (hηbd : ∀ y, |η y| ≤ Cη)
    {H : Vec3 → ℝ → ℝ}
    (hH : AEStronglyMeasurable (fun z : ℝ × Vec3 => H z.2 z.1)
      ((volume.restrict (Ioo 0 T)).prod volume))
    {m : ℝ → ℝ} (hm : IntegrableOn m (Ioo 0 T))
    (hbd : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), ∀ y ∈ K, |H y τ| ≤ m τ) :
    (∫ y, η y * ∫ τ in (0 : ℝ)..t, H y τ) =
      ∫ τ in (0 : ℝ)..t, ∫ y, η y * H y τ := by
  let μt : Measure ℝ := volume.restrict (Ι (0 : ℝ) t)
  let f : ℝ → Vec3 → ℝ := fun τ y => η y * H y τ
  have hsub : Ι (0 : ℝ) t ⊆ Ioc 0 T := by
    rw [uIoc_of_le ht.1]
    exact Ioc_subset_Ioc_right ht.2
  have hμt : μt ≤ volume.restrict (Ioo 0 T) := by
    calc
      μt ≤ volume.restrict (Ioc 0 T) := Measure.restrict_mono hsub le_rfl
      _ = volume.restrict (Ioo 0 T) := Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hmt : Integrable m μt := Integrable.mono_measure hm hμt
  have hmeasf : AEStronglyMeasurable (Function.uncurry f) (μt.prod volume) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ × Vec3 => η z.2) (μt.prod volume) :=
      (hηmeas.comp_measurable measurable_snd).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z : ℝ × Vec3 => H z.2 z.1) (μt.prod volume) :=
      hH.mono_measure (Measure.prod_mono hμt le_rfl)
    exact h1.mul h2
  have hmajor : Integrable (fun z : ℝ × Vec3 => m z.1 * (Cη * K.indicator 1 z.2))
      (μt.prod volume) := by
    have hind : Integrable (fun y : Vec3 => Cη * K.indicator (1 : Vec3 → ℝ) y) volume :=
      ((integrable_indicator_iff hK.measurableSet).mpr
        (integrableOn_const hK.measure_lt_top.ne)).const_mul Cη
    exact hmt.mul_prod hind
  have hbdt : ∀ᵐ τ ∂μt, ∀ y ∈ K, |H y τ| ≤ m τ := ae_mono hμt hbd
  have hbdprod : ∀ᵐ z ∂(μt.prod volume), ‖Function.uncurry f z‖ ≤
      m z.1 * (Cη * K.indicator 1 z.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbdt] with z hz
    change ‖η z.2 * H z.2 z.1‖ ≤ _
    by_cases hy : z.2 ∈ K
    · rw [Real.norm_eq_abs, abs_mul, indicator_of_mem hy, Pi.one_apply, mul_one]
      calc
        |η z.2| * |H z.2 z.1| ≤ Cη * m z.1 :=
          mul_le_mul (hηbd z.2) (hz z.2 hy) (abs_nonneg _)
            ((abs_nonneg _).trans (hηbd z.2))
        _ = m z.1 * Cη := by ring
    · rw [hηK z.2 hy, zero_mul, indicator_of_notMem hy]
      simp
  have hint : Integrable (Function.uncurry f) (μt.prod volume) :=
    hmajor.mono' hmeasf hbdprod
  have hswap := (intervalIntegral_integral_swap hint).symm
  simp only [f] at hswap
  rw [← hswap]
  congr 1
  funext y
  rw [intervalIntegral.integral_const_mul]

end ESS
