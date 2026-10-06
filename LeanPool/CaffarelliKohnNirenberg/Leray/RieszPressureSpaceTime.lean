/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureLp
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionNormTransport

/-!
# Joint pressure representatives for compactly supported space-time data

The completed CKN operator supplies jointly measurable representatives on
compactly supported spatial slices. This file identifies those representatives
with the all-exponent ESS pressure on common-domain slices.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Spatial slices of a compactly supported space-time function retain compact
support, used by `def:riesz-pressure`. -/
theorem continuous_spaceTimeSlice_hasCompactSupport
    {F : Vec3 × ℝ → ℝ} (hFc : HasCompactSupport F) (t : ℝ) :
    HasCompactSupport (fun x : Vec3 => F (x, t)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hFc.isCompact.image continuous_fst)
  intro x hx
  have hx' : (x, t) ∈ Function.support F := by
    change F (x, t) ≠ 0
    change F (x, t) ≠ 0 at hx
    exact hx
  exact ⟨(x, t), subset_tsupport F hx', rfl⟩

/-- Tonelli's formula for the (r)-power of a space-time (L^r) seminorm,
used by `eq:riesz-spacetime-bound`. -/
theorem eLpNorm_spaceTime_pow_eq_integral_slice (r : ℝ) (hr : 0 < r)
    {F : Vec3 × ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume : Measure (Vec3 × ℝ))) :
    eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r =
      ∫⁻ t, eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r)
        (volume : Measure Vec3) ^ r ∂(volume : Measure ℝ) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hFprod : AEStronglyMeasurable F
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hF
  have hprod := hFprod.enorm.pow_const r
  have hSlices := hFprod.prodMk_right
  rw [eLpNorm_eq_eLpNorm' hr0 hrtop hF, ENNReal.toReal_ofReal hr.le,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hr]
  calc
    (∫⁻ z, ‖F z‖ₑ ^ r ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) =
        ∫⁻ x, ∫⁻ t, ‖F (x, t)‖ₑ ^ r ∂(volume : Measure ℝ)
          ∂(volume : Measure Vec3) := by
      exact lintegral_prod _ hprod
    _ = ∫⁻ t, ∫⁻ x, ‖F (x, t)‖ₑ ^ r ∂(volume : Measure Vec3)
          ∂(volume : Measure ℝ) :=
      lintegral_lintegral_swap (f := fun x t => ‖F (x, t)‖ₑ ^ r) hprod
    _ = ∫⁻ t, eLpNorm' (fun x : Vec3 => F (x, t)) r
          (volume : Measure Vec3) ^ r ∂(volume : Measure ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [hSlices] with t ht
      exact (lintegral_rpow_enorm_eq_rpow_eLpNorm'
        (f := fun x : Vec3 => F (x, t)) hr)
    _ = ∫⁻ t, eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r)
          (volume : Measure Vec3) ^ r ∂(volume : Measure ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [hSlices] with t ht
      rw [eLpNorm_eq_eLpNorm' hr0 hrtop ht, ENNReal.toReal_ofReal hr.le]

/-- A continuous compactly supported space-time input has a jointly measurable
representative of its signed double Riesz transform, used by
`def:riesz-pressure`. -/
theorem exists_measurable_rieszPressure_component_of_compact
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∃ P : Vec3 × ℝ → ℝ, Measurable P ∧
      ∀ᵐ t ∂(volume : Measure ℝ),
        (fun x => P (x, t)) =ᵐ[volume]
          fun x => rieszPressureOperator r hr i j
            (((hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
              (continuous_spaceTimeSlice_hasCompactSupport hFc t)).toLp
              (fun y => F (y, t))) x := by
  let slice (t : ℝ) : Vec3 → ℝ := fun x => F (x, t)
  have hsliceContinuous (t : ℝ) : Continuous (slice t) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hsliceCompact (t : ℝ) : HasCompactSupport (slice t) := by
    exact continuous_spaceTimeSlice_hasCompactSupport hFc t
  have hsliceLp (t : ℝ) (p : ℝ) (hp : 0 < p) :
      MemLp (slice t) (ENNReal.ofReal p) volume :=
    (hsliceContinuous t).memLp_of_hasCompactSupport (hsliceCompact t)
  have hFs : ∀ᵐ t ∂(volume : Measure ℝ),
      MemLp (slice t) (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
      HasCompactSupport (slice t) := by
    filter_upwards [] with t
    exact ⟨hsliceLp t (6 / 5) (by norm_num), hsliceCompact t⟩
  obtain ⟨H, hHmeas, hHslice⟩ :=
    CKN.Core.Step4.exists_measurable_riesz_extension_field i j hF.measurable hFs
  refine ⟨fun z => -H z, hHmeas.neg, ?_⟩
  have hF2 (t : ℝ) : MemLp (slice t) 2 volume :=
    by simpa using hsliceLp t 2 (by norm_num)
  have hFr (t : ℝ) : MemLp (slice t) (ENNReal.ofReal r) volume :=
    hsliceLp t r (lt_trans zero_lt_one hr)
  filter_upwards [hHslice] with t ht
  have hRaw := CKN.Foundation.Euclidean.rieszSecondGradientExtensionOperator_ae_raw
    (CKN.Foundation.Euclidean.rieszSecondL2Input i j)
    (CKN.Foundation.Euclidean.rieszSecondL2_weak_type i j)
    (hsliceLp t (6 / 5) (by norm_num))
    (hF2 t)
  have hEss := rieszPressureOperator_ae_eq_negRaw r hr i j (slice t) (hFr t) (hF2 t)
  have hNeg : (fun x => -H (x, t)) =ᵐ[volume]
      fun x => -CKN.Foundation.Euclidean.rieszSecondL2RawOperator
        (CKN.Foundation.Euclidean.rieszSecondL2Input i j) (slice t) x :=
    ht.neg.trans hRaw.neg
  exact hNeg.trans hEss.symm

/-- The joint component representative for compact data is in product-space
`L^r`, with the componentwise CKN bound; used by `eq:riesz-spacetime-bound`. -/
theorem exists_rieszPressure_component_memLp_bound_of_compact
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∃ P : Vec3 × ℝ → ℝ, Measurable P ∧
      (∀ᵐ t ∂(volume : Measure ℝ),
        (fun x => P (x, t)) =ᵐ[volume]
          fun x => rieszPressureOperator r hr i j
            (((hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
              (continuous_spaceTimeSlice_hasCompactSupport hFc t)).toLp
              (fun y => F (y, t))) x) ∧
      MemLp P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ∧
      eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ≤
        ENNReal.ofReal (rieszPressureOperatorBound r hr) *
          eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
  obtain ⟨P, hPm, hPslice⟩ :=
    exists_measurable_rieszPressure_component_of_compact r hr i j hF hFc
  have hC : 0 ≤ rieszPressureOperatorBound r hr := by
    have h := rieszPressureOperator_norm_le r hr i j
    exact le_trans (norm_nonneg _) h
  have hr0 : r ≠ 0 := (lt_trans zero_lt_one hr).ne'
  have hFmem : MemLp F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    hF.memLp_of_hasCompactSupport hFc
  have hFprod : AEStronglyMeasurable F
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hF.aestronglyMeasurable
  have hPprod : AEStronglyMeasurable P
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hPm.aestronglyMeasurable
  have hFpowersMeas : Measurable (fun z : Vec3 × ℝ => ‖F z‖ₑ ^ r) :=
    hF.measurable.enorm.pow_const r
  have hPpowersMeas : Measurable (fun z : Vec3 × ℝ => ‖P z‖ₑ ^ r) :=
    hPm.enorm.pow_const r
  let IF : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x : Vec3, ‖F (x, t)‖ₑ ^ r ∂(volume : Measure Vec3)
  let IP : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x : Vec3, ‖P (x, t)‖ₑ ^ r ∂(volume : Measure Vec3)
  have hIFmeas : Measurable IF := by
    exact hFpowersMeas.lintegral_prod_left'
  have hIPmeas : Measurable IP := by
    exact hPpowersMeas.lintegral_prod_left'
  have hFsliceAE : ∀ᵐ t ∂(volume : Measure ℝ),
      AEStronglyMeasurable (fun x : Vec3 => F (x, t)) (volume : Measure Vec3) :=
    hFprod.prodMk_right
  have hPsliceAE : ∀ᵐ t ∂(volume : Measure ℝ),
      AEStronglyMeasurable (fun x : Vec3 => P (x, t)) (volume : Measure Vec3) :=
    hPprod.prodMk_right
  have hFsliceIntegral :
      (fun t => eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r)
        (volume : Measure Vec3) ^ r) =ᵐ[volume] IF := by
    filter_upwards [hFsliceAE] with t ht
    rw [eLpNorm_eq_eLpNorm'
      (by exact (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hr)).ne')
      ENNReal.ofReal_ne_top ht, ENNReal.toReal_ofReal (le_trans zero_le_one hr.le)]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (f := fun x : Vec3 => F (x, t)) (lt_trans zero_lt_one hr)).symm
  have hPsliceIntegral :
      (fun t => eLpNorm (fun x : Vec3 => P (x, t)) (ENNReal.ofReal r)
        (volume : Measure Vec3) ^ r) =ᵐ[volume] IP := by
    filter_upwards [hPsliceAE] with t ht
    rw [eLpNorm_eq_eLpNorm'
      (by exact (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hr)).ne')
      ENNReal.ofReal_ne_top ht, ENNReal.toReal_ofReal (le_trans zero_le_one hr.le)]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (f := fun x : Vec3 => P (x, t)) (lt_trans zero_lt_one hr)).symm
  have hFubiniF := eLpNorm_spaceTime_pow_eq_integral_slice r (lt_trans zero_lt_one hr)
    hF.aestronglyMeasurable
  have hFubiniP := eLpNorm_spaceTime_pow_eq_integral_slice r (lt_trans zero_lt_one hr)
    hPm.aestronglyMeasurable
  have hSliceBound : ∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm (fun x : Vec3 => P (x, t)) (ENNReal.ofReal r)
          (volume : Measure Vec3) ≤
        ENNReal.ofReal (rieszPressureOperatorBound r hr) *
          eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r)
            (volume : Measure Vec3) := by
    filter_upwards [hPslice] with t ht
    let f : Vec3 → ℝ := fun x => F (x, t)
    let g : Vec3 → ℝ := fun x => P (x, t)
    have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    have hfc : Continuous f := hF.comp (continuous_id.prodMk continuous_const)
    have hfs : HasCompactSupport f := continuous_spaceTimeSlice_hasCompactSupport hFc t
    have hf : MemLp f (ENNReal.ofReal r) (volume : Measure Vec3) :=
      hfc.memLp_of_hasCompactSupport hfs
    have hTmem : MemLp (fun x => rieszPressureOperator r hr i j (hf.toLp f) x)
        (ENNReal.ofReal r) (volume : Measure Vec3) :=
      Lp.memLp (rieszPressureOperator r hr i j (hf.toLp f))
    have hg : MemLp g (ENNReal.ofReal r) (volume : Measure Vec3) :=
      (memLp_congr_ae ht).2 hTmem
    have hclass : hg.toLp g = rieszPressureOperator r hr i j (hf.toLp f) := by
      apply Lp.ext
      filter_upwards [hg.coeFn_toLp, ht] with x hxg hxt
      exact hxg.trans hxt
    have hTnorm : ‖rieszPressureOperator r hr i j (hf.toLp f)‖ ≤
        rieszPressureOperatorBound r hr * ‖hf.toLp f‖ := by
      calc
        ‖rieszPressureOperator r hr i j (hf.toLp f)‖ ≤
            ‖rieszPressureOperator r hr i j‖ * ‖hf.toLp f‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ rieszPressureOperatorBound r hr * ‖hf.toLp f‖ :=
          mul_le_mul_of_nonneg_right (rieszPressureOperator_norm_le r hr i j)
            (norm_nonneg _)
    have hbound : ‖hg.toLp g‖ ≤
        rieszPressureOperatorBound r hr * ‖hf.toLp f‖ := by
      rw [hclass]
      exact hTnorm
    have hTbound := CKN.Core.Endgame.eLpNorm_le_of_toLp_norm_le hf hg hC hbound
    simpa [f, g] using hTbound
  have hSlicePowBound : ∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm (fun x : Vec3 => P (x, t)) (ENNReal.ofReal r)
          (volume : Measure Vec3) ^ r ≤
        ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
          eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r)
            (volume : Measure Vec3) ^ r := by
    filter_upwards [hSliceBound] with t ht
    calc
      eLpNorm (fun x : Vec3 => P (x, t)) (ENNReal.ofReal r) volume ^ r ≤
          (ENNReal.ofReal (rieszPressureOperatorBound r hr) *
            eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r) volume) ^ r :=
        ENNReal.rpow_le_rpow ht (le_trans zero_le_one hr.le)
      _ = ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
          eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r) volume ^ r :=
        ENNReal.mul_rpow_of_nonneg _ _ (le_trans zero_le_one hr.le)
  have hSlicePowBound' : ∀ᵐ t ∂(volume : Measure ℝ), IP t ≤
      ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r * IF t := by
    filter_upwards [hSlicePowBound, hPsliceIntegral, hFsliceIntegral] with t ht hp hf
    rw [← hp, ← hf]
    exact ht
  have hIntBound :
      (∫⁻ t, IP t ∂(volume : Measure ℝ)) ≤
        ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
          (∫⁻ t, IF t ∂(volume : Measure ℝ)) := by
    calc
      (∫⁻ t, IP t ∂(volume : Measure ℝ)) ≤
          ∫⁻ t, ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r * IF t
            ∂(volume : Measure ℝ) := lintegral_mono_ae hSlicePowBound'
      _ = ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
          (∫⁻ t, IF t ∂(volume : Measure ℝ)) :=
        lintegral_const_mul'' _ hIFmeas.aemeasurable
  have hFubiniIF :
      eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r =
        ∫⁻ t, IF t ∂(volume : Measure ℝ) := by
    calc
      eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r =
          ∫⁻ t, eLpNorm (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r)
            (volume : Measure Vec3) ^ r ∂(volume : Measure ℝ) := hFubiniF
      _ = ∫⁻ t, IF t ∂(volume : Measure ℝ) := lintegral_congr_ae hFsliceIntegral
  have hGlobalPow :
      eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r ≤
        ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
          eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r := by
    calc
      eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r =
          ∫⁻ t, eLpNorm (fun x : Vec3 => P (x, t)) (ENNReal.ofReal r)
            (volume : Measure Vec3) ^ r ∂(volume : Measure ℝ) := hFubiniP
      _ = ∫⁻ t, IP t ∂(volume : Measure ℝ) := lintegral_congr_ae hPsliceIntegral
      _ ≤ ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
          (∫⁻ t, IF t ∂(volume : Measure ℝ)) := hIntBound
      _ = ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
          eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r :=
        congrArg (fun z => ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r * z)
          hFubiniIF.symm
  have hGlobalNorm := ENNReal.rpow_le_rpow hGlobalPow (by positivity : 0 ≤ 1 / r)
  have hFinalBound : eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ≤
      ENNReal.ofReal (rieszPressureOperatorBound r hr) *
        eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := calc
    eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) =
        (eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r) ^ (1 / r) := by
      rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hr0, ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal (rieszPressureOperatorBound r hr) ^ r *
        eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r) ^ (1 / r) :=
      hGlobalNorm
    _ = ENNReal.ofReal (rieszPressureOperatorBound r hr) *
        eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / r)]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      rw [one_div, mul_inv_cancel₀ hr0, ENNReal.rpow_one]
      rw [ENNReal.rpow_one]
  have hPmem : MemLp P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
    change eLpNorm P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) < ∞
    apply lt_of_le_of_lt hFinalBound
    exact ENNReal.mul_lt_top (by simp) hFmem.eLpNorm_lt_top
  exact ⟨P, hPm, hPslice, hPmem, hFinalBound⟩

end CKN.Leray

end
