/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The local L^{3/2} bound for mixed-norm pressures

A space-time function in L²_t L⁶_x is locally in L^{3/2}: on a bounded
cylinder K × J, the finite-measure embeddings L⁶(K) ⊂ L^{3/2}(K) and
L²(J) ⊂ L^{3/2}(J) give `eq:force-pressure-local`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The L^p norm of the time slices of a strongly measurable space-time
function is measurable in time. -/
theorem measurable_eLpNorm_slice {P : Vec3 × ℝ → ℝ} (hP : StronglyMeasurable P)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (μ : Measure Vec3) [SFinite μ] :
    Measurable fun t : ℝ => eLpNorm (fun x : Vec3 => P (x, t)) p μ := by
  have hslice (t : ℝ) : AEStronglyMeasurable (fun x : Vec3 => P (x, t)) μ :=
    (hP.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have heq : (fun t : ℝ => eLpNorm (fun x : Vec3 => P (x, t)) p μ) =
      fun t => (∫⁻ x, ‖P (x, t)‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    funext t
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hslice t)]
  rw [heq]
  refine Measurable.pow_const ?_ _
  exact Measurable.lintegral_prod_left'
    (f := fun q : Vec3 × ℝ => ‖P q‖ₑ ^ p.toReal) (hP.measurable.enorm.pow_const _)

private theorem forcePressure_rpow_rpow (x : ℝ≥0∞) {a b : ℝ} (hab : a * b = 1) :
    (x ^ a) ^ b = x := by
  rw [← ENNReal.rpow_mul, hab, ENNReal.rpow_one]

/-- The local bound `eq:force-pressure-local`: on a cylinder K × J inside
the slab (0, T), the L^{3/2} norm is at most
|K|^{1/2} |J|^{1/6} times the L²_t L⁶_x norm on the slab. -/
theorem eLpNorm_threeHalves_cylinder_le {P : Vec3 × ℝ → ℝ} (hP : StronglyMeasurable P)
    {T : ℝ} (K : Set Vec3) {I : Set ℝ} (hIT : I ⊆ Ioo 0 T) :
    eLpNorm P (ENNReal.ofReal (3 / 2 : ℝ)) ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ I)) ≤
      volume K ^ (1 / 2 : ℝ) * volume I ^ (1 / 6 : ℝ) *
        (∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => P (x, t)) (ENNReal.ofReal (6 : ℝ))
          (volume : Measure Vec3) ^ (2 : ℝ) ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) := by
  set q : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  set r : ℝ≥0∞ := ENNReal.ofReal (6 : ℝ)
  have hq0 : q ≠ 0 := by simp [q]
  have hr0 : r ≠ 0 := by simp [r]
  have hqr : q ≤ r := ENNReal.ofReal_le_ofReal (by norm_num)
  have hqReal : q.toReal = 3 / 2 := ENNReal.toReal_ofReal (by norm_num)
  have hrReal : r.toReal = 6 := ENNReal.toReal_ofReal (by norm_num)
  let μK : Measure Vec3 := (volume : Measure Vec3).restrict K
  let μI : Measure ℝ := (volume : Measure ℝ).restrict I
  let a : ℝ → ℝ≥0∞ := fun t => eLpNorm (fun x : Vec3 => P (x, t)) r volume
  let b : ℝ → ℝ≥0∞ := fun t => eLpNorm (fun x : Vec3 => P (x, t)) q μK
  have ha : Measurable a := measurable_eLpNorm_slice hP hr0 ENNReal.ofReal_ne_top volume
  have hslice (t : ℝ) : AEStronglyMeasurable (fun x : Vec3 => P (x, t)) μK :=
    (hP.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  -- the space-time norm through slices
  have hmeasure : (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ I) = μK.prod μI := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hstep1 : eLpNorm P q ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ I)) =
      (∫⁻ t, b t ^ (3 / 2 : ℝ) ∂μI) ^ (2 / 3 : ℝ) := by
    rw [hmeasure, eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top
      hP.aestronglyMeasurable, hqReal,
      lintegral_prod_symm' _ (hP.measurable.enorm.pow_const _)]
    have hb (t : ℝ) : b t ^ (3 / 2 : ℝ) = ∫⁻ x, ‖P (x, t)‖ₑ ^ (3 / 2 : ℝ) ∂μK := by
      simp only [b]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top (hslice t), hqReal]
      exact forcePressure_rpow_rpow _ (by norm_num)
    simp only [hb]
    norm_num
  -- Hölder in space
  have hstep2 (t : ℝ) : b t ≤ a t * volume K ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqr (hslice t)
    rw [hqReal, hrReal, Measure.restrict_apply_univ] at h
    refine h.trans ?_
    have hexp : (1 / (3 / 2 : ℝ) - 1 / 6) = 1 / 2 := by norm_num
    rw [hexp]
    gcongr
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hstep3 : ∫⁻ t, b t ^ (3 / 2 : ℝ) ∂μI ≤
      volume K ^ (3 / 4 : ℝ) * ∫⁻ t, a t ^ (3 / 2 : ℝ) ∂μI := by
    rw [← lintegral_const_mul _ (ha.pow_const _)]
    · apply lintegral_mono
      intro t
      calc
        b t ^ (3 / 2 : ℝ) ≤ (a t * volume K ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) := by
          gcongr
          exact hstep2 t
        _ = volume K ^ (3 / 4 : ℝ) * a t ^ (3 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, mul_comm]
          norm_num
  -- Hölder in time
  have hstep4 : (∫⁻ t, a t ^ (3 / 2 : ℝ) ∂μI) ^ (2 / 3 : ℝ) ≤
      (∫⁻ t, a t ^ (2 : ℝ) ∂μI) ^ (1 / 2 : ℝ) * volume I ^ (1 / 6 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μI)
      (show q ≤ (2 : ℝ≥0∞) from ENNReal.ofReal_le_ofNat.2 (by norm_num))
      ha.aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top ha.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ha.aestronglyMeasurable,
      hqReal, Measure.restrict_apply_univ] at h
    simp only [enorm_eq_self, ENNReal.toReal_ofNat] at h
    have hexp : (1 / (3 / 2 : ℝ) - 1 / 2) = 1 / 6 := by norm_num
    have h23 : (1 / (3 / 2 : ℝ)) = 2 / 3 := by norm_num
    rw [hexp, h23] at h
    exact h
  have hstep5 : ∫⁻ t, a t ^ (2 : ℝ) ∂μI ≤ ∫⁻ t in Ioo 0 T, a t ^ (2 : ℝ) :=
    lintegral_mono_set hIT
  rw [hstep1]
  calc
    (∫⁻ t, b t ^ (3 / 2 : ℝ) ∂μI) ^ (2 / 3 : ℝ) ≤
        (volume K ^ (3 / 4 : ℝ) * ∫⁻ t, a t ^ (3 / 2 : ℝ) ∂μI) ^ (2 / 3 : ℝ) := by
      gcongr
    _ = volume K ^ (1 / 2 : ℝ) * (∫⁻ t, a t ^ (3 / 2 : ℝ) ∂μI) ^ (2 / 3 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
      norm_num
    _ ≤ volume K ^ (1 / 2 : ℝ) *
        ((∫⁻ t, a t ^ (2 : ℝ) ∂μI) ^ (1 / 2 : ℝ) * volume I ^ (1 / 6 : ℝ)) := by
      gcongr
    _ ≤ volume K ^ (1 / 2 : ℝ) *
        ((∫⁻ t in Ioo 0 T, a t ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * volume I ^ (1 / 6 : ℝ)) := by
      gcongr
    _ = volume K ^ (1 / 2 : ℝ) * volume I ^ (1 / 6 : ℝ) *
        (∫⁻ t in Ioo 0 T, a t ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by ring

end CKN.Leray
