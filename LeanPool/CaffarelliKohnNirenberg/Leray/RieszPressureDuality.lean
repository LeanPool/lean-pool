/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Space-time Riesz pressure duality

The pressure operators are paired through the integral on the product space.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

theorem rieszPressureLpPairing_bound
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q)
    (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
    ‖∫ z, (u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z‖ ≤ ‖u‖ * ‖v‖ := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  have : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q) :=
    Real.HolderConjugate.ennrealOfReal hHolder
  have hu : MemLp (u : Vec3 × ℝ → ℝ) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) := Lp.memLp u
  have hv : MemLp (v : Vec3 × ℝ → ℝ) (ENNReal.ofReal q)
      (volume : Measure (Vec3 × ℝ)) := Lp.memLp v
  have hHolderIntegral := integral_mul_norm_le_Lp_mul_Lq hHolder hu hv
  have hLpNormU : lpNorm (u : Vec3 × ℝ → ℝ) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) =
    (∫ z, ‖(u : Vec3 × ℝ → ℝ) z‖ ^ r ∂(volume : Measure (Vec3 × ℝ))) ^ (1 / r) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hr)).ne'
      ENNReal.ofReal_ne_top hu.aestronglyMeasurable,
      ENNReal.toReal_ofReal (le_of_lt (lt_trans zero_lt_one hr))]
    simp only [one_div]
  have hLpNormV : lpNorm (v : Vec3 × ℝ → ℝ) (ENNReal.ofReal q)
      (volume : Measure (Vec3 × ℝ)) =
    (∫ z, ‖(v : Vec3 × ℝ → ℝ) z‖ ^ q ∂(volume : Measure (Vec3 × ℝ))) ^ (1 / q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hq)).ne'
      ENNReal.ofReal_ne_top hv.aestronglyMeasurable,
      ENNReal.toReal_ofReal (le_of_lt (lt_trans zero_lt_one hq))]
    simp only [one_div]
  have hNormU :
      (∫ z, ‖(u : Vec3 × ℝ → ℝ) z‖ ^ r ∂(volume : Measure (Vec3 × ℝ))) ^ (1 / r) = ‖u‖ := by
    rw [← hLpNormU, Lp.norm_def, MeasureTheory.toReal_eLpNorm]
  have hNormV :
      (∫ z, ‖(v : Vec3 × ℝ → ℝ) z‖ ^ q ∂(volume : Measure (Vec3 × ℝ))) ^ (1 / q) = ‖v‖ := by
    rw [← hLpNormV, Lp.norm_def, MeasureTheory.toReal_eLpNorm]
  calc
    ‖∫ z, (u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z‖ ≤
        ∫ z, ‖(u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ z, ‖(u : Vec3 × ℝ → ℝ) z‖ * ‖(v : Vec3 × ℝ → ℝ) z‖ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact norm_mul _ _
    _ ≤ (∫ z, ‖(u : Vec3 × ℝ → ℝ) z‖ ^ r ∂(volume : Measure (Vec3 × ℝ))) ^ (1 / r) *
        (∫ z, ‖(v : Vec3 × ℝ → ℝ) z‖ ^ q ∂(volume : Measure (Vec3 × ℝ))) ^ (1 / q) :=
      hHolderIntegral
    _ = ‖u‖ * ‖v‖ := by rw [hNormU, hNormV]

/-- The linear pairing of an `L^r` field with a fixed conjugate `L^q` field. -/
@[expose]
def rieszPressureLpPairingLinear
    (r q : ℝ)
    (hHolder : r.HolderConjugate q)
    (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
    Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) →ₗ[ℝ] ℝ := by
  letI : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q) :=
    Real.HolderConjugate.ennrealOfReal hHolder
  let hm (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) : ℝ :=
    ∫ z, (u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z
  exact {
    toFun := hm
    map_add' := by
      intro u₁ u₂
      have hInt₁ : Integrable
          (fun z : Vec3 × ℝ => (u₁ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z) :=
        (Lp.memLp u₁).integrable_mul (Lp.memLp v)
      have hInt₂ : Integrable
          (fun z : Vec3 × ℝ => (u₂ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z) :=
        (Lp.memLp u₂).integrable_mul (Lp.memLp v)
      have hAE : (fun z : Vec3 × ℝ =>
          ((u₁ + u₂ : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
            Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z) =ᵐ[volume]
          fun z => (u₁ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z +
            (u₂ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z := by
        filter_upwards [Lp.coeFn_add u₁ u₂] with z hz
        have hz' : ((u₁ + u₂ : Lp ℝ (ENNReal.ofReal r)
            (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) z =
            (u₁ : Vec3 × ℝ → ℝ) z + (u₂ : Vec3 × ℝ → ℝ) z := by
          simpa only [Pi.add_apply] using hz
        calc
          _ = ((u₁ : Vec3 × ℝ → ℝ) z + (u₂ : Vec3 × ℝ → ℝ) z) *
              (v : Vec3 × ℝ → ℝ) z :=
            congrArg (fun w : ℝ => w * (v : Vec3 × ℝ → ℝ) z) hz'
          _ = (u₁ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z +
              (u₂ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z := by
            simp only [add_mul]
      calc
        hm (u₁ + u₂) = ∫ z, (u₁ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z +
            (u₂ : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z := integral_congr_ae hAE
        _ = hm u₁ + hm u₂ := by
          simpa only [hm] using integral_add hInt₁ hInt₂
    map_smul' := by
      intro c u
      have hAE : (fun z : Vec3 × ℝ =>
          ((c • u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
            Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z) =ᵐ[volume]
          fun z => c * ((u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z) := by
        filter_upwards [Lp.coeFn_smul c u] with z hz
        calc
          ((c • u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
              Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z =
              (c • (u : Vec3 × ℝ → ℝ) z) * (v : Vec3 × ℝ → ℝ) z :=
            congrArg (fun w : ℝ => w * (v : Vec3 × ℝ → ℝ) z) hz
          _ = c * ((u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z) := by
            simp only [smul_eq_mul]
            ring
      calc
        hm (c • u) = ∫ z, c * ((u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z) :=
          integral_congr_ae hAE
        _ = c * hm u := by
          simpa only [hm] using integral_const_mul c
            (fun z : Vec3 × ℝ => (u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z)
  }

/-- The Hölder pairing as a continuous functional, used by
`lem:riesz-duality`. -/
@[expose]
def rieszPressureLpPairingCLM
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q)
    (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq.le⟩
    Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ := by
  letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  let f := rieszPressureLpPairingLinear r q hHolder v
  exact f.mkContinuous ‖v‖ (by
    intro u
    calc
      ‖f u‖ ≤ ‖u‖ * ‖v‖ := rieszPressureLpPairing_bound r hr q hq hHolder u v
      _ = ‖v‖ * ‖u‖ := mul_comm _ _)

/-- Evaluation of `rieszPressureLpPairingCLM`, used by
`lem:riesz-duality`. -/
theorem rieszPressureLpPairingCLM_apply
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q)
    (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ)))
    (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq.le⟩
    rieszPressureLpPairingCLM r hr q hq hHolder v u =
      ∫ z, (u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z := by
  rfl

end CKN.Leray

end
