/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSuitable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSupDisplay
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Time-integrated harmonic pressure bound

CKN's interior estimate on each harmonic slice gives a uniform estimate after
integration in time (`lem:pressure-split`).
-/

public section


open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The interior `L∞` norm of almost every harmonic slice has a time-integral
bound with an absolute constant. -/
theorem blowupHarmonicSlices_time_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (h : ParabolicPoint → ℝ) (J : Set ℝ),
        (∀ᵐ t ∂(volume.restrict J),
          MemLp (fun x : Vec3 => h (x, t))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (CKN.euclideanBall 0 1)) ∧
          CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
            (fun x : Vec3 => h (x, t))) →
        (∫⁻ t in J,
          eLpNorm (fun x : Vec3 => h (x, t)) ⊤
            (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ^
              (3 / 2 : ℝ)) ≤
          C * (∫⁻ t in J,
            eLpNorm (fun x : Vec3 => h (x, t))
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (CKN.euclideanBall 0 1)) ^
                (3 / 2 : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := CKN.Foundation.Heat.weak_harmonic_interior_sup
  let C : ℝ := max C₀ 0
  let D : ℝ≥0∞ := ENNReal.ofReal C ^ (3 / 2 : ℝ)
  have hDfinite : D < ⊤ := by
    dsimp [D]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  refine ⟨D, hDfinite, ?_⟩
  intro h J hSlices
  have hpoint : ∀ᵐ t ∂(volume.restrict J),
      eLpNorm (fun x : Vec3 => h (x, t)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ^
            (3 / 2 : ℝ) ≤
        D * eLpNorm (fun x : Vec3 => h (x, t))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (CKN.euclideanBall 0 1)) ^
            (3 / 2 : ℝ) := by
    filter_upwards [hSlices] with t ht
    have hraw := hC₀ (fun x : Vec3 => h (x, t)) 0 1
      (by norm_num : (0 : ℝ) < 1) ht.1 ht.2
    have hraw' : eLpNorm (fun x : Vec3 => h (x, t)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ≤
        ENNReal.ofReal (C₀ * lpNorm (fun x : Vec3 => h (x, t))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (CKN.euclideanBall 0 1))) := by
      norm_num at hraw ⊢
      exact hraw
    have hCnonneg : 0 ≤ C := le_max_right _ _
    have hCmon : C₀ ≤ C := le_max_left _ _
    have hnormnonneg : 0 ≤ lpNorm (fun x : Vec3 => h (x, t))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (CKN.euclideanBall 0 1)) := lpNorm_nonneg
    have hbase : eLpNorm (fun x : Vec3 => h (x, t)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ≤
        ENNReal.ofReal C *
          eLpNorm (fun x : Vec3 => h (x, t))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (CKN.euclideanBall 0 1)) := by
      calc
        _ ≤ ENNReal.ofReal (C₀ * lpNorm (fun x : Vec3 => h (x, t))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (CKN.euclideanBall 0 1))) := hraw'
        _ ≤ ENNReal.ofReal (C * lpNorm (fun x : Vec3 => h (x, t))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (CKN.euclideanBall 0 1))) := by
              exact ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right hCmon hnormnonneg)
        _ = _ := by
          rw [ENNReal.ofReal_mul hCnonneg,
            ofReal_lpNorm ht.1]
    have hpow := ENNReal.rpow_le_rpow hbase (by norm_num : (0 : ℝ) ≤ 3 / 2)
    simpa only [D, ENNReal.mul_rpow_of_nonneg _ _
      (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hpow
  have hInt := lintegral_mono_ae hpoint
  rw [lintegral_const_mul' D _ hDfinite.ne] at hInt
  exact hInt

end ESS
