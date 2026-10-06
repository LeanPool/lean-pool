/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszNear
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSupDisplay

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A globally bounded `L^(3/2)` function that is harmonic on a large ball
is small on a fixed inner ball. This is the interior estimate for the far
pressure in `prop:blowup-limit`. -/
theorem blowup_harmonic_far_local_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (h : Vec3 → ℝ) (L R : ℝ), 0 < L → 0 < R →
        R ≤ 3 * L / 4 →
        MemLp h (3 / 2 : ℝ≥0∞) (volume : Measure Vec3) →
        CKN.Foundation.Heat.WeaklyHarmonicOn
          (CKN.euclideanBall 0 L) h →
        eLpNorm h ⊤ (volume.restrict (CKN.euclideanBall 0 R)) ≤
          C * ENNReal.ofReal ((L ^ 2)⁻¹) *
            eLpNorm h (3 / 2 : ℝ≥0∞) volume := by
  obtain ⟨C₀, hC₀⟩ := CKN.Foundation.Heat.weak_harmonic_interior_sup
  let C : ℝ≥0∞ := ENNReal.ofReal (max C₀ 0)
  have hCfin : C < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨C, hCfin, ?_⟩
  intro h L R hL hR hRL hmem hweak
  let BL := CKN.euclideanBall (0 : Vec3) L
  let BI := CKN.euclideanBall (0 : Vec3) (3 * L / 4)
  let BR := CKN.euclideanBall (0 : Vec3) R
  have hExp : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hsubR : BR ⊆ BI := by
    intro x hx
    exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : 0 < 3 * L / 4)).2
      ((CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx |>.trans_le hRL)
  have hmemL : MemLp h (3 / 2 : ℝ≥0∞) (volume.restrict BL) :=
    hmem.mono_measure Measure.restrict_le_self
  have hlocal := hC₀ h 0 L hL (by simpa only [BL, hExp] using hmemL) hweak
  have hlocal' : eLpNorm h ⊤ (volume.restrict BI) ≤
      ENNReal.ofReal (C₀ * (L ^ 2)⁻¹ *
        lpNorm h (3 / 2 : ℝ≥0∞) (volume.restrict BL)) := by
    simpa only [BI, BL, hExp] using hlocal
  have hnormLocal : lpNorm h (3 / 2 : ℝ≥0∞) (volume.restrict BL) ≤
      lpNorm h (3 / 2 : ℝ≥0∞) volume := by
    exact ENNReal.toReal_mono hmem.eLpNorm_ne_top
      (eLpNorm_mono_measure h Measure.restrict_le_self)
  have hnonneg : 0 ≤ (L ^ 2)⁻¹ := by positivity
  have hcoef : C₀ ≤ max C₀ 0 := le_max_left _ _
  have hraw : C₀ * (L ^ 2)⁻¹ *
        lpNorm h (3 / 2 : ℝ≥0∞) (volume.restrict BL) ≤
      max C₀ 0 * (L ^ 2)⁻¹ *
        lpNorm h (3 / 2 : ℝ≥0∞) volume := by
    calc
      _ ≤ max C₀ 0 * (L ^ 2)⁻¹ *
          lpNorm h (3 / 2 : ℝ≥0∞) (volume.restrict BL) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hnonneg) lpNorm_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hnormLocal
        (mul_nonneg (le_max_right _ _) hnonneg)
  calc
    eLpNorm h ⊤ (volume.restrict BR) ≤
        eLpNorm h ⊤ (volume.restrict BI) :=
      eLpNorm_mono_measure h (Measure.restrict_mono_set volume hsubR)
    _ ≤ ENNReal.ofReal (C₀ * (L ^ 2)⁻¹ *
          lpNorm h (3 / 2 : ℝ≥0∞) (volume.restrict BL)) := hlocal'
    _ ≤ ENNReal.ofReal (max C₀ 0 * (L ^ 2)⁻¹ *
          lpNorm h (3 / 2 : ℝ≥0∞) volume) := by
      exact ENNReal.ofReal_le_ofReal hraw
    _ = C * ENNReal.ofReal ((L ^ 2)⁻¹) *
          eLpNorm h (3 / 2 : ℝ≥0∞) volume := by
      rw [ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) hnonneg),
        ENNReal.ofReal_mul (le_max_right _ _), ofReal_lpNorm hmem]

end ESS
