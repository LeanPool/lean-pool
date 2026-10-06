/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszSliceBound
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarTime

/-!
# Blowup Riesz Far Bound

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- Exterior support and a uniform tensor-slice bound give the quantitative
far-field pressure estimate on a bounded past cylinder. -/
theorem blowup_rieszPressure_exterior_mass_bound
    : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
        (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume : Measure (Vec3 × ℝ)))
        (L R a b M : ℝ),
        0 < L → 0 < R → R ≤ 3 * L / 4 → a < b →
        (∀ i j z, z.1 ∈ CKN.euclideanBall 0 L → F i j z = 0) →
        (∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
          ∀ i j : Fin 3,
            lpNorm (fun x : Vec3 => F i j (x,t))
              (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ M) →
      (∫⁻ z, ENNReal.ofReal (|CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) F hF z|) ^
          (3 / 2 : ℝ)
        ∂((volume.restrict (CKN.euclideanBall 0 R)).prod
          (volume.restrict (Ioo a b)))) ≤
        volume (Ioo a b) *
          (C * ENNReal.ofReal ((L ^ 2)⁻¹) *
            ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
              (3 / 2 : ℝ) (by norm_num) * (9 * M)) *
            volume (CKN.euclideanBall (0 : Vec3) R) ^ (2 / 3 : ℝ)) ^
              (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hBound⟩ := blowup_harmonic_far_spaceTime_mass_bound
  refine ⟨C, hC, ?_⟩
  intro F hF L R a b M hL hR hRL hab hzero hinput
  let p : Vec3 × ℝ → ℝ := CKN.Leray.rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) F hF
  have hHarm := blowup_rieszPressureSpaceTime_exterior_harmonic_slices
    F hF (CKN.euclideanBall 0 L) (CKN.isOpen_euclideanBall 0 L) hzero hab
  have hNorm := blowup_rieszPressureSpaceTime_slice_norm_bound
    F hF M hinput
  have hExp : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hSlices : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      MemLp (fun x : Vec3 => p (x,t)) (3 / 2 : ℝ≥0∞) volume ∧
      eLpNorm (fun x : Vec3 => p (x,t)) (3 / 2 : ℝ≥0∞) volume ≤
        ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
          (3 / 2 : ℝ) (by norm_num) * (9 * M)) ∧
      CKN.Foundation.Heat.WeaklyHarmonicOn
        (CKN.euclideanBall 0 L) (fun x : Vec3 => p (x,t)) := by
    filter_upwards [hNorm, hHarm] with t ht hh
    exact ⟨by simpa only [p, ← hExp] using ht.1,
      by simpa only [p, ← hExp] using ht.2, hh⟩
  have hpMeas : Measurable p :=
    CKN.Leray.rieszPressureSpaceTime_measurable (3 / 2 : ℝ)
      (by norm_num) F hF
  exact hBound p L R (Ioo a b)
    (ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
      (3 / 2 : ℝ) (by norm_num) * (9 * M)))
    hL hR hRL hpMeas.aestronglyMeasurable hSlices

end ESS
