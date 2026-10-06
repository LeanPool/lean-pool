/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalMeanJumpLinear
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalGagliardoSquareFunction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.FractionalMeanJumpAmplitudeAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembly of a linear fractional-amplitude mean-jump estimate
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A pointwise cross-ball estimate against the global Gagliardo amplitude
integrates to a linear bound for the corresponding jump of volume averages. -/
theorem edist_volumeAverageVec_le_amplitudeAverage_of_cross
    {U E F : Set (Vec d)} {s : ℝ} {G : Vec d → Vec d}
    (hEmeas : MeasurableSet E)
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hFpos : 0 < volume F) (hFtop : volume F ≠ ⊤)
    (hGE : Integrable G (volume.restrict E))
    (hGF : Integrable G (volume.restrict F))
    {C : ℝ≥0∞} (hCtop : C ≠ ⊤)
    (hcross : ∀ x ∈ E,
      (∫⁻ y in F, ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume) ≤
        volume F * C * fractionalGagliardoAmplitude U s G x) :
    edist (HilbertVec.ofVec (volumeAverageVec E G))
        (HilbertVec.ofVec (volumeAverageVec F G)) ≤
      C * (volume E)⁻¹ *
        ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume := by
  have hbase := edist_volumeAverageVec_le_crossDistanceAverage
    hEpos hEtop hFpos hFtop hGE hGF
  have hinter :
      (∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume) ≤
        volume F * C *
          ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume := by
    calc
      (∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume) ≤
          ∫⁻ x in E, volume F * C *
            fractionalGagliardoAmplitude U s G x ∂volume :=
        setLIntegral_mono' hEmeas hcross
      _ = volume F * C *
          ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume := by
        rw [lintegral_const_mul']
        exact ENNReal.mul_ne_top hFtop hCtop
  calc
    edist (HilbertVec.ofVec (volumeAverageVec E G))
        (HilbertVec.ofVec (volumeAverageVec F G)) ≤
        (volume E)⁻¹ * (volume F)⁻¹ *
          (∫⁻ x in E, ∫⁻ y in F,
            ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume) := hbase
    _ ≤ (volume E)⁻¹ * (volume F)⁻¹ *
        (volume F * C *
          ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume) :=
      mul_le_mul_right hinter _
    _ = C * (volume E)⁻¹ *
        ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume := by
      calc
        (volume E)⁻¹ * (volume F)⁻¹ *
            (volume F * C *
              ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume) =
            (volume E)⁻¹ * ((volume F)⁻¹ * volume F) * C *
              ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume := by
          ac_rfl
        _ = C * (volume E)⁻¹ *
            ∫⁻ x in E, fractionalGagliardoAmplitude U s G x ∂volume := by
          rw [ENNReal.inv_mul_cancel hFpos.ne' hFtop]
          simp only [mul_one]
          ac_rfl

end

end HighContrast
end HCPolySupport
