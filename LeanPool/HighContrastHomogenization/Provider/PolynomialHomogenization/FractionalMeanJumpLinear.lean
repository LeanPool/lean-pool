/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalChainMeanTelescope

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalMeanJumpLinear

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Linear cross-average control of mean jumps
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Volume restricted to `E` and rescaled by the inverse of `volume E` for mean jumps. -/
@[expose]
public noncomputable def normalizedJumpMeasure (E : Set (Vec d)) :
    Measure (Vec d) :=
  (volume E)⁻¹ • volume.restrict E

private theorem normalizedJumpMeasure_isProbability {E : Set (Vec d)}
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤) :
    IsProbabilityMeasure (normalizedJumpMeasure E) := by
  refine ⟨?_⟩
  rw [normalizedJumpMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hEpos.ne' hEtop

private theorem integral_normalizedJumpMeasure_eq_volumeAverageVec
    {E : Set (Vec d)} {G : Vec d → Vec d}
    (hG : Integrable G (volume.restrict E)) :
    ∫ x, G x ∂normalizedJumpMeasure E = volumeAverageVec E G := by
  funext i
  have hproj : ∫ x in E, G x i ∂volume = (∫ x in E, G x ∂volume) i := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).integral_comp_comm hG
  rw [normalizedJumpMeasure, integral_smul_measure, volumeAverageVec,
    volumeAverage, Pi.smul_apply, smul_eq_mul, ENNReal.toReal_inv, hproj]

private theorem integrable_normalizedJumpMeasure
    {E : Type*} [NormedAddCommGroup E] {V : Set (Vec d)}
    (hVpos : 0 < volume V) {F : Vec d → E}
    (hF : Integrable F (volume.restrict V)) :
    Integrable F (normalizedJumpMeasure V) :=
  hF.smul_measure (ENNReal.inv_ne_top.mpr hVpos.ne')

private theorem enorm_hilbertVec_sub_eq_ofReal_euclideanDist
    (v w : Vec d) :
    ‖HilbertVec.ofVec v - HilbertVec.ofVec w‖ₑ =
      ENNReal.ofReal (euclideanDist v w) := by
  rw [← ofReal_norm, ← euclideanDist_eq_norm_sub_ofVec]

/-- The distance between two vector-valued volume averages is bounded by the
normalized cross average of pointwise distances. -/
theorem edist_volumeAverageVec_le_crossDistanceAverage
    {E F : Set (Vec d)}
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hFpos : 0 < volume F) (hFtop : volume F ≠ ⊤)
    {G : Vec d → Vec d}
    (hGE : Integrable G (volume.restrict E))
    (hGF : Integrable G (volume.restrict F)) :
    edist (HilbertVec.ofVec (volumeAverageVec E G))
        (HilbertVec.ofVec (volumeAverageVec F G)) ≤
      (volume E)⁻¹ * (volume F)⁻¹ *
        ∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume := by
  let μE := normalizedJumpMeasure E
  let μF := normalizedJumpMeasure F
  let GH : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (G x)
  have : IsProbabilityMeasure μE :=
    normalizedJumpMeasure_isProbability hEpos hEtop
  have : IsProbabilityMeasure μF :=
    normalizedJumpMeasure_isProbability hFpos hFtop
  have hGHE : Integrable GH μE :=
    integrable_normalizedJumpMeasure hEpos
      ((HilbertVec.ofVecL d).integrable_comp hGE)
  have hGHF : Integrable GH μF :=
    integrable_normalizedJumpMeasure hFpos
      ((HilbertVec.ofVecL d).integrable_comp hGF)
  have hmeansE : ∫ x, GH x ∂μE =
      HilbertVec.ofVec (volumeAverageVec E G) := by
    rw [show ∫ x, GH x ∂μE = HilbertVec.ofVec (∫ x, G x ∂μE) by
      simpa [GH] using (HilbertVec.ofVecL d).integral_comp_comm
        (integrable_normalizedJumpMeasure hEpos hGE),
      integral_normalizedJumpMeasure_eq_volumeAverageVec hGE]
  have hmeansF : ∫ y, GH y ∂μF =
      HilbertVec.ofVec (volumeAverageVec F G) := by
    rw [show ∫ y, GH y ∂μF = HilbertVec.ofVec (∫ y, G y ∂μF) by
      simpa [GH] using (HilbertVec.ofVecL d).integral_comp_comm
        (integrable_normalizedJumpMeasure hFpos hGF),
      integral_normalizedJumpMeasure_eq_volumeAverageVec hGF]
  have houter :
      ‖(∫ x, GH x ∂μE) - (∫ y, GH y ∂μF)‖ₑ ≤
        ∫⁻ x, ∫⁻ y, ‖GH x - GH y‖ₑ ∂μF ∂μE := by
    have hrewrite :
        (∫ x, GH x ∂μE) - (∫ y, GH y ∂μF) =
          ∫ x, (GH x - ∫ y, GH y ∂μF) ∂μE := by
      rw [integral_sub hGHE (integrable_const _), integral_const]
      simp
    rw [hrewrite]
    calc
      ‖∫ x, GH x - ∫ y, GH y ∂μF ∂μE‖ₑ ≤
          ∫⁻ x, ‖GH x - ∫ y, GH y ∂μF‖ₑ ∂μE :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, ∫⁻ y, ‖GH x - GH y‖ₑ ∂μF ∂μE := by
        apply lintegral_mono
        intro x
        have hinnerRewrite :
            GH x - ∫ y, GH y ∂μF =
              ∫ y, (GH x - GH y) ∂μF := by
          rw [integral_sub (integrable_const _) hGHF, integral_const]
          simp
        change ‖GH x - ∫ y, GH y ∂μF‖ₑ ≤
          ∫⁻ y, ‖GH x - GH y‖ₑ ∂μF
        rw [hinnerRewrite]
        exact enorm_integral_le_lintegral_enorm _
  rw [hmeansE, hmeansF] at houter
  calc
    edist (HilbertVec.ofVec (volumeAverageVec E G))
        (HilbertVec.ofVec (volumeAverageVec F G)) ≤
        ∫⁻ x, ∫⁻ y, ‖GH x - GH y‖ₑ ∂μF ∂μE := by
      simpa only [edist_eq_enorm_sub] using houter
    _ =
        ∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (euclideanDist (G x) (G y)) ∂μF ∂μE := by
      simp_rw [GH, enorm_hilbertVec_sub_eq_ofReal_euclideanDist]
    _ = (volume E)⁻¹ * (volume F)⁻¹ *
        ∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume := by
      simp only [μE, μF, normalizedJumpMeasure, lintegral_smul_measure,
        smul_eq_mul]
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hFpos.ne')]
      ac_rfl

end

end HighContrast
end HCPolySupport
