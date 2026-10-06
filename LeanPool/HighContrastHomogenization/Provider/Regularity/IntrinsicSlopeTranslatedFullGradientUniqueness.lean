/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.CongruenceAE
public import LeanPool.HighContrastHomogenization.Provider.Regularity.IntrinsicSlopeTranslationStability

/-!
# High-contrast homogenization: Provider.Regularity.IntrinsicSlopeTranslatedFullGradientUniqueness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Intrinsic-slope uniqueness for a translated full gradient

If two intrinsically normalized corrector carriers represent the same global
full gradient after translating the first corrector component, the slopes are
equal.  The fixed-translation boundary cost is supplied by one weak corrector
row for the first carrier.
-/

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory

noncomputable section

/-- A global a.e. identity between a translated full corrector gradient and an
intrinsically normalized target full gradient identifies their slopes. -/
theorem intrinsicSlope_eq_of_translated_globalFullGradient_ae_eq_of_weakRow
    {d : ℕ} [NeZero d]
    {e e' : Vec d} {Phi Psi : NormalizedLocalH1Carrier d}
    (he : HasIntrinsicNormalizedSlope e Phi)
    (he' : HasIntrinsicNormalizedSlope e' Psi)
    (t : Vec d) (eRow : Vec d) {s : ℝ} (hs : 0 < s) (hs2 : s < 1 / 2)
    (q0 : ℕ) (N : ℝ)
    (hRow : ∀ q : ℕ, q0 ≤ q →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (q : ℤ)) s
        (fun x ↦ eRow + Phi.globalGradientRepresentative x) ≤ N)
    (hGradient : (fun x ↦ e + Phi.globalGradientRepresentative (x + t))
      =ᵐ[volume] fun x ↦ e' + Psi.globalGradientRepresentative x) :
    e = e' := by
  have hTranslatedCorrector :=
    he.tendsto_integral_globalGradient_translate_zero_of_weakRow t eRow hs hs2
      q0 N hRow
  have hLeftRaw : Tendsto
      (fun n : ℕ ↦ e +
        ∫ x, Phi.globalGradientRepresentative (x + t)
          ∂normalizedCubeMeasure (originCube d (n : ℤ)))
      atTop (nhds e) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ e) atTop (nhds e)).add
        hTranslatedCorrector
  have hLeft : Tendsto
      (fun n : ℕ ↦ ∫ x, e + Phi.globalGradientRepresentative (x + t)
        ∂normalizedCubeMeasure (originCube d (n : ℤ)))
      atTop (nhds e) := by
    apply hLeftRaw.congr'
    filter_upwards [] with n
    rw [integral_add]
    · rw [integral_const, Measure.real_def,
        normalizedCubeMeasure_apply_univ]
      simp only [ENNReal.toReal_one, one_smul]
    · exact integrable_const e
    · exact
        (Phi.memLp_globalGradientRepresentative_translate_normalizedCubeMeasure
          t n).integrable (by norm_num)
  have hRightAverage : Tendsto
      (fun n : ℕ ↦ cubeAverageVec (originCube d (n : ℤ))
        (fun x ↦ e' + Psi.globalGradientRepresentative x))
      atTop (nhds e') := by
    simpa only [HasIntrinsicNormalizedSlope,
      localGradientClassAverage_eq_globalFullGradientAverage] using he'
  have hRight : Tendsto
      (fun n : ℕ ↦ ∫ x, e' + Psi.globalGradientRepresentative x
        ∂normalizedCubeMeasure (originCube d (n : ℤ)))
      atTop (nhds e') := by
    apply hRightAverage.congr'
    filter_upwards [] with n
    apply cubeAverageVec_eq_integral_normalizedCubeMeasure_of_integrable
    exact ((memLp_const e').add
      (Psi.memLp_globalGradientRepresentative_normalizedCubeMeasure n)).integrable
        (by norm_num)
  have hSame : (fun n : ℕ ↦ ∫ x, e + Phi.globalGradientRepresentative (x + t)
      ∂normalizedCubeMeasure (originCube d (n : ℤ))) =
      fun n : ℕ ↦ ∫ x, e' + Psi.globalGradientRepresentative x
        ∂normalizedCubeMeasure (originCube d (n : ℤ)) := by
    funext n
    apply integral_congr_ae
    have hCube : (fun x ↦ e + Phi.globalGradientRepresentative (x + t))
        =ᵐ[cubeMeasure (originCube d (n : ℤ))]
        fun x ↦ e' + Psi.globalGradientRepresentative x := by
      simpa only [cubeMeasure] using
        hGradient.filter_mono (ae_mono Measure.restrict_le_self)
    exact Gagliardo.ae_normalizedCubeMeasure_iff.mpr hCube
  have hRightOnLeft : Tendsto
      (fun n : ℕ ↦ ∫ x, e + Phi.globalGradientRepresentative (x + t)
        ∂normalizedCubeMeasure (originCube d (n : ℤ)))
      atTop (nhds e') := by
    rw [hSame]
    exact hRight
  exact tendsto_nhds_unique hLeft hRightOnLeft

end

end HighContrast
end HCPolySupport
