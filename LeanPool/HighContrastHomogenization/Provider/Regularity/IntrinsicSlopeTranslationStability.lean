/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGradientTranslationStabilityWeakRow
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.IntrinsicSlopeGlobalGradientUniqueness
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlopeCanonical

/-!
# High-contrast homogenization: Provider.Regularity.IntrinsicSlopeTranslationStability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Intrinsic-slope stability under a fixed translation

The average of a fixed translate of the global corrector gradient differs
asymptotically negligibly from the unshifted average.  Consequently, any
carrier whose canonical global representative is that translate inherits the
same intrinsic normalized slope.
-/

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory

noncomputable section

/-- A fixed translate of an intrinsically normalized corrector gradient has
vanishing centered normalized cube average under one weak corrector row. -/
theorem HasIntrinsicNormalizedSlope.tendsto_integral_globalGradient_translate_zero_of_weakRow
    {d : ℕ} [NeZero d] {e : Vec d}
    {Phi : NormalizedLocalH1Carrier d}
    (hPhi : HasIntrinsicNormalizedSlope e Phi)
    (t : Vec d) (eRow : Vec d) {s : ℝ} (hs : 0 < s) (hs2 : s < 1 / 2)
    (q0 : ℕ) (N : ℝ)
    (hRow : ∀ q : ℕ, q0 ≤ q →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (q : ℤ)) s
        (fun x ↦ eRow + Phi.globalGradientRepresentative x) ≤ N) :
    Tendsto
      (fun n : ℕ ↦ ∫ x, Phi.globalGradientRepresentative (x + t)
        ∂normalizedCubeMeasure (originCube d (n : ℤ)))
      atTop (nhds 0) := by
  have hPhiAverage := hPhi.hasVanishingCorrectorGradientAverage
  rw [HasVanishingCorrectorGradientAverage] at hPhiAverage
  have hPhiIntegral : Tendsto
      (fun n : ℕ ↦ ∫ x, Phi.globalGradientRepresentative x
        ∂normalizedCubeMeasure (originCube d (n : ℤ)))
      atTop (nhds 0) := by
    apply hPhiAverage.congr'
    filter_upwards [] with n
    calc
      localGradientClassAverage (Phi.gradientComponent n) =
          cubeAverageVec (originCube d (n : ℤ))
            Phi.globalGradientRepresentative := by
        have h := localGradientClassAverage_eq_globalFullGradientAverage
          (0 : Vec d) Phi n
        simpa only [localGradientClassAverage_add,
          localGradientClassAverage_finiteAffineBoundaryH1, zero_add] using h
      _ = ∫ x, Phi.globalGradientRepresentative x
          ∂normalizedCubeMeasure (originCube d (n : ℤ)) := by
        apply cubeAverageVec_eq_integral_normalizedCubeMeasure_of_integrable
        exact
          (Phi.memLp_globalGradientRepresentative_normalizedCubeMeasure n).integrable
            (by norm_num)
  have hDifference : Tendsto
      (fun n : ℕ ↦
        (∫ x, Phi.globalGradientRepresentative (x + t)
          ∂normalizedCubeMeasure (originCube d (n : ℤ))) -
        ∫ x, Phi.globalGradientRepresentative x
          ∂normalizedCubeMeasure (originCube d (n : ℤ)))
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    exact
      Phi.tendsto_norm_integral_globalGradient_translate_sub_zero_of_weakRow
        eRow t hs hs2 q0 N hRow
  simpa only [sub_add_cancel, add_zero] using hDifference.add hPhiIntegral

end

end HighContrast
end HCPolySupport
