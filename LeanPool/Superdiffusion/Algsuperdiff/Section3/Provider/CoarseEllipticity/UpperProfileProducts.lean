/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperProfileExponents
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower

/-!
# UpperProfileProducts

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

theorem isBigOWith_upperProfileTarget_hsep_mul_one [IsFiniteMeasure mu]
    {sigma AR AZ : ℝ} {R Z : Omega → ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hAR : 0 ≤ AR) (hAZ : 0 ≤ AZ)
    (hR0 : ∀ omega, 0 ≤ R omega) (hZ0 : ∀ omega, 0 ≤ Z omega)
    (hR : IsBigOWith mu (gammaSigma (upperProfileHsepTau sigma)) R AR)
    (hZ : IsBigOWith mu (gammaSigma 1) Z AZ) :
    IsBigOWith mu (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => R omega * Z omega)
      (HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileHsepTau sigma) 1 * AR * AZ) := by
  have hprod :=
    Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_mul_of_nonneg
      (μ := mu) (X := R) (Y := Z)
      (upperProfileHsepTau_pos hsigma0 hsigma) one_pos
      hAR hAZ hR0 hZ0 hR hZ
  have hprod' : IsBigOWith mu
      (gammaSigma (upperProfileHsepTau sigma /
        (upperProfileHsepTau sigma + 1)))
      (fun omega => R omega * Z omega)
      (HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileHsepTau sigma) 1 * AR * AZ) := by
    simpa using hprod
  exact HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
    (upperProfileTargetSigma_le_hsep_mul_one hsigma0 hsigma) hprod'

theorem isBigOWith_upperProfileTarget_hsep_mul_tail [IsFiniteMeasure mu]
    {sigma AR AZ : ℝ} {R Z : Omega → ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hAR : 0 ≤ AR) (hAZ : 0 ≤ AZ)
    (hR0 : ∀ omega, 0 ≤ R omega) (hZ0 : ∀ omega, 0 ≤ Z omega)
    (hR : IsBigOWith mu (gammaSigma (upperProfileHsepTau sigma)) R AR)
    (hZ : IsBigOWith mu
      (gammaSigma (upperProfileTailSigma sigma)) Z AZ) :
    IsBigOWith mu (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => R omega * Z omega)
      (HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileHsepTau sigma)
        (upperProfileTailSigma sigma) * AR * AZ) := by
  have hprod :=
    Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_mul_of_nonneg
      (μ := mu) (X := R) (Y := Z)
      (upperProfileHsepTau_pos hsigma0 hsigma)
      (upperProfileTailSigma_pos hsigma0 hsigma)
      hAR hAZ hR0 hZ0 hR hZ
  rw [upperProfile_hsep_mul_tailSigma_eq hsigma0 hsigma] at hprod
  exact hprod

theorem isBigOWith_upperProfileTarget_collarPower_mul_one [IsFiniteMeasure mu]
    {sigma gamma b AR AZ : ℝ} {R Z : Omega → ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgamma0 : 0 ≤ gamma) (hb : 0 < b) (hgamma : gamma ≤ b * sigma)
    (hAR : 0 ≤ AR) (hAZ : 0 ≤ AZ)
    (hR0 : ∀ omega, 0 ≤ R omega) (hZ0 : ∀ omega, 0 ≤ Z omega)
    (hR : IsBigOWith mu
      (gammaSigma (upperProfileBaseSigma sigma /
        ((2 * gamma + 2 * b) / b))) R AR)
    (hZ : IsBigOWith mu (gammaSigma 1) Z AZ) :
    IsBigOWith mu (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => R omega * Z omega)
      (HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileBaseSigma sigma / ((2 * gamma + 2 * b) / b)) 1 *
          AR * AZ) := by
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * gamma + 2 * b) / b)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    exact div_pos (upperProfileBaseSigma_pos hsigma0 hsigma) (by positivity)
  have htaualpha : upperProfileHsepTau sigma ≤ alpha :=
    upperProfileHsepTau_le_collarPowerSigma hsigma0 hsigma hgamma0 hb hgamma
  have hmono : upperProfileHsepTau sigma /
        (upperProfileHsepTau sigma + 1) ≤ alpha / (alpha + 1) := by
    simpa using productSigma_mono_left
      (upperProfileHsepTau_pos hsigma0 hsigma) htaualpha one_pos
  have htarget : upperProfileTargetSigma sigma ≤ alpha / (alpha + 1) :=
    (upperProfileTargetSigma_le_hsep_mul_one hsigma0 hsigma).trans hmono
  have hprod :=
    Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_mul_of_nonneg
      (μ := mu) (X := R) (Y := Z) halpha one_pos hAR hAZ hR0 hZ0 hR hZ
  have hprod' : IsBigOWith mu (gammaSigma (alpha / (alpha + 1)))
      (fun omega => R omega * Z omega)
      (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AR * AZ) := by
    simpa using hprod
  exact HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
    htarget hprod'

theorem isBigOWith_upperProfileTarget_collarPower_mul_tail [IsFiniteMeasure mu]
    {sigma gamma b AR AZ : ℝ} {R Z : Omega → ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgamma0 : 0 ≤ gamma) (hb : 0 < b) (hgamma : gamma ≤ b * sigma)
    (hAR : 0 ≤ AR) (hAZ : 0 ≤ AZ)
    (hR0 : ∀ omega, 0 ≤ R omega) (hZ0 : ∀ omega, 0 ≤ Z omega)
    (hR : IsBigOWith mu
      (gammaSigma (upperProfileBaseSigma sigma /
        ((2 * gamma + 2 * b) / b))) R AR)
    (hZ : IsBigOWith mu
      (gammaSigma (upperProfileTailSigma sigma)) Z AZ) :
    IsBigOWith mu (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => R omega * Z omega)
      (HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileBaseSigma sigma / ((2 * gamma + 2 * b) / b))
        (upperProfileTailSigma sigma) * AR * AZ) := by
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * gamma + 2 * b) / b)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    exact div_pos (upperProfileBaseSigma_pos hsigma0 hsigma) (by positivity)
  have htarget : upperProfileTargetSigma sigma ≤
      alpha * upperProfileTailSigma sigma /
        (alpha + upperProfileTailSigma sigma) :=
    upperProfileTargetSigma_le_collarPower_mul_tail
      hsigma0 hsigma hgamma0 hb hgamma
  have hprod :=
    Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_mul_of_nonneg
      (μ := mu) (X := R) (Y := Z) halpha
      (upperProfileTailSigma_pos hsigma0 hsigma)
      hAR hAZ hR0 hZ0 hR hZ
  exact HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
    htarget hprod

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
