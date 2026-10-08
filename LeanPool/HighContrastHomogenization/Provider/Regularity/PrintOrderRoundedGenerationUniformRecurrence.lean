/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderToleranceSelectedRoundedSpine

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationUniformRecurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Uniform finite recurrence for one selected rounded geometry

The rounded generation and all analytic constants are selected before the
coefficient sample.  The stochastic certificate enters only through the
printed-order weak-error row.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set Book.Ch03
open scoped BigOperators ENNReal

noncomputable section

open FiniteLipschitzCoreInternal

/-- At a fixed selected geometry, one constant controls the finite recurrence
for every centered coefficient realization. -/
theorem exists_printOrderRoundedGenerationUniformFiniteRecurrenceConstant
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aRounded.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d)) →
        ∀ (n m : ℤ)
          (u : Book.Ch03.CubeSolution (originCube d m) aRounded), n ≤ m →
          RoundedGenerationSpatialGoodMaxOnInterval
              geom.generation a abar hS (printCertificateOrder g) 1 n m →
          ∀ h ∈ Finset.Icc n m,
            finiteCenteredCubeSolutionEnergy aRounded m u h ≤
              C * finiteCenteredCubeSolutionEnergy aRounded m u m +
                C * ∑ j ∈ Finset.Ioc h m,
                  roundedGenerationSpatialWeakError
                      geom.generation a abar hS
                      (printCertificateOrder g) j *
                    finiteCenteredCubeSolutionEnergy aRounded m u j := by
  have hs : 0 < printCertificateOrder g := (printOrder_margins hg).1
  have hsHalf : printCertificateOrder g < (1 : ℝ) / 2 :=
    (printOrder_margins hg).2.1
  obtain ⟨step, hstep, Cstep, hCstep, honeStep⟩ :=
    exists_printOrderRoundedGenerationOneStepAffineExcess
      d g geom hg hdual
  obtain ⟨Cc, hCc, hcaccioppoli⟩ :=
    exists_roundedGenerationFiniteLipschitzCaccioppoliAffineConstant
      d geom (printCertificateOrder g) hs hsHalf
  obtain ⟨Ct, hCt, hterminal⟩ :=
    exists_roundedGenerationFiniteLipschitzTerminalSlopeConstant
      d geom (printCertificateOrder g) hs hsHalf
  obtain ⟨Ce, hCe, herrorEnergy⟩ :=
    exists_roundedGenerationFiniteLipschitzAffineErrorEnergyConstant
      d geom (printCertificateOrder g) hs hsHalf
  obtain ⟨C, hC, hrecurrence⟩ :=
    exists_mixedResponseFiniteLipschitzEnergyRecurrenceConstant
      d step hstep Cstep hCstep Cc hCc Ct hCt Ce hCe
  refine ⟨C, hC, ?_⟩
  intro a abar hS aRounded hRounded n m u hnm hgood h hh
  let R : ℤ → ℝ := fun j ↦
    geom.spatialWeakError a abar hS (printCertificateOrder g) j
  have hR : ∀ j : ℤ, 0 ≤ R j := by
    intro j
    exact geom.spatialWeakError_nonneg
      a abar hS (printCertificateOrder g) j
  have hgood' : ∀ k ∈ Finset.Icc n m, R k ≤ 1 := by
    intro k hk
    simpa only [R, RoundedGenerationAnalyticGeometry.spatialWeakError] using
      hgood k hk
  have hraw := hrecurrence aRounded R hR
    (honeStep a abar hS aRounded hRounded)
    (hcaccioppoli a abar hS aRounded hRounded)
    (hterminal a abar hS aRounded hRounded)
    (herrorEnergy a abar hS aRounded hRounded)
    n m u hnm hgood' h hh
  simpa only [finiteCenteredCubeSolutionEnergy,
    finiteLipschitzEnergyRow, R,
    RoundedGenerationAnalyticGeometry.spatialWeakError] using! hraw

/-- A finite recurrence driven by a selected-generation row closes under the
summable good-tail bound at that same generation and order. -/
theorem finiteCenteredEnergy_le_of_roundedGenerationGoodTail
    {d : ℕ} {generation : ℤ}
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s : ℝ}
    {aRounded : Book.Ch03.CoeffFamily d}
    {C : ℝ} (hC : 1 ≤ C) {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) aRounded)
    (hrecurrence : ∀ q ∈ Finset.Icc n m,
      finiteCenteredCubeSolutionEnergy aRounded m u q ≤
        C * finiteCenteredCubeSolutionEnergy aRounded m u m +
          C * ∑ j ∈ Finset.Ioc q m,
            roundedGenerationSpatialWeakError
                generation a abar hS s j *
              finiteCenteredCubeSolutionEnergy aRounded m u j)
    (hTail : RoundedGenerationSpatialGoodTailOnInterval
      generation a abar hS s (2 * C)⁻¹ n m) :
    ∀ h ∈ Finset.Icc n m,
      finiteCenteredCubeSolutionEnergy aRounded m u h ≤
        2 * C * finiteCenteredCubeSolutionEnergy aRounded m u m := by
  let D : ℤ → ℝ := finiteCenteredCubeSolutionEnergy aRounded m u
  let E : ℤ → ℝ :=
    roundedGenerationSpatialWeakError generation a abar hS s
  have hD : ∀ j ∈ Finset.Icc n m, 0 ≤ D j := by
    intro j _hj
    dsimp only [D, finiteCenteredCubeSolutionEnergy]
    exact finiteLipschitzEnergyRow_nonneg aRounded m u j
  have hE : ∀ j ∈ Finset.Icc n m, 0 ≤ E j := by
    intro j _hj
    exact roundedGenerationSpatialWeakError_nonneg
      generation a abar hS s j
  have hrec : ∀ q ∈ Finset.Icc n m,
      D q ≤ C * D m + C * ∑ j ∈ Finset.Ioc q m, E j * D j := by
    intro q hq
    simpa only [D, E] using hrecurrence q hq
  have hsmall : ∑ j ∈ Finset.Icc n m, E j ≤ (2 * C)⁻¹ := by
    simpa only [RoundedGenerationSpatialGoodTailOnInterval, E] using hTail
  intro h hh
  have hbound :=
    smallTail_interval_bound C D E hnm hC hD hE hrec hsmall h hh
  simpa only [D] using hbound

end

end HighContrast
end HCPolySupport
