/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationUniformRecurrence

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Root surface of the order-decoupled rounded spine

The printed stochastic order controls the weak-error row.  The private
Dirichlet response keeps its independently selected deterministic order, and
the two constructions meet only through the selected coefficient family and
the finite energy recurrence.
-/

namespace HCPolySupport
namespace HighContrast
namespace Certificate

open MeasureTheory Set Book.Ch03
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

/-- Complete pointwise output of the decoupled spine.  It retains the source
certificate, the selected rounded generation, all recurrence inputs, and the
closed finite terminal induction. -/
structure PrintOrderDecoupledFiniteTerminalSurface
    (d : ℕ) [NeZero d] (g c kappa Cid : ℝ)
    (abar : Mat d) (a : CoeffSpace d) (x : ℝ) where
  /-- Source amplitude in the initial quantitative normalized reference certificate. -/
  sourceAmplitude : ℝ
  /-- Coefficient-dependent scale function used by the initial and final reference certificates. -/
  X : CoeffSpace d → ℝ
  sourceCertificate :
    PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g sourceAmplitude kappa (X a) a
  rootScale_eq :
    x = commonQuantitativeAffineScale sourceAmplitude
      (correctorTargetAmplitude c kappa) kappa
      (Transport.roundedOuterResponseAffineConstant d)
      (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
      kappa X a
  /-- Rounded spine selected at the tolerance determined by `Cid`. -/
  spine : PrintOrderToleranceSelectedRoundedSpine d Cid
  /-- Rounded response application joining the source amplitude to the target amplitude. -/
  join : PrintOrderParametricRoundedResponseJoin
    d g a abar sourceAmplitude (correctorTargetAmplitude c kappa)
      kappa Cid X
  generation_eq : join.application.generation = spine.generation
  finalCertificate :
    PrintOrderQuantitativeNormalizedReferenceCertificate abar g
      (correctorTargetAmplitude c kappa) kappa
      (printOrderCommonQuantitativeAffineScale d g sourceAmplitude
        (correctorTargetAmplitude c kappa) kappa abar X a) a
  /-- Finite recurrence estimates for the selected rounded response join. -/
  recurrenceInputs : PrintOrderParametricFiniteRecurrenceInputs
    d g a abar sourceAmplitude (correctorTargetAmplitude c kappa)
      kappa Cid X join
  /-- Constant in the terminal finite induction and the inverse target relation. -/
  recurrenceConstant : ℝ
  recurrenceConstant_ge : 1 ≤ recurrenceConstant
  target_eq_inverse : c = (2 * recurrenceConstant)⁻¹
  recurrence :
    ∀ (n m : ℤ)
      (u : Book.Ch03.CubeSolution
        (originCube d m) join.application.aRounded), n ≤ m →
      RoundedGenerationSpatialGoodMaxOnInterval
          join.application.generation a abar join.application.hS
          (printCertificateOrder g) 1 n m →
      ∀ h ∈ Finset.Icc n m,
        finiteCenteredCubeSolutionEnergy
            join.application.aRounded m u h ≤
          recurrenceConstant * finiteCenteredCubeSolutionEnergy
              join.application.aRounded m u m +
            recurrenceConstant * ∑ j ∈ Finset.Ioc h m,
              roundedGenerationSpatialWeakError
                  join.application.generation a abar join.application.hS
                  (printCertificateOrder g) j *
                finiteCenteredCubeSolutionEnergy
                  join.application.aRounded m u j
  terminal :
    let n := (Quenched.triadicCeilingIndex
      (printOrderCommonQuantitativeAffineScale d g sourceAmplitude
        (correctorTargetAmplitude c kappa) kappa abar X a) : ℤ)
    ∀ (m : ℤ) (_hm : n ≤ m)
      (u : Book.Ch03.CubeSolution
        (originCube d m) join.application.aRounded)
      (h : ℤ), h ∈ Finset.Icc n m →
        finiteCenteredCubeSolutionEnergy
            join.application.aRounded m u h ≤
          2 * recurrenceConstant *
            finiteCenteredCubeSolutionEnergy
              join.application.aRounded m u m

/-- The constructor selected from the identity estimate gives a pointwise
terminal surface for every rate-bearing certificate.  The contraction
amplitude is selected after `g`, because the printed-order analytic constant
depends on that order, but before the coefficient sample and certificate. -/
theorem exists_printOrderDecoupledFiniteTerminalSurface
    (d : ℕ) [NeZero d] (g Cid : ℝ)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hidentity : PrintOrderIdentityCubeDualRegularityWithConstant d g Cid) :
    ∃ C c : ℝ, 1 ≤ C ∧ c = (2 * C)⁻¹ ∧ c ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (kappa : ℝ) (abar : Mat d) (a : CoeffSpace d) (x : ℝ),
        PrintOrderRateBearingCommonAffineGoodScale
            d g c kappa abar a x →
          Nonempty (PrintOrderDecoupledFiniteTerminalSurface
            d g c kappa Cid abar a x) := by
  obtain ⟨spine⟩ := nonempty_printOrderToleranceSelectedRoundedSpine d Cid
  let geom : RoundedGenerationAnalyticGeometry d := spine.geometry
  have hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation := by
    simpa only [geom, PrintOrderToleranceSelectedRoundedSpine.geometry] using
      printOrderRoundedReferenceDualRegularityAtGeneration_of_absorption
        d g Cid hg hidentity spine.absorptionProperties
  obtain ⟨C, hC, hrecurrence⟩ :=
    exists_printOrderRoundedGenerationUniformFiniteRecurrenceConstant
      d g geom hg hdual
  let c : ℝ := (2 * C)⁻¹
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have htwoCpos : 0 < 2 * C := mul_pos (by norm_num) hCpos
  have hcpos : 0 < c := by
    dsimp only [c]
    exact inv_pos.mpr htwoCpos
  have htwoC : 1 < 2 * C := by
    calc
      1 < 2 := by norm_num
      _ ≤ 2 * C := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)
  have hclt : c < 1 := by
    dsimp only [c]
    exact (inv_lt_one₀ htwoCpos).2 htwoC
  refine ⟨C, c, hC, rfl, ⟨hcpos, hclt⟩, ?_⟩
  intro kappa abar a x hGood
  obtain ⟨sourceAmplitude, X, hCertificate, hx⟩ := hGood
  have hCertificateData := hCertificate
  obtain ⟨_hS, _aRef, _hs, _hsHalf, _hAmplitude,
    hKappa, _hX, _haRef, _hTail⟩ := hCertificateData
  have hTarget : 0 < correctorTargetAmplitude c kappa :=
    correctorTargetAmplitude_pos hcpos hKappa
  obtain ⟨join, hgeneration⟩ :=
    hCertificate.exists_joinAtSelectedSpine
      spine hg hTarget hidentity
  obtain ⟨inputs⟩ :=
    nonempty_printOrderParametricFiniteRecurrenceInputs hg join
  have hRounded : ∀ Q : TriadicCube d,
      (join.application.aRounded.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace abar join.application.hS a).1 :
          CoeffField d) := by
    intro Q
    simpa only [geom, PrintOrderToleranceSelectedRoundedSpine.geometry,
      RoundedGenerationAnalyticGeometry.centeredCoeffSpace, hgeneration] using
      join.application.aRounded_eq Q
  have hrecurrence' :
      ∀ (n m : ℤ)
        (u : Book.Ch03.CubeSolution
          (originCube d m) join.application.aRounded), n ≤ m →
        RoundedGenerationSpatialGoodMaxOnInterval
            join.application.generation a abar join.application.hS
            (printCertificateOrder g) 1 n m →
        ∀ h ∈ Finset.Icc n m,
          finiteCenteredCubeSolutionEnergy
              join.application.aRounded m u h ≤
            C * finiteCenteredCubeSolutionEnergy
                join.application.aRounded m u m +
              C * ∑ j ∈ Finset.Ioc h m,
                roundedGenerationSpatialWeakError
                    join.application.generation a abar join.application.hS
                    (printCertificateOrder g) j *
                  finiteCenteredCubeSolutionEnergy
                    join.application.aRounded m u j := by
    intro n m u hnm hgood h hh
    have hgood' : RoundedGenerationSpatialGoodMaxOnInterval
        geom.generation a abar join.application.hS
        (printCertificateOrder g) 1 n m := by
      simpa only [geom, PrintOrderToleranceSelectedRoundedSpine.geometry,
        hgeneration] using hgood
    have hraw := hrecurrence a abar join.application.hS
      join.application.aRounded hRounded n m u hnm hgood' h hh
    simpa only [geom, PrintOrderToleranceSelectedRoundedSpine.geometry,
      hgeneration] using hraw
  have htargetHalf : correctorTargetAmplitude c kappa /
      (1 - (3 : ℝ) ^ (-kappa)) = c / 2 :=
    correctorTargetAmplitude_div hKappa
  have hhalf_le_c : c / 2 ≤ c := by
    linarith only [hcpos]
  have hhalf_le_one : c / 2 ≤ 1 := by
    linarith only [hclt]
  have hterminal :
      let n := (Quenched.triadicCeilingIndex
        (printOrderCommonQuantitativeAffineScale d g sourceAmplitude
          (correctorTargetAmplitude c kappa) kappa abar X a) : ℤ)
      ∀ (m : ℤ) (hm : n ≤ m)
        (u : Book.Ch03.CubeSolution
          (originCube d m) join.application.aRounded)
        (h : ℤ), h ∈ Finset.Icc n m →
          finiteCenteredCubeSolutionEnergy
              join.application.aRounded m u h ≤
            2 * C * finiteCenteredCubeSolutionEnergy
              join.application.aRounded m u m := by
    dsimp only
    intro m hm u h hh
    let n : ℤ := (Quenched.triadicCeilingIndex
      (printOrderCommonQuantitativeAffineScale d g sourceAmplitude
        (correctorTargetAmplitude c kappa) kappa abar X a) : ℤ)
    have hgood : RoundedGenerationSpatialGoodMaxOnInterval
        join.application.generation a abar join.application.hS
        (printCertificateOrder g) 1 n m := by
      intro j hj
      have hjraw := join.application.goodMax m hm j hj
      exact hjraw.trans (by
        rw [htargetHalf]
        exact hhalf_le_one)
    have hrec := hrecurrence' n m u hm hgood
    have htail : RoundedGenerationSpatialGoodTailOnInterval
        join.application.generation a abar join.application.hS
        (printCertificateOrder g) (2 * C)⁻¹ n m := by
      have hraw := join.application.goodTail m hm
      unfold RoundedGenerationSpatialGoodTailOnInterval at hraw ⊢
      calc
        ∑ j ∈ Finset.Icc n m,
            roundedGenerationSpatialWeakError
              join.application.generation a abar join.application.hS
                (printCertificateOrder g) j ≤
            correctorTargetAmplitude c kappa /
              (1 - (3 : ℝ) ^ (-kappa)) := hraw
        _ = c / 2 := htargetHalf
        _ ≤ c := hhalf_le_c
        _ = (2 * C)⁻¹ := rfl
    exact finiteCenteredEnergy_le_of_roundedGenerationGoodTail
      hC hm u hrec htail h hh
  exact ⟨⟨sourceAmplitude, X, hCertificate, hx, spine, join,
    hgeneration, join.application.commonCertificate, inputs, C, hC, rfl,
    hrecurrence', hterminal⟩⟩

end

end Certificate
end HighContrast
end HCPolySupport
