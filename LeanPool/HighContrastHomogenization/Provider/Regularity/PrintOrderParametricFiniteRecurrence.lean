/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.MixedOrderFiniteRecurrenceCore
public import LeanPool.HighContrastHomogenization.Provider.Regularity.OrderDecouplingBoundary
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationOneStepAffineExcess
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationFiniteCaccioppoli

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderParametricFiniteRecurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite recurrence at a tolerance-selected rounded generation

The stochastic certificate and every finite response row use the printed
order.  The deterministic Dirichlet response retains its independently
selected private order; the two sides meet only through order-independent
coefficient and energy data.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set Book.Ch03
open scoped BigOperators ENNReal

noncomputable section

open FiniteLipschitzCoreInternal

/-- The selected-generation application together with the fixed private
Dirichlet response.  No equality between the two fractional orders occurs. -/
structure PrintOrderParametricRoundedResponseJoin
    (d : ℕ) [NeZero d] (g : ℝ) (a : CoeffSpace d) (abar : Mat d)
    (sourceAmplitude target kappa Cid : ℝ) (X : CoeffSpace d → ℝ) where
  application : PrintOrderParametricRoundedCoefficientApplication
    d g a abar sourceAmplitude target kappa Cid X
  responseSpine : PrivateRoundedPhysicalDirichletSpine d
  responseSpine_eq : responseSpine = privateRoundedPhysicalDirichletSpine d
  privateOrder_lt_printOrder :
    responseSpine.order.1 < printCertificateOrder g

namespace PrintOrderParametricRoundedResponseJoin

variable {d : ℕ} [NeZero d] {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
  {sourceAmplitude target kappa Cid : ℝ} {X : CoeffSpace d → ℝ}

/-- The deterministic geometry selected by the absorption tolerance. -/
@[expose]
def geometry
    (join : PrintOrderParametricRoundedResponseJoin
      d g a abar sourceAmplitude target kappa Cid X) :
    RoundedGenerationAnalyticGeometry d :=
  RoundedGenerationAnalyticGeometry.ofApplication join.application

end PrintOrderParametricRoundedResponseJoin

/-- Complete analytic data for the finite recurrence at the selected rounded
generation and printed response order. -/
structure PrintOrderParametricFiniteRecurrenceInputs
    (d : ℕ) [NeZero d] (g : ℝ) (a : CoeffSpace d) (abar : Mat d)
    (sourceAmplitude target kappa Cid : ℝ) (X : CoeffSpace d → ℝ)
    (join : PrintOrderParametricRoundedResponseJoin
      d g a abar sourceAmplitude target kappa Cid X) where
  step : ℕ
  step_pos : 0 < step
  stepConstant : ℝ
  stepConstant_nonneg : 0 ≤ stepConstant
  oneStep :
    ∀ (m : ℤ) (u : Book.Ch03.CubeSolution
        (originCube d m) join.application.aRounded)
      (k : ℤ) (hkm : k ≤ m),
      finiteCenteredCubeBestFitErrorAt join.application.aRounded m u
          (k - (step : ℤ)) (by omega) ≤
        (1 / 8 : ℝ) * finiteCenteredCubeBestFitErrorAt
            join.application.aRounded m u k hkm +
          stepConstant *
              join.geometry.spatialWeakError a abar join.application.hS
                (printCertificateOrder g) k *
            finiteCenteredCubeSolutionEnergy
              join.application.aRounded m u k
  caccioppoliConstant : ℝ
  caccioppoliConstant_pos : 0 < caccioppoliConstant
  caccioppoli :
    ∀ (k : ℤ) (u : Book.Ch03.CubeSolution
        (originCube d k) join.application.aRounded) (c : ℝ) (e : Vec d),
      join.geometry.spatialWeakError a abar join.application.hS
          (printCertificateOrder g) k ≤ 1 →
        Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2))
            join.application.aRounded
            (finiteCubeSolutionRestriction join.application.aRounded
              (by omega : k - 2 ≤ k) u).toH1 ≤
          caccioppoliConstant *
            (normalizedAffineCandidateError
              (originCube d k) u.toH1.toFun c e + euclideanNorm e)
  terminalConstant : ℝ
  terminalConstant_pos : 0 < terminalConstant
  terminalSlope :
    ∀ (m : ℤ) (u : Book.Ch03.CubeSolution
        (originCube d m) join.application.aRounded),
      join.geometry.spatialWeakError a abar join.application.hS
          (printCertificateOrder g) m ≤ 1 →
        euclideanNorm
            (finiteLipschitzBestSlope join.application.aRounded m u m) ≤
          terminalConstant *
            finiteLipschitzEnergyRow join.application.aRounded m u m
  affineErrorConstant : ℝ
  affineErrorConstant_pos : 0 < affineErrorConstant
  affineErrorEnergy :
    ∀ (m : ℤ) (u : Book.Ch03.CubeSolution
        (originCube d m) join.application.aRounded)
      (k : ℤ) (_hkm : k ≤ m),
      join.geometry.spatialWeakError a abar join.application.hS
          (printCertificateOrder g) k ≤ 1 →
        finiteLipschitzAffineErrorRow
            join.application.aRounded m u k ≤
          affineErrorConstant *
            finiteLipschitzEnergyRow join.application.aRounded m u k

/-- Every selected-generation join supplies all four analytic fields. -/
theorem nonempty_printOrderParametricFiniteRecurrenceInputs
    {d : ℕ} [NeZero d] {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
    {sourceAmplitude target kappa Cid : ℝ} {X : CoeffSpace d → ℝ}
    (hg : g ∈ Ico (0 : ℝ) 1)
    (join : PrintOrderParametricRoundedResponseJoin
      d g a abar sourceAmplitude target kappa Cid X) :
    Nonempty (PrintOrderParametricFiniteRecurrenceInputs
      d g a abar sourceAmplitude target kappa Cid X join) := by
  let geom := join.geometry
  have hs : 0 < printCertificateOrder g := (printOrder_margins hg).1
  have hsHalf : printCertificateOrder g < (1 : ℝ) / 2 :=
    (printOrder_margins hg).2.1
  obtain ⟨step, hstep, Cstep, hCstep, honeStep⟩ :=
    exists_printOrderRoundedGenerationOneStepAffineExcess
      d g geom hg (by
        simpa only [geom, PrintOrderParametricRoundedResponseJoin.geometry,
          RoundedGenerationAnalyticGeometry.ofApplication] using
          join.application.dualRegularity)
  obtain ⟨Cc, hCc, hcaccioppoli⟩ :=
    exists_roundedGenerationFiniteLipschitzCaccioppoliAffineConstant
      d geom (printCertificateOrder g) hs hsHalf
  obtain ⟨Ct, hCt, hterminal⟩ :=
    exists_roundedGenerationFiniteLipschitzTerminalSlopeConstant
      d geom (printCertificateOrder g) hs hsHalf
  obtain ⟨Ca, hCa, haffine⟩ :=
    exists_roundedGenerationFiniteLipschitzAffineErrorEnergyConstant
      d geom (printCertificateOrder g) hs hsHalf
  refine ⟨⟨step, hstep, Cstep, hCstep, ?_,
    Cc, hCc, ?_, Ct, hCt, ?_, Ca, hCa, ?_⟩⟩
  · exact honeStep a abar join.application.hS join.application.aRounded
      join.application.aRounded_eq
  · exact hcaccioppoli a abar join.application.hS
      join.application.aRounded join.application.aRounded_eq
  · exact hterminal a abar join.application.hS
      join.application.aRounded join.application.aRounded_eq
  · exact haffine a abar join.application.hS
      join.application.aRounded join.application.aRounded_eq

end

end HighContrast
end HCPolySupport
