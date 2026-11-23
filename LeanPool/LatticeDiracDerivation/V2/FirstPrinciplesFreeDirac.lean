/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.FinitePeriodicTangent
public import LeanPool.LatticeDiracDerivation.V2.NativeC19CliffordRoot
public import LeanPool.LatticeDiracDerivation.V2.NativePhaseReadout

/-! # The native action and free Dirac certificate -/

@[expose] public section

namespace LeanDirac.V2

open Complex Filter Topology
noncomputable section

/-- The action variation, vacuum tangent, and four-component equation in one statement. -/
structure FirstPrinciplesFreeDiracCertificate : Prop where
  actionTangentExtracted : ∀ (r eps : ℝ), r ≠ 0 →
    ∀ position velocity momentum site,
      uniformCharacterActionDensity r eps position velocity momentum site =
        eps ^ 2 * uniformVacuumModalLagrangian
          r momentum position velocity -
          eps ^ 4 * uniformCell2Density position ^ 2 / 4
  actionHessianExact : ∀ (r eps : ℝ), r ≠ 0 →
    ∀ position velocity momentum site,
      uniformCharacterTangentQuotient
          r eps position velocity momentum site =
        2 * uniformVacuumModalLagrangian
          r momentum position velocity -
          eps ^ 2 * uniformCell2Density position ^ 2 / 2
  actionHessianLimit : ∀ (r : ℝ), r ≠ 0 →
    ∀ position velocity momentum site,
      Tendsto
        (fun eps : ℝ =>
          uniformCharacterTangentQuotient
            r eps position velocity momentum site)
        (nhds 0)
        (nhds (2 * uniformVacuumModalLagrangian
          r momentum position velocity))
  finitePeriodicActionHessian : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum) (r B : ℝ), r ≠ 0 →
      ∀ (mode : PeriodicC19FourierMode L momentum) position velocity,
      Tendsto
        (fun eps : ℝ =>
          periodicC19LagrangianTangentQuotient
            r B eps mode position velocity)
        (nhds 0)
        (nhds (2 * periodicSiteCount L *
          uniformVacuumModalLagrangian
            r momentum position velocity))
  finitePeriodicForceDiagonalizes : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum) (r : ℝ)
      (mode : PeriodicC19FourierMode L momentum)
      (amplitude : ℂ) (site : PeriodicCubicSite L),
      periodicC19LinearizedAcceleration r
          (periodicModeField mode amplitude) site =
        -((r ^ 2 + c19TransportSymbol momentum : ℝ) : ℂ) *
          periodicModeField mode amplitude site
  finitePeriodicPotentialHessianForce : ∀ (L : ℕ) [NeZero L]
      (r : ℝ), r ≠ 0 →
      ∀ (component : PeriodicTransverseChannel)
        (field : PeriodicCubicSite L → ℂ)
        (site : PeriodicCubicSite L) (amplitude : ℂ),
      AnalyticHasDerivAt
        (fun eps : ℝ =>
          potentialFirstVariation r
            (periodicTransverseComponentState r eps component field)
            (periodicTransverseComponentDirection component
              (periodicSingleSiteScalarDirection site amplitude))
            (c19Bond (periodicC19Geometry L)))
        (-uniformScalarRealPair
          (periodicC19LinearizedAcceleration r field site) amplitude) 0
  finitePeriodicModeHessianForce : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum) (r : ℝ), r ≠ 0 →
      ∀ (mode : PeriodicC19FourierMode L momentum)
        (position : UniformCell2) (component : Fin 2)
        (site : PeriodicCubicSite L) (testAmplitude : ℂ),
      AnalyticHasDerivAt
        (fun eps : ℝ =>
          potentialFirstVariation r
            (periodicTransverseComponentState r eps component
              (periodicModeField mode (position component)))
            (periodicTransverseComponentDirection component
              (periodicSingleSiteScalarDirection site testAmplitude))
            (c19Bond (periodicC19Geometry L)))
        (-uniformScalarRealPair
          (periodicModeField mode
            ((uniformVacuumModalAcceleration r momentum position) component)
            site) testAmplitude) 0
  finitePeriodicLongitudinalCrossBlock : ∀ (L : ℕ) [NeZero L]
      (r eps : ℝ)
      (field first second : PeriodicCubicSite L → ℂ),
      potentialFirstVariation r
          (uniformTransverseState r eps first second)
          (periodicLongitudinalPsiDirection field)
          (c19Bond (periodicC19Geometry L)) = 0
  finitePeriodicChiCrossBlock : ∀ (L : ℕ) [NeZero L]
      (r : ℝ) (first second : PeriodicCubicSite L → ℂ)
      (chiDirection : PeriodicCubicSite L → C3),
      AnalyticHasDerivAt
        (fun eps : ℝ =>
          potentialFirstVariation r
            (uniformTransverseState r eps first second)
            (pureChiDirection chiDirection)
            (c19Bond (periodicC19Geometry L))) 0 0
  orientedC19CliffordRoot : NativeC19CliffordRootCertificate
  lowerCoordinatesForced : ∀ mass px py pz,
    mass ≠ 0 → ∀ phase lower,
      (∀ component,
        mass * lower component =
          I * phase.2 component +
            cubicalSpatialLower px py pz phase.1 component) →
      lower = cubicalPhaseLower mass px py pz phase
  eulerLagrange : ∀ r momentum position direction,
    uniformCell2RealPair
        (uniformVacuumModalAcceleration r momentum position) direction +
      uniformVacuumModalPotentialVariation
        r momentum position direction = 0
  losslessRankFourReadout : ∀ r, r ≠ 0 → ∀ momentum,
    Function.Injective (uniformActionToStandardDirac r momentum)
  oneOperatorIntertwining : ∀ r, r ≠ 0 → ∀ momentum phase,
    uniformActionToStandardDirac r momentum
        (uniformVacuumContinuumGenerator r momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase) component
  positiveRestFrequencyGrading : ∀ r, r ≠ 0 → ∀ position,
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestPositivePhase r position)) =
      uniformActionToStandardDirac r (fun _ => 0)
        (uniformRestPositivePhase r position)
  negativeRestFrequencyGrading : ∀ r, r ≠ 0 → ∀ position,
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position)) =
      fun component =>
        -uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position) component
  pureCubeCopies : ∀ (r : ℝ) momentum phase,
    (cubicalNativeHamiltonian (r : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum)
        (cubicalDiracEmbedMinus
          (uniformActionToStandardDirac r momentum phase)) =
      cubicalDiracEmbedMinus
        (cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase))) ∧
    (cubicalNativeHamiltonian (r : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum)
        (cubicalDiracEmbedPlus
          (uniformActionToStandardDirac r momentum phase)) =
      cubicalDiracEmbedPlus
        (cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase)))
  exactC19Defect : ∀ r momentum phase,
    uniformVacuumNativeGenerator r momentum phase =
      (fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).1 component +
          (uniformNativeSpatialDefectPhase momentum phase).1 component,
       fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).2 component +
          (uniformNativeSpatialDefectPhase momentum phase).2 component)

theorem first_principles_free_dirac :
    FirstPrinciplesFreeDiracCertificate where
  actionTangentExtracted := uniform_character_action_density_expansion
  actionHessianExact := uniform_character_tangent_quotient_exact
  actionHessianLimit := uniform_character_tangent_quotient_tends_to_hessian
  finitePeriodicActionHessian :=
    fun _ _ _ r B hr mode position velocity =>
      periodic_c19_lagrangian_tangent_tends_to_modal
        r B hr mode position velocity
  finitePeriodicForceDiagonalizes :=
    fun _ _ _ r mode amplitude site =>
      periodic_c19_linearized_force_diagonalizes
        r mode amplitude site
  finitePeriodicPotentialHessianForce :=
    fun _ _ r hr component field site amplitude =>
      periodic_c19_transverse_component_hessian_localized
        r hr component field site amplitude
  finitePeriodicModeHessianForce :=
    fun _ _ _ r hr mode position component site testAmplitude =>
      periodic_c19_action_hessian_mode_force
        r hr mode position component site testAmplitude
  finitePeriodicLongitudinalCrossBlock :=
    fun _ _ r eps field first second =>
      periodic_c19_transverse_longitudinal_cross_variation_zero
        r eps field first second
  finitePeriodicChiCrossBlock :=
    fun _ _ r first second chiDirection =>
      periodic_c19_transverse_chi_cross_hessian_zero
        r first second chiDirection
  orientedC19CliffordRoot := native_c19_clifford_root
  lowerCoordinatesForced := cubical_phase_lower_unique
  eulerLagrange := uniform_modal_euler_lagrange
  losslessRankFourReadout := uniform_action_to_standard_injective
  oneOperatorIntertwining :=
    uniform_action_tangent_intertwines_cubical_dirac
  positiveRestFrequencyGrading :=
    uniform_rest_positive_readout_has_positive_beta
  negativeRestFrequencyGrading :=
    uniform_rest_negative_readout_has_negative_beta
  pureCubeCopies := uniform_action_dirac_has_both_cubical_copies
  exactC19Defect := uniform_native_generator_exact_defect

end
end LeanDirac.V2
