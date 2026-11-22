/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativeC19CliffordRoot

/-!
# One connected native-action to free-Dirac diagram

The source operator in this file is the quadratic Euler--Lagrange generator
extracted in `UniformVacuumEulerLagrange`.  The target Clifford algebra is
constructed independently from abstract cube incidence in
`CubicalClifford`.  The exact C19-to-continuum mismatch remains visible.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex Filter Topology
noncomputable section

/-- The first-order phase-space form of the two action-derived transverse
Klein--Gordon channels.  This definition contains no Clifford data. -/
def uniformTwoChannelKleinGordonVector
    (mass px py pz : ℂ)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (phase.2, fun component =>
    -(mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) * phase.1 component)

/-- The first physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPx (momentum : LatticeMomentum) : ℂ :=
  (c19ContinuumSpeed * momentum 0 : ℝ)

/-- The second physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPy (momentum : LatticeMomentum) : ℂ :=
  (c19ContinuumSpeed * momentum 1 : ℝ)

/-- The third physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPz (momentum : LatticeMomentum) : ℂ :=
  (c19ContinuumSpeed * momentum 2 : ℝ)

theorem uniform_continuum_generator_is_kg
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVacuumContinuumGenerator r momentum phase =
      uniformTwoChannelKleinGordonVector (r : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum) phase := by
  have hc : ((c19ContinuumSpeed : ℂ) ^ 2) = 12 := by
    exact_mod_cast c19_continuum_speed_square
  have hcoefficient :
      (((r ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ)) =
        (r : ℂ) ^ 2 + (uniformContinuumPx momentum) ^ 2 +
          (uniformContinuumPy momentum) ^ 2 +
          (uniformContinuumPz momentum) ^ 2 := by
    simp only [uniformContinuumPx, uniformContinuumPy, uniformContinuumPz, c19QuadraticSymbol,
      ofReal_add, ofReal_pow, ofReal_mul, ofReal_ofNat, mul_pow]
    rw [hc]
    ring
  apply Prod.ext
  · rfl
  · funext component
    simp only [uniformVacuumContinuumGenerator,
      uniformVacuumContinuumAcceleration,
      uniformTwoChannelKleinGordonVector]
    rw [hcoefficient]

/-- Embed the two native transverse positions into the positive beta half of
the four-coordinate cubical representation. -/
def cubicalUpperEmbedding (position : UniformCell2) : CubicalCell4
  | 0 => position 0
  | 1 => position 1
  | _ => 0

/-- Off-diagonal spatial response derived from the pure cubical incidence
Hamiltonian, restricted from the positive beta half to the negative half. -/
def cubicalSpatialLower
    (px py pz : ℂ) (position : UniformCell2) : UniformCell2
  | 0 => orientedCubicalSpatialCoordinates px py pz
      (cubicalUpperEmbedding position) 2
  | _ => orientedCubicalSpatialCoordinates px py pz
      (cubicalUpperEmbedding position) 3

/-- The velocity-dependent two-component coordinate in the native-to-spinor map. -/
def cubicalPhaseLower
    (mass px py pz : ℂ) (phase : UniformTwoChannelPhase) : UniformCell2 :=
  fun component =>
    (I * phase.2 component +
      cubicalSpatialLower px py pz phase.1 component) / mass

/-- For nonzero mass, the lower two coordinates are uniquely forced by the
incidence balance.  They are solved from the native phase variables rather
than fitted as an independent spinor rule. -/
theorem cubical_phase_lower_unique
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (phase : UniformTwoChannelPhase) (lower : UniformCell2)
    (hbalance : ∀ component,
      mass * lower component =
        I * phase.2 component +
          cubicalSpatialLower px py pz phase.1 component) :
    lower = cubicalPhaseLower mass px py pz phase := by
  funext component
  unfold cubicalPhaseLower
  field_simp [hmass]
  simpa [mul_comm] using hbalance component

/-- Four-component readout written only with the action-derived phase space
and the pure cubical incidence response.  No Pauli operator occurs in this
definition. -/
def cubicalPhaseReadout
    (mass px py pz : ℂ) (phase : UniformTwoChannelPhase) : CubicalCell4
  | 0 => phase.1 0 + cubicalPhaseLower mass px py pz phase 0
  | 1 => phase.1 1 + cubicalPhaseLower mass px py pz phase 1
  | 2 => -phase.1 0 + cubicalPhaseLower mass px py pz phase 0
  | _ => -phase.1 1 + cubicalPhaseLower mass px py pz phase 1

/-- The four-component readout with the continuum momentum determined by the action. -/
def uniformActionToStandardDirac
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  cubicalPhaseReadout (r : ℂ)
    (uniformContinuumPx momentum)
    (uniformContinuumPy momentum)
    (uniformContinuumPz momentum) phase

/-- Native positive-rest-frequency data.  The sign convention is
`q(t) = exp (-i r t) q(0)`. -/
def uniformRestPositivePhase
    (r : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  (position, fun component => -I * (r : ℂ) * position component)

/-- Native negative-rest-frequency data. -/
def uniformRestNegativePhase
    (r : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  (position, fun component => I * (r : ℂ) * position component)

/-- The cube-parity beta grading is forced by the native positive rest
frequency after the lossless phase-space reconstruction. -/
theorem uniform_rest_positive_readout_has_positive_beta
    (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestPositivePhase r position)) =
      uniformActionToStandardDirac r (fun _ => 0)
        (uniformRestPositivePhase r position) := by
  funext component
  fin_cases component <;>
    simp [uniformActionToStandardDirac, uniformRestPositivePhase,
      uniformContinuumPx, uniformContinuumPy, uniformContinuumPz,
      cubicalPhaseReadout, cubicalPhaseLower, cubicalSpatialLower,
      cubicalUpperEmbedding, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hr] <;> ring_nf <;> rw [Complex.I_sq] <;> ring

/-- The opposite native rest frequency lands in the negative beta sector. -/
theorem uniform_rest_negative_readout_has_negative_beta
    (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position)) =
      fun component =>
        -uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position) component := by
  funext component
  fin_cases component <;>
    simp [uniformActionToStandardDirac, uniformRestNegativePhase,
      uniformContinuumPx, uniformContinuumPy, uniformContinuumPz,
      cubicalPhaseReadout, cubicalPhaseLower, cubicalSpatialLower,
      cubicalUpperEmbedding, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hr] <;> ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_phase_readout_intertwines
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadout mass px py pz
        (uniformTwoChannelKleinGordonVector mass px py pz phase) =
      fun component =>
        -I * cubicalStandardHamiltonian mass px py pz
          (cubicalPhaseReadout mass px py pz phase) component := by
  have hI3 : I ^ 3 = -I := by
    rw [pow_succ, Complex.I_sq]
    ring
  funext component
  fin_cases component <;>
    simp [cubicalPhaseReadout, cubicalPhaseLower, cubicalSpatialLower,
      cubicalUpperEmbedding, uniformTwoChannelKleinGordonVector,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hmass] <;>
    ring_nf <;> simp only [Complex.I_sq, hI3] <;> ring

/-- Recover the two position coordinates by combining upper and lower spinor components. -/
def cubicalStandardPosition (z : CubicalCell4) : UniformCell2
  | 0 => (z 0 - z 2) / 2
  | _ => (z 1 - z 3) / 2

/-- Recover the two auxiliary coordinates from differences of spinor components. -/
def cubicalStandardLower (z : CubicalCell4) : UniformCell2
  | 0 => (z 0 + z 2) / 2
  | _ => (z 1 + z 3) / 2

/-- Recover native position and velocity from the four-component readout. -/
def cubicalPhaseReadoutInverse
    (mass px py pz : ℂ) (z : CubicalCell4) : UniformTwoChannelPhase :=
  let position := cubicalStandardPosition z
  (position, fun component =>
    -I * (mass * cubicalStandardLower z component -
      cubicalSpatialLower px py pz position component))

theorem cubical_phase_readout_left_inverse
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadoutInverse mass px py pz
        (cubicalPhaseReadout mass px py pz phase) = phase := by
  have hposition :
      cubicalStandardPosition (cubicalPhaseReadout mass px py pz phase) =
        phase.1 := by
    funext component
    fin_cases component <;>
      simp [cubicalStandardPosition, cubicalPhaseReadout]
  apply Prod.ext
  · exact hposition
  · funext component
    rw [show (cubicalPhaseReadoutInverse mass px py pz
        (cubicalPhaseReadout mass px py pz phase)).2 component =
      -I * (mass * cubicalStandardLower
          (cubicalPhaseReadout mass px py pz phase) component -
        cubicalSpatialLower px py pz
          (cubicalStandardPosition
            (cubicalPhaseReadout mass px py pz phase)) component) by rfl,
      hposition]
    fin_cases component <;>
      simp [cubicalStandardLower, cubicalPhaseReadout,
        cubicalPhaseLower] <;>
      field_simp [hmass] <;>
      ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_phase_readout_injective
    (mass px py pz : ℂ) (hmass : mass ≠ 0) :
    Function.Injective (cubicalPhaseReadout mass px py pz) := by
  have leftInverse : Function.LeftInverse (cubicalPhaseReadoutInverse mass px py pz)
      (cubicalPhaseReadout mass px py pz) := cubical_phase_readout_left_inverse mass px py pz hmass
  exact leftInverse.injective

theorem cubical_phase_readout_add
    (mass px py pz : ℂ) (first second : UniformTwoChannelPhase) :
    cubicalPhaseReadout mass px py pz
        (fun component => first.1 component + second.1 component,
         fun component => first.2 component + second.2 component) =
      fun component =>
        cubicalPhaseReadout mass px py pz first component +
          cubicalPhaseReadout mass px py pz second component := by
  funext component
  fin_cases component <;>
    simp [cubicalPhaseReadout, cubicalPhaseLower, cubicalSpatialLower,
      cubicalUpperEmbedding, cubicalStandardSpatial,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;> ring

theorem cubical_phase_readout_right_inverse
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (z : CubicalCell4) :
    cubicalPhaseReadout mass px py pz
        (cubicalPhaseReadoutInverse mass px py pz z) = z := by
  funext component
  fin_cases component <;>
    simp [cubicalPhaseReadoutInverse, cubicalStandardPosition,
      cubicalStandardLower, cubicalPhaseReadout, cubicalPhaseLower] <;>
    field_simp [hmass] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_phase_readout_bijective
    (mass px py pz : ℂ) (hmass : mass ≠ 0) :
    Function.Bijective (cubicalPhaseReadout mass px py pz) := by
  constructor
  · exact cubical_phase_readout_injective mass px py pz hmass
  · intro z
    exact ⟨cubicalPhaseReadoutInverse mass px py pz z,
      cubical_phase_readout_right_inverse mass px py pz hmass z⟩

theorem uniform_action_to_standard_injective
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum) :
    Function.Injective (uniformActionToStandardDirac r momentum) := by
  exact cubical_phase_readout_injective (r : ℂ)
    (uniformContinuumPx momentum)
    (uniformContinuumPy momentum)
    (uniformContinuumPz momentum) (by exact_mod_cast hr)

theorem uniform_action_to_standard_bijective
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum) :
    Function.Bijective (uniformActionToStandardDirac r momentum) := by
  exact cubical_phase_readout_bijective (r : ℂ)
    (uniformContinuumPx momentum)
    (uniformContinuumPy momentum)
    (uniformContinuumPz momentum) (by exact_mod_cast hr)

/-- The same action-derived flow in conventional four-component coordinates,
where alpha and beta are downstream coordinates on pure cube incidence. -/
theorem uniform_action_tangent_intertwines_cubical_dirac
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (uniformVacuumContinuumGenerator r momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase) component := by
  unfold uniformActionToStandardDirac
  rw [uniform_continuum_generator_is_kg]
  exact cubical_phase_readout_intertwines
    (r : ℂ) (uniformContinuumPx momentum)
    (uniformContinuumPy momentum) (uniformContinuumPz momentum)
    (by exact_mod_cast hr) phase

/-- Both native cubical flavor copies carry that same derived four-component
operator.  Nothing selects or discards either copy. -/
theorem uniform_action_dirac_has_both_cubical_copies
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
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
          (uniformActionToStandardDirac r momentum phase))) := by
  exact ⟨cubical_hamiltonian_intertwines_minus _ _ _ _ _,
    cubical_hamiltonian_intertwines_plus _ _ _ _ _⟩

/-- The phase correction whose acceleration component is the C19 spatial remainder. -/
def uniformNativeSpatialDefectPhase
    (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (fun _ => 0,
    fun component =>
      -(c19SpatialRemainder momentum : ℂ) * phase.1 component)

/-- Exact finite-spacing statement: the native C19 generator equals the
continuum generator plus one explicit action-derived spatial defect. -/
theorem uniform_native_generator_exact_defect
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVacuumNativeGenerator r momentum phase =
      (fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).1 component +
          (uniformNativeSpatialDefectPhase momentum phase).1 component,
       fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).2 component +
          (uniformNativeSpatialDefectPhase momentum phase).2 component) := by
  rw [uniform_native_generator_splits]
  apply Prod.ext
  · funext component
    simp [uniformNativeSpatialDefectPhase]
  · funext component
    simp [uniformNativeSpatialDefectPhase]
    ring

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
