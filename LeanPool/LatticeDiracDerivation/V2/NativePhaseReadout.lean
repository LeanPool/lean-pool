/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.ContinuumDiracOperators
public import LeanPool.LatticeDiracDerivation.V2.CubicalPhaseAlgebra
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumEulerLagrange

/-!
# Native phase readout and the free Dirac generator

The source operator in this file is the quadratic Euler--Lagrange generator
extracted in `UniformVacuumEulerLagrange`.  The target Clifford algebra is
constructed independently from abstract cube incidence in
`CubicalClifford`.  The exact C19-to-continuum mismatch remains visible.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex Filter Topology
noncomputable section

/-- The first physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPx (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 0 : ℝ)

/-- The second physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPy (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 1 : ℝ)

/-- The third physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPz (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 2 : ℝ)

theorem uniform_continuum_generator_is_kg
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVacuumContinuumGenerator r momentum phase =
      uniformTwoChannelKleinGordonVector (r : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum) phase := by
  have hcoefficient :
      (((r ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ)) =
        (r : ℂ) ^ 2 + (uniformContinuumPx momentum) ^ 2 +
          (uniformContinuumPy momentum) ^ 2 +
          (uniformContinuumPz momentum) ^ 2 := by
    simp only [uniformContinuumPx, uniformContinuumPy, uniformContinuumPz,
      c19_quadratic_symbol_eq_scaled_momentum, ofReal_add, ofReal_pow, add_assoc]
  apply Prod.ext
  · rfl
  · funext component
    simp only [uniformVacuumContinuumGenerator,
      uniformVacuumContinuumAcceleration,
      uniformTwoChannelKleinGordonVector]
    rw [hcoefficient]

/-- The four-component readout with the continuum momentum determined by the action. -/
def uniformActionToStandardDirac
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  cubicalPhaseReadout (r : ℂ)
    (uniformContinuumPx momentum)
    (uniformContinuumPy momentum)
    (uniformContinuumPz momentum) phase

private theorem uniform_action_readout_at_rest (r : ℝ) (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r (fun _ => 0) phase =
      cubicalPhaseReadout (r : ℂ) 0 0 0 phase := by
  have hcoordinate (axis : Fin 3) : (c19ScaledMomentum (fun _ => 0) axis : ℂ) = 0 := by
    simp [c19ScaledMomentum]
  simp only [uniformActionToStandardDirac, uniformContinuumPx, uniformContinuumPy,
    uniformContinuumPz, hcoordinate]

/-- Native positive-rest-frequency data.  The sign convention is
`q(t) = exp (-i r t) q(0)`. -/
def uniformRestPositivePhase
    (r : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  uniformPositiveFrequencyPhase r position

/-- Native negative-rest-frequency data. -/
def uniformRestNegativePhase
    (r : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  (position, fun component => I * (r : ℂ) * position component)

private theorem cubical_spatial_lower_zero (position : UniformCell2) :
    cubicalSpatialLower 0 0 0 position = 0 := by
  funext component
  fin_cases component <;> simp [cubicalSpatialLower, cubicalStandardSpatial]

/-- The positive rest mode reads out as twice its upper-block embedding. -/
theorem uniform_rest_positive_readout_eq_double (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    uniformActionToStandardDirac r (fun _ => 0) (uniformRestPositivePhase r position) =
      2 • cubicalUpperEmbedding position := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlower :
      cubicalPhaseLower (r : ℂ) 0 0 0 (uniformRestPositivePhase r position) = position := by
    funext component
    simp only [cubicalPhaseLower, uniformRestPositivePhase, uniformPositiveFrequencyPhase,
      cubical_spatial_lower_zero,
      Pi.zero_apply, add_zero]
    apply (div_eq_iff hrC).2
    rw [← mul_assoc, ← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul, mul_comm]
  have hposition : (uniformRestPositivePhase r position).1 = position := rfl
  rw [uniform_action_readout_at_rest]
  funext component
  fin_cases component <;>
    simp [cubicalPhaseReadout, cubicalFromPositionLower, cubicalUpperEmbedding,
      hlower, hposition, add_comm, two_mul]

/-- The cube-parity beta grading is forced by the native positive rest
frequency after the lossless phase-space reconstruction. -/
theorem uniform_rest_positive_readout_has_positive_beta
    (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestPositivePhase r position)) =
      uniformActionToStandardDirac r (fun _ => 0)
        (uniformRestPositivePhase r position) := by
  rw [uniform_rest_positive_readout_eq_double r hr position]
  funext component
  fin_cases component <;> simp [cubicalStandardBeta, cubicalUpperEmbedding, two_mul]

/-- The opposite native rest frequency lands in the negative beta sector. -/
theorem uniform_rest_negative_readout_has_negative_beta
    (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position)) =
      fun component =>
        -uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position) component := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlower :
      cubicalPhaseLower (r : ℂ) 0 0 0 (uniformRestNegativePhase r position) = -position := by
    funext component
    simp only [cubicalPhaseLower, uniformRestNegativePhase, cubical_spatial_lower_zero,
      Pi.zero_apply, add_zero, Pi.neg_apply]
    apply (div_eq_iff hrC).2
    rw [← mul_assoc, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_comm, mul_neg, neg_mul]
  have hreadout :
      uniformActionToStandardDirac r (fun _ => 0) (uniformRestNegativePhase r position) =
        cubicalSpinorOfBlocks 0 (-(2 : ℂ) • position) := by
    rw [uniform_action_readout_at_rest, cubicalPhaseReadout, hlower]
    change cubicalSpinorOfBlocks (position + -position) (-position + -position) = _
    rw [add_neg_cancel]
    apply congrArg (cubicalSpinorOfBlocks 0)
    funext component
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hreadout]
  funext component
  fin_cases component <;> simp [cubicalStandardBeta]

theorem uniform_action_readout_add
    (r : ℝ) (momentum : LatticeMomentum) (first second : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (fun component => first.1 component + second.1 component,
         fun component => first.2 component + second.2 component) =
      fun component =>
        uniformActionToStandardDirac r momentum first component +
          uniformActionToStandardDirac r momentum second component :=
  cubical_phase_readout_add _ _ _ _ first second

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

theorem uniform_readout_tangent_is_position_dirac
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (uniformVacuumContinuumGenerator r momentum phase) =
      cubicalDiracTimeDerivative r
        (uniformActionToStandardDirac r momentum phase)
        (uniformPlaneWaveSpatialDerivative momentum
          (uniformActionToStandardDirac r momentum phase)) := by
  rw [uniform_action_tangent_intertwines_cubical_dirac r hr]
  exact cubical_standard_hamiltonian_is_position_dirac r momentum _

end
end LeanDirac.V2
