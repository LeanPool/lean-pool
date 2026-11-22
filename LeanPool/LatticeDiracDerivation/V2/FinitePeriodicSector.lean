/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.FinitePeriodicTangent
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumCurrentBridge
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumDiscreteTime

/-!
# The invariant native periodic tangent sector

This module makes the embedding omitted by a mode-only calculation explicit.
The source is the actual two-channel transverse tangent field on a finite
periodic C19 lattice.  Its generator is the action-Hessian force proved in
`FinitePeriodicTangent`.  A compatible Fourier character embeds four complex
phase coordinates into that full lattice field, and the native generator
preserves the image.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Site : Type}

open Complex
noncomputable section

private theorem nativeVelocityExt
    {Site : Type} (first second : Velocity Site)
    (hpsi : first.psiDot = second.psiDot)
    (hchi : first.chiDot = second.chiDot) : first = second := by
  cases first
  cases second
  simp_all

/-- The positions and velocities of the two transverse fields on the periodic lattice. -/
structure PeriodicTransversePhase (L : ℕ) [NeZero L] where
  /-- The two transverse positions at each lattice site. -/
  position : Fin 2 → PeriodicCubicSite L → ℂ
  /-- The two transverse velocities at each lattice site. -/
  velocity : Fin 2 → PeriodicCubicSite L → ℂ

@[ext] theorem PeriodicTransversePhase.ext
    {L : ℕ} [NeZero L]
    (first second : PeriodicTransversePhase L)
    (hposition : first.position = second.position)
    (hvelocity : first.velocity = second.velocity) : first = second := by
  cases first
  cases second
  simp_all

/-- The generator on the position and velocity of the two transverse components. -/
def periodicTransverseGenerator
    {L : ℕ} [NeZero L] (r : ℝ)
    (phase : PeriodicTransversePhase L) : PeriodicTransversePhase L where
  position := phase.velocity
  velocity := fun component site =>
    periodicC19LinearizedAcceleration r (phase.position component) site

/-- Embed a two-channel Fourier phase in the corresponding periodic scalar fields. -/
def periodicModePhaseEmbed
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) : PeriodicTransversePhase L where
  position := fun component =>
    periodicModeField mode (phase.1 component)
  velocity := fun component =>
    periodicModeField mode (phase.2 component)

/-- The position part of the same mode written as an honest tangent vector
in the complete native two-field state space.  It perturbs the first two
`Psi` channels and has zero `chi` tangent; the uniform vacuum itself is kept
separate from its tangent vector. -/
def periodicNativeTangentState
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (position : UniformCell2) : State (PeriodicCubicSite L) where
  psi := fun site component =>
    if component = 0 then periodicModeField mode (position 0) site
    else if component = 1 then periodicModeField mode (position 1) site
    else 0
  chi := fun _ _ => 0

/-- The velocity part of the complete native tangent vector. -/
def periodicNativeTangentVelocity
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (velocity : UniformCell2) : Velocity (PeriodicCubicSite L) where
  psiDot := fun site component =>
    if component = 0 then periodicModeField mode (velocity 0) site
    else if component = 1 then periodicModeField mode (velocity 1) site
    else 0
  chiDot := fun _ _ => 0

/-- Explicit embedding into the complete native tangent phase space.  No
spinor coordinates or auxiliary fields occur in this map. -/
def periodicFullNativeTangentEmbed
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    State (PeriodicCubicSite L) × Velocity (PeriodicCubicSite L) :=
  (periodicNativeTangentState mode phase.1,
    periodicNativeTangentVelocity mode phase.2)

/-- The native first-order tangent generator, written on the complete
`State × Velocity` phase-space representation and restricted only by the
uniform-vacuum transverse Hessian itself.  Its position derivative is the
native velocity.  Its two nonzero acceleration channels are the C19 Riesz
forces obtained from the native action Hessian; the complementary channels
are zero on this tangent sector.  In particular, this definition contains
no modal eigenvalue and no Dirac operator. -/
def periodicNativeTransverseTangentGenerator
    {L : ℕ} (r : ℝ)
    (native : State (PeriodicCubicSite L) ×
      Velocity (PeriodicCubicSite L)) :
    State (PeriodicCubicSite L) × Velocity (PeriodicCubicSite L) :=
  ({ psi := native.2.psiDot
     chi := native.2.chiDot },
   { psiDot := fun site component =>
       if component = 0 then
         periodicC19LinearizedAcceleration r
           (fun neighbor => native.1.psi neighbor 0) site
       else if component = 1 then
         periodicC19LinearizedAcceleration r
           (fun neighbor => native.1.psi neighbor 1) site
       else 0
     chiDot := fun _ _ => 0 })

/-- The affine finite-amplitude state used only to evaluate the full native
action around its uniform vacuum.  This is deliberately distinct from the
tangent embedding above. -/
def periodicAffineModePhaseState
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    State (PeriodicCubicSite L) × Velocity (PeriodicCubicSite L) :=
  (periodicModeState r 1 mode phase.1,
    periodicModeVelocity 1 mode phase.2)

theorem periodic_mode_character_nonzero
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (site : PeriodicCubicSite L) : mode.character site ≠ 0 := by
  intro hzero
  have hnorm := mode.normSq_one site
  simp [hzero] at hnorm

theorem periodic_mode_phase_embed_injective
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum) :
    Function.Injective (periodicModePhaseEmbed mode) := by
  intro first second heq
  have hposition := congrArg PeriodicTransversePhase.position heq
  have hvelocity := congrArg PeriodicTransversePhase.velocity heq
  let origin : PeriodicCubicSite L := fun _ => 0
  have hcharacter : mode.character origin ≠ 0 :=
    periodic_mode_character_nonzero mode origin
  apply Prod.ext
  · funext component
    have hcomponent := congrFun (congrFun hposition component) origin
    unfold periodicModePhaseEmbed periodicModeField at hcomponent
    exact (mul_left_cancel₀ hcharacter hcomponent)
  · funext component
    have hcomponent := congrFun (congrFun hvelocity component) origin
    unfold periodicModePhaseEmbed periodicModeField at hcomponent
    exact (mul_left_cancel₀ hcharacter hcomponent)

theorem periodic_full_native_tangent_embed_injective
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum) :
    Function.Injective (periodicFullNativeTangentEmbed mode) := by
  intro first second heq
  have hstate := congrArg Prod.fst heq
  have hvelocity := congrArg Prod.snd heq
  let origin : PeriodicCubicSite L := fun _ => 0
  have hcharacter : mode.character origin ≠ 0 :=
    periodic_mode_character_nonzero mode origin
  apply Prod.ext
  · funext component
    fin_cases component
    · have hcomponent := congrArg
        (fun state => state.psi origin (0 : Fin 3)) hstate
      simp only [periodicFullNativeTangentEmbed,
        periodicNativeTangentState, periodicModeField] at hcomponent
      exact mul_left_cancel₀ hcharacter hcomponent
    · have hcomponent := congrArg
        (fun state => state.psi origin (1 : Fin 3)) hstate
      simp only [periodicFullNativeTangentEmbed,
        periodicNativeTangentState, periodicModeField] at hcomponent
      exact mul_left_cancel₀ hcharacter hcomponent
  · funext component
    fin_cases component
    · have hcomponent := congrArg
        (fun velocity => velocity.psiDot origin (0 : Fin 3)) hvelocity
      simp only [periodicFullNativeTangentEmbed,
        periodicNativeTangentVelocity, periodicModeField] at hcomponent
      exact mul_left_cancel₀ hcharacter hcomponent
    · have hcomponent := congrArg
        (fun velocity => velocity.psiDot origin (1 : Fin 3)) hvelocity
      simp only [periodicFullNativeTangentEmbed,
        periodicNativeTangentVelocity, periodicModeField] at hcomponent
      exact mul_left_cancel₀ hcharacter hcomponent

/-- One commuting equality for the complete native phase-space coordinates.
The full `State × Velocity` tangent generator sends the embedded Fourier
phase to the embedding of the modal Euler--Lagrange generator.  Thus kinetic
closure and force closure are established together rather than inferred
from a list of scalar pairings. -/
theorem periodic_full_native_tangent_generator_intertwines
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    periodicNativeTransverseTangentGenerator r
        (periodicFullNativeTangentEmbed mode phase) =
      periodicFullNativeTangentEmbed mode
        (uniformVacuumNativeGenerator r momentum phase) := by
  apply Prod.ext
  · cases phase with
    | mk position velocity =>
      rfl
  · apply nativeVelocityExt
    · funext site component
      fin_cases component
      · simp only [periodicNativeTransverseTangentGenerator,
          periodicFullNativeTangentEmbed, periodicNativeTangentState,
          periodicNativeTangentVelocity, ite_eq_left]
        exact periodic_c19_linearized_force_is_modal_acceleration
          r mode phase.1 0 site
      · simp only [periodicNativeTransverseTangentGenerator,
          periodicFullNativeTangentEmbed, periodicNativeTangentState,
          periodicNativeTangentVelocity, Fin.isValue, ite_eq_left]
        exact periodic_c19_linearized_force_is_modal_acceleration
          r mode phase.1 1 site
      · simp [periodicNativeTransverseTangentGenerator,
          periodicFullNativeTangentEmbed, periodicNativeTangentVelocity]
    · rfl

/-- True sector closure: the full finite-lattice transverse Hessian generator
maps an embedded Fourier phase state to the embedding of the modal native
generator. -/
theorem periodic_mode_sector_is_invariant
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    periodicTransverseGenerator r (periodicModePhaseEmbed mode phase) =
      periodicModePhaseEmbed mode
        (uniformVacuumNativeGenerator r momentum phase) := by
  apply PeriodicTransversePhase.ext
  · funext component site
    rfl
  · funext component site
    change periodicC19LinearizedAcceleration r
        (periodicModeField mode (phase.1 component)) site = _
    rw [periodic_c19_linearized_force_diagonalizes]
    simp only [periodicModePhaseEmbed, periodicModeField,
      uniformVacuumNativeGenerator, uniformVacuumModalAcceleration,
      uniformVacuumModalSquare]
    push_cast
    ring

/-- Full native weak Euler--Lagrange closure of the periodic four-complex-
dimensional tangent sector.  The first clause makes the embedding into
`(delta Psi, delta chi, delta PsiDot, delta chiDot)` lossless.  The second
identifies both retained accelerations by differentiating the full native
potential twice.  The next two clauses prove zero leakage into longitudinal
`Psi` and live `chi`; the final clause is the resulting sitewise invariant
Fourier evolution. -/
theorem periodic_full_native_tangent_sector_is_action_invariant
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    Function.Injective (periodicFullNativeTangentEmbed mode) ∧
      (∀ component site testAmplitude,
        AnalyticHasDerivAt
          (fun eps : ℝ =>
            potentialFirstVariation r
              (periodicTransverseComponentState r eps component
                (periodicModeField mode (phase.1 component)))
              (periodicTransverseComponentDirection component
                (periodicSingleSiteScalarDirection site testAmplitude))
              (c19Bond (periodicC19Geometry L)))
          (-uniformScalarRealPair
            (periodicModeField mode
              ((uniformVacuumModalAcceleration r momentum phase.1)
                component) site)
            testAmplitude) 0) ∧
      (∀ eps longitudinal,
        potentialFirstVariation r
          (uniformTransverseState r eps
            (periodicModeField mode (phase.1 0))
            (periodicModeField mode (phase.1 1)))
          (periodicLongitudinalPsiDirection longitudinal)
          (c19Bond (periodicC19Geometry L)) = 0) ∧
      (∀ chiDirection,
        AnalyticHasDerivAt
          (fun eps : ℝ =>
            potentialFirstVariation r
              (uniformTransverseState r eps
                (periodicModeField mode (phase.1 0))
                (periodicModeField mode (phase.1 1)))
              (pureChiDirection chiDirection)
              (c19Bond (periodicC19Geometry L))) 0 0) ∧
      periodicTransverseGenerator r (periodicModePhaseEmbed mode phase) =
        periodicModePhaseEmbed mode
          (uniformVacuumNativeGenerator r momentum phase) := by
  exact ⟨periodic_full_native_tangent_embed_injective mode,
    fun component site testAmplitude =>
      periodic_c19_action_hessian_mode_force
        r hr mode phase.1 component site testAmplitude,
    fun eps longitudinal =>
      periodic_c19_transverse_longitudinal_cross_variation_zero
        r eps longitudinal
          (periodicModeField mode (phase.1 0))
          (periodicModeField mode (phase.1 1)),
    fun chiDirection =>
      periodic_c19_transverse_chi_cross_hessian_zero r
        (periodicModeField mode (phase.1 0))
        (periodicModeField mode (phase.1 1)) chiDirection,
    periodic_mode_sector_is_invariant r mode phase⟩

/-- The single full phase-space intertwiner together with its action-level
provenance.  The first equality contains both the native position derivative
and every velocity derivative in the full `State × Velocity` representation;
the remaining clauses certify that the two retained forces are exactly the
Riesz representatives of the full native action Hessian and that no
longitudinal `Psi` or live-`chi` response is generated. -/
theorem periodic_full_native_action_generator_intertwines
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    periodicNativeTransverseTangentGenerator r
        (periodicFullNativeTangentEmbed mode phase) =
      periodicFullNativeTangentEmbed mode
        (uniformVacuumNativeGenerator r momentum phase) ∧
      (∀ component site testAmplitude,
        AnalyticHasDerivAt
          (fun eps : ℝ =>
            potentialFirstVariation r
              (periodicTransverseComponentState r eps component
                (periodicModeField mode (phase.1 component)))
              (periodicTransverseComponentDirection component
                (periodicSingleSiteScalarDirection site testAmplitude))
              (c19Bond (periodicC19Geometry L)))
          (-uniformScalarRealPair
            (periodicModeField mode
              ((uniformVacuumModalAcceleration r momentum phase.1)
                component) site)
            testAmplitude) 0) ∧
      (∀ eps longitudinal,
        potentialFirstVariation r
          (uniformTransverseState r eps
            (periodicModeField mode (phase.1 0))
            (periodicModeField mode (phase.1 1)))
          (periodicLongitudinalPsiDirection longitudinal)
          (c19Bond (periodicC19Geometry L)) = 0) ∧
      (∀ chiDirection,
        AnalyticHasDerivAt
          (fun eps : ℝ =>
            potentialFirstVariation r
              (uniformTransverseState r eps
                (periodicModeField mode (phase.1 0))
                (periodicModeField mode (phase.1 1)))
              (pureChiDirection chiDirection)
              (c19Bond (periodicC19Geometry L))) 0 0) := by
  rcases periodic_full_native_tangent_sector_is_action_invariant
      r hr mode phase with
    ⟨_, hforce, hlongitudinal, hchi, _⟩
  exact ⟨periodic_full_native_tangent_generator_intertwines r mode phase,
    hforce, hlongitudinal, hchi⟩

/-- The explicit finite-lattice sector and the four-component readout form
one commuting diagram.  The only finite-spacing departure is the displayed
C19 remainder already bounded in `C19Fourier`. -/
theorem periodic_native_sector_intertwines_dirac_with_remainder
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    periodicTransverseGenerator r (periodicModePhaseEmbed mode phase) =
        periodicModePhaseEmbed mode
          (uniformVacuumNativeGenerator r momentum phase) ∧
      uniformActionToStandardDirac r momentum
          (uniformVacuumNativeGenerator r momentum phase) =
        fun component =>
          -I * cubicalStandardHamiltonian (r : ℂ)
            (uniformContinuumPx momentum)
            (uniformContinuumPy momentum)
            (uniformContinuumPz momentum)
            (uniformActionToStandardDirac r momentum phase) component +
          uniformActionToStandardDirac r momentum
            (uniformNativeSpatialDefectPhase momentum phase) component := by
  refine ⟨periodic_mode_sector_is_invariant r mode phase, ?_⟩
  rw [uniform_native_generator_exact_defect]
  rw [show uniformActionToStandardDirac r momentum
      (fun channel =>
          (uniformVacuumContinuumGenerator r momentum phase).1 channel +
            (uniformNativeSpatialDefectPhase momentum phase).1 channel,
       fun channel =>
          (uniformVacuumContinuumGenerator r momentum phase).2 channel +
            (uniformNativeSpatialDefectPhase momentum phase).2 channel) =
      fun output =>
        uniformActionToStandardDirac r momentum
            (uniformVacuumContinuumGenerator r momentum phase) output +
          uniformActionToStandardDirac r momentum
            (uniformNativeSpatialDefectPhase momentum phase) output by
    unfold uniformActionToStandardDirac
    exact cubical_phase_readout_add _ _ _ _ _ _]
  rw [uniform_action_tangent_intertwines_cubical_dirac r hr]

/-- Native charge continuity for the same force used in the periodic action Hessian. -/
theorem periodic_c19_native_tangent_local_continuity {L : ℕ}
    (r : ℝ) (position velocity : PeriodicCubicSite L → ℂ) (site : PeriodicCubicSite L) :
    uniformNativePhaseDensityDerivative (position site) (velocity site)
        (periodicC19LinearizedAcceleration r position site) +
      uniformNativeOutwardCurrentDivergence (periodicC19Geometry L) position site = 0 :=
  uniform_native_tangent_local_continuity (r ^ 2) (periodicC19Geometry L) position velocity site

end
end LeanDirac.V2
