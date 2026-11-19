/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac008.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac007

/-!
DIRAC-008: complete native first-order evolution map.

The native equations remain the nonlinear, second-order, two-field equations
derived in DIRAC-003/004.  DIRAC-007 supplied an exact change of coordinates
from two committed layers to the current state and the backward interval
velocity.  This gate conjugates the unique action-stationary native update
through that change of coordinates.

Nothing is discarded: the map acts on the complete Psi/chi state and on all
thirty-two complex coordinates of the admitted unit-cell sector.  It is not a
linear Dirac operator and it does not select four components.  Linearization,
native four-component selection and Clifford algebra remain later gates.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section

def nativeLayerForward [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (layers : NativeTwoLayerState Site) : NativeTwoLayerState Site where
  previous := layers.current
  current := nativeNextState chi0 B dt bond layers.previous layers.current

def nativeLayerBackward [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (layers : NativeTwoLayerState Site) : NativeTwoLayerState Site where
  previous := nativeNextState chi0 B dt bond layers.current layers.previous
  current := layers.previous

theorem native_layer_backward_after_forward
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (layers : NativeTwoLayerState Site) :
    nativeLayerBackward chi0 B dt bond
        (nativeLayerForward chi0 B dt bond layers) = layers := by
  cases layers with
  | mk previous current =>
      apply congrArg₂ NativeTwoLayerState.mk
      · exact native_next_is_reversible chi0 B dt bond previous current
      · rfl

theorem native_layer_forward_after_backward
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (layers : NativeTwoLayerState Site) :
    nativeLayerForward chi0 B dt bond
        (nativeLayerBackward chi0 B dt bond layers) = layers := by
  cases layers with
  | mk previous current =>
      apply congrArg₂ NativeTwoLayerState.mk
      · rfl
      · exact native_next_is_reversible chi0 B dt bond current previous

def nativeLayerEvolutionEquiv
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site) :
    NativeTwoLayerState Site ≃ NativeTwoLayerState Site where
  toFun := nativeLayerForward chi0 B dt bond
  invFun := nativeLayerBackward chi0 B dt bond
  left_inv := native_layer_backward_after_forward chi0 B dt bond
  right_inv := native_layer_forward_after_backward chi0 B dt bond

def nativeRunningEvolutionEquiv
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site) :
    NativeRunningState Site ≃ NativeRunningState Site :=
  (nativeLayersRunningEquiv dt hdt).symm |>.trans
    ((nativeLayerEvolutionEquiv chi0 B dt bond).trans
      (nativeLayersRunningEquiv dt hdt))

def nativeRunningStep
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) : NativeRunningState Site :=
  nativeRunningEvolutionEquiv chi0 B dt hdt bond running

def nativeRunningStepBackward
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) : NativeRunningState Site :=
  (nativeRunningEvolutionEquiv chi0 B dt hdt bond).symm running

theorem native_running_backward_after_forward
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) :
    nativeRunningStepBackward chi0 B dt hdt bond
        (nativeRunningStep chi0 B dt hdt bond running) = running :=
  (nativeRunningEvolutionEquiv chi0 B dt hdt bond).left_inv running

theorem native_running_forward_after_backward
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) :
    nativeRunningStep chi0 B dt hdt bond
        (nativeRunningStepBackward chi0 B dt hdt bond running) = running :=
  (nativeRunningEvolutionEquiv chi0 B dt hdt bond).right_inv running

theorem native_running_step_is_action_layer_step
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) :
    nativeRunningStep chi0 B dt hdt bond running =
      nativePairedReadout dt
        (nativeLayerForward chi0 B dt bond
          (rebuildNativeLayers dt running)) := by
  rfl

theorem native_running_step_current
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) :
    (nativeRunningStep chi0 B dt hdt bond running).current =
      nativeNextState chi0 B dt bond
        (rebuildPreviousState dt running) running.current := by
  rfl

theorem native_running_step_current_psi
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) (site : Site) (component : Fin 3) :
    (nativeRunningStep chi0 B dt hdt bond running).current.psi site component =
      running.current.psi site component +
        (dt : ℂ) * running.intervalVelocity.psiDot site component +
        (dt ^ 2 : ℂ) *
          (accelerationVelocity chi0 B running.current bond).psiDot
            site component := by
  rw [native_running_step_current]
  simp [nativeNextState, rebuildPreviousState]
  ring

theorem native_running_step_current_chi
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) (site : Site) (component : Fin 3) :
    (nativeRunningStep chi0 B dt hdt bond running).current.chi site component =
      running.current.chi site component +
        (dt : ℂ) * running.intervalVelocity.chiDot site component +
        (dt ^ 2 : ℂ) *
          (accelerationVelocity chi0 B running.current bond).chiDot
            site component := by
  rw [native_running_step_current]
  simp [nativeNextState, rebuildPreviousState]
  ring

theorem native_running_step_interval_velocity
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) :
    (nativeRunningStep chi0 B dt hdt bond running).intervalVelocity =
      stateDifferenceVelocity dt running.current
        (nativeRunningStep chi0 B dt hdt bond running).current := by
  rfl

theorem native_running_step_velocity_psi
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) (site : Site) (component : Fin 3) :
    (nativeRunningStep chi0 B dt hdt bond running).intervalVelocity.psiDot
        site component =
      running.intervalVelocity.psiDot site component +
        (dt : ℂ) *
          (accelerationVelocity chi0 B running.current bond).psiDot
            site component := by
  rw [native_running_step_interval_velocity]
  simp [stateDifferenceVelocity]
  rw [native_running_step_current_psi]
  field_simp [hdt]
  ring

theorem native_running_step_velocity_chi
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (hdt : dt ≠ 0) (bond : Edge → Bond Site)
    (running : NativeRunningState Site) (site : Site) (component : Fin 3) :
    (nativeRunningStep chi0 B dt hdt bond running).intervalVelocity.chiDot
        site component =
      running.intervalVelocity.chiDot site component +
        (dt : ℂ) *
          (accelerationVelocity chi0 B running.current bond).chiDot
            site component := by
  rw [native_running_step_interval_velocity]
  simp [stateDifferenceVelocity]
  rw [native_running_step_current_chi]
  field_simp [hdt]
  ring

theorem native_running_step_is_action_stationary
    [Fintype Site] [DecidableEq Site]
    (dt : ℝ) (hdt : dt ≠ 0) (geometry : C19Lattice Site)
    (running : NativeRunningState Site) :
    IsDiscreteActionStationary chi0 chiKineticNormalization dt
      (rebuildPreviousState dt running) running.current
      (nativeRunningStep chi0 chiKineticNormalization dt hdt
        (c19Bond geometry) running).current
      (c19Bond geometry) := by
  rw [native_running_step_current]
  exact (dirac004_c19_update_iff_discrete_action_stationary
    dt geometry (rebuildPreviousState dt running) running.current hdt).stationary

theorem native_running_step_is_unique_action_stationary
    [Fintype Site] [DecidableEq Site]
    (dt : ℝ) (hdt : dt ≠ 0) (geometry : C19Lattice Site)
    (running : NativeRunningState Site) (next : State Site)
    (hstationary : IsDiscreteActionStationary
      chi0 chiKineticNormalization dt
      (rebuildPreviousState dt running) running.current next
      (c19Bond geometry)) :
    next = (nativeRunningStep chi0 chiKineticNormalization dt hdt
      (c19Bond geometry) running).current := by
  rw [native_running_step_current]
  exact (dirac004_c19_update_iff_discrete_action_stationary
    dt geometry (rebuildPreviousState dt running) running.current hdt).uniqueStationary
      next hstationary

theorem native_layer_forward_preserves_eight_site_sector
    [Fintype Edge]
    (chi0 B dt : ℝ) (hB : B ≠ 0)
    (bond : Edge → Bond CubeCorner)
    (layers : NativeTwoLayerState CubeCorner)
    (hprevious : InEightSiteSector layers.previous)
    (hcurrent : InEightSiteSector layers.current) :
    InEightSiteSector
        (nativeLayerForward chi0 B dt bond layers).previous ∧
      InEightSiteSector
        (nativeLayerForward chi0 B dt bond layers).current := by
  exact ⟨hcurrent,
    native_next_preserves_eight_site_sector chi0 B dt hB bond
      layers.previous layers.current hprevious hcurrent⟩

theorem native_layer_backward_preserves_eight_site_sector
    [Fintype Edge]
    (chi0 B dt : ℝ) (hB : B ≠ 0)
    (bond : Edge → Bond CubeCorner)
    (layers : NativeTwoLayerState CubeCorner)
    (hprevious : InEightSiteSector layers.previous)
    (hcurrent : InEightSiteSector layers.current) :
    InEightSiteSector
        (nativeLayerBackward chi0 B dt bond layers).previous ∧
      InEightSiteSector
        (nativeLayerBackward chi0 B dt bond layers).current := by
  exact ⟨native_next_preserves_eight_site_sector chi0 B dt hB bond
      layers.current layers.previous hcurrent hprevious,
    hprevious⟩

theorem native_running_step_preserves_eight_site_sector
    (dt : ℝ) (hdt : dt ≠ 0) (running : NativeRunningState CubeCorner)
    (hrunning : InEightSiteRunningSector running) :
    InEightSiteRunningSector
      (nativeRunningStep chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry) running) := by
  have hlayers := rebuild_native_layers_preserves_eight_site_sector
    dt running hrunning
  have hB : chiKineticNormalization ≠ 0 := by
    rw [chi_kinetic_normalization_eq_1197]
    norm_num
  have hforward := native_layer_forward_preserves_eight_site_sector
    chi0 chiKineticNormalization dt hB (c19Bond cubeC19Geometry)
    (rebuildNativeLayers dt running) hlayers.1 hlayers.2
  exact native_paired_readout_preserves_eight_site_sector dt
    (nativeLayerForward chi0 chiKineticNormalization dt
      (c19Bond cubeC19Geometry) (rebuildNativeLayers dt running))
    hforward.1 hforward.2

theorem native_running_step_backward_preserves_eight_site_sector
    (dt : ℝ) (hdt : dt ≠ 0) (running : NativeRunningState CubeCorner)
    (hrunning : InEightSiteRunningSector running) :
    InEightSiteRunningSector
      (nativeRunningStepBackward chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry) running) := by
  have hlayers := rebuild_native_layers_preserves_eight_site_sector
    dt running hrunning
  have hB : chiKineticNormalization ≠ 0 := by
    rw [chi_kinetic_normalization_eq_1197]
    norm_num
  have hbackward := native_layer_backward_preserves_eight_site_sector
    chi0 chiKineticNormalization dt hB (c19Bond cubeC19Geometry)
    (rebuildNativeLayers dt running) hlayers.1 hlayers.2
  exact native_paired_readout_preserves_eight_site_sector dt
    (nativeLayerBackward chi0 chiKineticNormalization dt
      (c19Bond cubeC19Geometry) (rebuildNativeLayers dt running))
    hbackward.1 hbackward.2

def nativeRunningSectorEvolutionEquiv (dt : ℝ) (hdt : dt ≠ 0) :
    NativeRunningSector ≃ NativeRunningSector where
  toFun running :=
    ⟨nativeRunningStep chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry) running.1,
      native_running_step_preserves_eight_site_sector dt hdt
        running.1 running.2⟩
  invFun running :=
    ⟨nativeRunningStepBackward chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry) running.1,
      native_running_step_backward_preserves_eight_site_sector dt hdt
        running.1 running.2⟩
  left_inv := by
    intro running
    apply Subtype.ext
    exact native_running_backward_after_forward
      chi0 chiKineticNormalization dt hdt (c19Bond cubeC19Geometry) running.1
  right_inv := by
    intro running
    apply Subtype.ext
    exact native_running_forward_after_backward
      chi0 chiKineticNormalization dt hdt (c19Bond cubeC19Geometry) running.1

def nativeCoordinateEvolutionEquiv (dt : ℝ) (hdt : dt ≠ 0) :
    (NativeUnitCellRunningCoordinate → ℂ) ≃
      (NativeUnitCellRunningCoordinate → ℂ) :=
  (nativeRunningSectorCoordinateEquiv dt hdt).symm |>.trans
    ((nativeRunningSectorEvolutionEquiv dt hdt).trans
      (nativeRunningSectorCoordinateEquiv dt hdt))

theorem native_coordinate_evolution_is_sector_step
    (dt : ℝ) (hdt : dt ≠ 0) (running : NativeRunningSector) :
    nativeCoordinateEvolutionEquiv dt hdt
        (nativeRunningSectorCoordinateEquiv dt hdt running) =
      nativeRunningSectorCoordinateEquiv dt hdt
        (nativeRunningSectorEvolutionEquiv dt hdt running) := by
  simp [nativeCoordinateEvolutionEquiv]

theorem native_coordinate_backward_after_forward
    (dt : ℝ) (hdt : dt ≠ 0)
    (coordinates : NativeUnitCellRunningCoordinate → ℂ) :
    (nativeCoordinateEvolutionEquiv dt hdt).symm
        (nativeCoordinateEvolutionEquiv dt hdt coordinates) = coordinates :=
  (nativeCoordinateEvolutionEquiv dt hdt).left_inv coordinates

theorem native_coordinate_forward_after_backward
    (dt : ℝ) (hdt : dt ≠ 0)
    (coordinates : NativeUnitCellRunningCoordinate → ℂ) :
    nativeCoordinateEvolutionEquiv dt hdt
        ((nativeCoordinateEvolutionEquiv dt hdt).symm coordinates) =
      coordinates :=
  (nativeCoordinateEvolutionEquiv dt hdt).right_inv coordinates

structure Dirac008Certificate (dt : ℝ) (hdt : dt ≠ 0) : Prop where
  actionStationary : ∀ running : NativeRunningState CubeCorner,
    IsDiscreteActionStationary chi0 chiKineticNormalization dt
      (rebuildPreviousState dt running) running.current
      (nativeRunningStep chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry) running).current
      (c19Bond cubeC19Geometry)
  uniqueActionStep : ∀ (running : NativeRunningState CubeCorner)
      (next : State CubeCorner),
    IsDiscreteActionStationary chi0 chiKineticNormalization dt
      (rebuildPreviousState dt running) running.current next
      (c19Bond cubeC19Geometry) →
    next = (nativeRunningStep chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running).current
  explicitCurrentPsi : ∀ running site component,
    (nativeRunningStep chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running).current.psi site component =
      running.current.psi site component +
        (dt : ℂ) * running.intervalVelocity.psiDot site component +
        (dt ^ 2 : ℂ) *
          (accelerationVelocity chi0 chiKineticNormalization running.current
            (c19Bond cubeC19Geometry)).psiDot site component
  explicitCurrentChi : ∀ running site component,
    (nativeRunningStep chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running).current.chi site component =
      running.current.chi site component +
        (dt : ℂ) * running.intervalVelocity.chiDot site component +
        (dt ^ 2 : ℂ) *
          (accelerationVelocity chi0 chiKineticNormalization running.current
            (c19Bond cubeC19Geometry)).chiDot site component
  explicitVelocityPsi : ∀ running site component,
    (nativeRunningStep chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running).intervalVelocity.psiDot
        site component =
      running.intervalVelocity.psiDot site component +
        (dt : ℂ) *
          (accelerationVelocity chi0 chiKineticNormalization running.current
            (c19Bond cubeC19Geometry)).psiDot site component
  explicitVelocityChi : ∀ running site component,
    (nativeRunningStep chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running).intervalVelocity.chiDot
        site component =
      running.intervalVelocity.chiDot site component +
        (dt : ℂ) *
          (accelerationVelocity chi0 chiKineticNormalization running.current
            (c19Bond cubeC19Geometry)).chiDot site component
  runningRoundTrips :
    (∀ running : NativeRunningState CubeCorner,
      nativeRunningStepBackward chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry)
        (nativeRunningStep chi0 chiKineticNormalization dt hdt
          (c19Bond cubeC19Geometry) running) = running) ∧
    (∀ running : NativeRunningState CubeCorner,
      nativeRunningStep chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry)
        (nativeRunningStepBackward chi0 chiKineticNormalization dt hdt
          (c19Bond cubeC19Geometry) running) = running)
  sectorPreserved : ∀ running : NativeRunningState CubeCorner,
    InEightSiteRunningSector running →
    InEightSiteRunningSector
      (nativeRunningStep chi0 chiKineticNormalization dt hdt
        (c19Bond cubeC19Geometry) running)
  coordinateEvolutionConjugate : ∀ running : NativeRunningSector,
    nativeCoordinateEvolutionEquiv dt hdt
        (nativeRunningSectorCoordinateEquiv dt hdt running) =
      nativeRunningSectorCoordinateEquiv dt hdt
        (nativeRunningSectorEvolutionEquiv dt hdt running)
  coordinateRoundTrips :
    (∀ coordinates : NativeUnitCellRunningCoordinate → ℂ,
      (nativeCoordinateEvolutionEquiv dt hdt).symm
        (nativeCoordinateEvolutionEquiv dt hdt coordinates) = coordinates) ∧
    (∀ coordinates : NativeUnitCellRunningCoordinate → ℂ,
      nativeCoordinateEvolutionEquiv dt hdt
        ((nativeCoordinateEvolutionEquiv dt hdt).symm coordinates) =
          coordinates)
  coordinateCount : Fintype.card NativeUnitCellRunningCoordinate = 32

theorem dirac008_complete_native_first_order_map
    (dt : ℝ) (hdt : dt ≠ 0) : Dirac008Certificate dt hdt where
  actionStationary := fun running =>
    native_running_step_is_action_stationary dt hdt cubeC19Geometry running
  uniqueActionStep := fun running next hstationary =>
    native_running_step_is_unique_action_stationary
      dt hdt cubeC19Geometry running next hstationary
  explicitCurrentPsi := fun running site component =>
    native_running_step_current_psi chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running site component
  explicitCurrentChi := fun running site component =>
    native_running_step_current_chi chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running site component
  explicitVelocityPsi := fun running site component =>
    native_running_step_velocity_psi chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running site component
  explicitVelocityChi := fun running site component =>
    native_running_step_velocity_chi chi0 chiKineticNormalization dt hdt
      (c19Bond cubeC19Geometry) running site component
  runningRoundTrips :=
    ⟨native_running_backward_after_forward
      chi0 chiKineticNormalization dt hdt (c19Bond cubeC19Geometry),
    native_running_forward_after_backward
      chi0 chiKineticNormalization dt hdt (c19Bond cubeC19Geometry)⟩
  sectorPreserved := native_running_step_preserves_eight_site_sector dt hdt
  coordinateEvolutionConjugate :=
    native_coordinate_evolution_is_sector_step dt hdt
  coordinateRoundTrips :=
    ⟨native_coordinate_backward_after_forward dt hdt,
      native_coordinate_forward_after_backward dt hdt⟩
  coordinateCount := native_unit_cell_running_coordinate_count

end
end LeanDirac
