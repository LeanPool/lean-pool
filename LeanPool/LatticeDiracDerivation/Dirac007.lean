/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac007.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac006Restriction

/-!
DIRAC-007: lossless native paired readout.

The native update carries two committed `State` layers.  This gate changes
coordinates, without reducing them, to the current native state and the
backward interval velocity already used by the DIRAC-004 action.  That
velocity belongs to the interval from the previous layer to the current
layer; it is not silently treated as a same-time continuum derivative.  At
nonzero timestep the map is invertible in both directions.  It acts on the
complete Psi/chi state, so it supplies no four-component selector, spinor or
first-order evolution rule.  Constructing the latter is the separate
DIRAC-008 gate.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section

/-- A pair of states at two consecutive time steps. -/
structure NativeTwoLayerState (Site : Type) where
  /-- The state at the earlier time step. -/
  previous : State Site
  /-- The state at the later time step. -/
  current : State Site

/-- A state together with a velocity, used as position-velocity coordinates for two time
steps. -/
structure NativeRunningState (Site : Type) where
  /-- The state at the current time step. -/
  current : State Site
  /-- The difference quotient of the state over the preceding time interval. -/
  intervalVelocity : Velocity Site

/-- The map sending two layers to the current layer and the backward difference quotient
`(current - previous) / dt`. -/
def nativePairedReadout (dt : ℝ) (layers : NativeTwoLayerState Site) :
    NativeRunningState Site where
  current := layers.current
  intervalVelocity := stateDifferenceVelocity dt layers.previous layers.current

/-- The state `current - dt * intervalVelocity`, computed componentwise for `psi` and `chi`. -/
def rebuildPreviousState (dt : ℝ) (running : NativeRunningState Site) :
    State Site where
  psi := fun site component =>
    running.current.psi site component -
      (dt : ℂ) * running.intervalVelocity.psiDot site component
  chi := fun site component =>
    running.current.chi site component -
      (dt : ℂ) * running.intervalVelocity.chiDot site component

/-- The two layers with previous layer `rebuildPreviousState dt running` and current layer
`running.current`. -/
def rebuildNativeLayers (dt : ℝ) (running : NativeRunningState Site) :
    NativeTwoLayerState Site where
  previous := rebuildPreviousState dt running
  current := running.current

theorem rebuild_previous_after_native_readout
    (dt : ℝ) (hdt : dt ≠ 0) (previous current : State Site) :
    rebuildPreviousState dt
        (nativePairedReadout dt ⟨previous, current⟩) = previous := by
  apply congrArg₂ State.mk <;> funext site component <;>
    simp [nativePairedReadout, stateDifferenceVelocity] <;>
    field_simp [hdt] <;> ring

theorem rebuild_after_native_readout
    (dt : ℝ) (hdt : dt ≠ 0) (layers : NativeTwoLayerState Site) :
    rebuildNativeLayers dt (nativePairedReadout dt layers) = layers := by
  cases layers with
  | mk previous current =>
      apply congrArg₂ NativeTwoLayerState.mk
      · exact rebuild_previous_after_native_readout dt hdt previous current
      · rfl

theorem native_readout_after_rebuild
    (dt : ℝ) (hdt : dt ≠ 0) (running : NativeRunningState Site) :
    nativePairedReadout dt (rebuildNativeLayers dt running) = running := by
  cases running with
  | mk position velocity =>
      apply congrArg₂ NativeRunningState.mk
      · rfl
      · apply congrArg₂ Velocity.mk <;> funext site component <;>
          simp [rebuildNativeLayers, rebuildPreviousState] <;>
          field_simp [hdt]

/-- For nonzero `dt`, the equivalence between two-layer states and position-velocity states
given by `nativePairedReadout dt` with inverse `rebuildNativeLayers dt`. -/
def nativeLayersRunningEquiv (dt : ℝ) (hdt : dt ≠ 0) :
    NativeTwoLayerState Site ≃ NativeRunningState Site where
  toFun := nativePairedReadout dt
  invFun := rebuildNativeLayers dt
  left_inv := rebuild_after_native_readout dt hdt
  right_inv := native_readout_after_rebuild dt hdt

/-- The cube velocity whose `psi` part at each corner is `psiVelocity corner` times
`tetraCorner corner` and whose `chi` part is `chiVelocity corner` times `companion corner`. -/
def alignedEightSiteVelocity (psiVelocity chiVelocity : Cell8) :
    Velocity CubeCorner where
  psiDot corner := c3ScaleComplex (psiVelocity corner) (tetraCorner corner)
  chiDot corner := c3ScaleComplex (chiVelocity corner) (companion corner)

/-- A cube velocity lies in the eight-site sector if it equals `alignedEightSiteVelocity` for
some pair of eight-corner amplitudes. -/
def InEightSiteVelocitySector (velocity : Velocity CubeCorner) : Prop :=
  ∃ psiVelocity chiVelocity,
    velocity = alignedEightSiteVelocity psiVelocity chiVelocity

/-- Both the state and the velocity of a position-velocity cube state lie in the eight-site
sector. -/
def InEightSiteRunningSector
    (running : NativeRunningState CubeCorner) : Prop :=
  InEightSiteSector running.current ∧
    InEightSiteVelocitySector running.intervalVelocity

theorem state_difference_velocity_preserves_eight_site_sector
    (dt : ℝ) (previous current : State CubeCorner)
    (hprevious : InEightSiteSector previous)
    (hcurrent : InEightSiteSector current) :
    InEightSiteVelocitySector
      (stateDifferenceVelocity dt previous current) := by
  rcases hprevious with ⟨previousPsi, previousChi, rfl⟩
  rcases hcurrent with ⟨currentPsi, currentChi, rfl⟩
  refine ⟨fun corner =>
      (currentPsi corner - previousPsi corner) / (dt : ℂ),
    fun corner =>
      (currentChi corner - previousChi corner) / (dt : ℂ), ?_⟩
  apply congrArg₂ Velocity.mk <;> funext corner component <;>
    simp [alignedEightSiteState, c3ScaleComplex] <;> ring

theorem native_paired_readout_preserves_eight_site_sector
    (dt : ℝ) (layers : NativeTwoLayerState CubeCorner)
    (hprevious : InEightSiteSector layers.previous)
    (hcurrent : InEightSiteSector layers.current) :
    InEightSiteRunningSector (nativePairedReadout dt layers) := by
  exact ⟨hcurrent,
    state_difference_velocity_preserves_eight_site_sector dt
      layers.previous layers.current hprevious hcurrent⟩

theorem rebuild_previous_preserves_eight_site_sector
    (dt : ℝ) (position : State CubeCorner)
    (velocity : Velocity CubeCorner)
    (hposition : InEightSiteSector position)
    (hvelocity : InEightSiteVelocitySector velocity) :
    InEightSiteSector
      (rebuildPreviousState dt ⟨position, velocity⟩) := by
  rcases hposition with ⟨positionPsi, positionChi, rfl⟩
  rcases hvelocity with ⟨velocityPsi, velocityChi, rfl⟩
  refine ⟨fun corner =>
      positionPsi corner - (dt : ℂ) * velocityPsi corner,
    fun corner =>
      positionChi corner - (dt : ℂ) * velocityChi corner, ?_⟩
  apply congrArg₂ State.mk <;> funext corner component <;>
    simp [alignedEightSiteState, alignedEightSiteVelocity,
      c3ScaleComplex] <;> ring

theorem rebuild_native_layers_preserves_eight_site_sector
    (dt : ℝ) (running : NativeRunningState CubeCorner)
    (hrunning : InEightSiteRunningSector running) :
    InEightSiteSector (rebuildNativeLayers dt running).previous ∧
      InEightSiteSector (rebuildNativeLayers dt running).current := by
  exact ⟨rebuild_previous_preserves_eight_site_sector dt
      running.current running.intervalVelocity hrunning.1 hrunning.2,
    hrunning.1⟩

/-- The subtype of two-layer cube states whose both layers lie in the eight-site sector. -/
abbrev NativeTwoLayerSector :=
  { layers : NativeTwoLayerState CubeCorner //
    InEightSiteSector layers.previous ∧ InEightSiteSector layers.current }

/-- The subtype of position-velocity cube states lying in `InEightSiteRunningSector`. -/
abbrev NativeRunningSector :=
  { running : NativeRunningState CubeCorner //
    InEightSiteRunningSector running }

/-- A pair of unit-cell amplitude pairs, one for each of two layers. -/
abbrev NativeTwoLayerAmplitudes :=
  NativeUnitCellAmplitudes × NativeUnitCellAmplitudes

/-- The thirty-two coordinate indices `NativeUnitCellTwoLayerCoordinate`, used for the
position-velocity sector. -/
abbrev NativeUnitCellRunningCoordinate :=
  NativeUnitCellTwoLayerCoordinate

/-- Flattens two layers of amplitudes into a function on the thirty-two coordinates, using
`nativeUnitCellAmplitudeCoordinates` on each layer. -/
def nativeTwoLayerAmplitudeCoordinates
    (amplitudes : NativeTwoLayerAmplitudes) :
    NativeUnitCellRunningCoordinate → ℂ
  | Sum.inl coordinate =>
      nativeUnitCellAmplitudeCoordinates amplitudes.1 coordinate
  | Sum.inr coordinate =>
      nativeUnitCellAmplitudeCoordinates amplitudes.2 coordinate

/-- Splits a function on the thirty-two coordinates into two layers of amplitudes, using
`nativeUnitCellCoordinatesAmplitude` on each summand. -/
def nativeTwoLayerCoordinatesAmplitude
    (coordinates : NativeUnitCellRunningCoordinate → ℂ) :
    NativeTwoLayerAmplitudes :=
  (nativeUnitCellCoordinatesAmplitude
      (fun coordinate => coordinates (Sum.inl coordinate)),
    nativeUnitCellCoordinatesAmplitude
      (fun coordinate => coordinates (Sum.inr coordinate)))

/-- The equivalence between two layers of amplitudes and functions on the thirty-two
coordinates `NativeUnitCellRunningCoordinate`. -/
def nativeTwoLayerAmplitudeCoordinateEquiv :
    NativeTwoLayerAmplitudes ≃
      (NativeUnitCellRunningCoordinate → ℂ) where
  toFun := nativeTwoLayerAmplitudeCoordinates
  invFun := nativeTwoLayerCoordinatesAmplitude
  left_inv := by
    intro amplitudes
    rcases amplitudes with ⟨previous, current⟩
    apply Prod.ext
    · exact nativeUnitCellAmplitudeCoordinateEquiv.left_inv previous
    · exact nativeUnitCellAmplitudeCoordinateEquiv.left_inv current
  right_inv := by
    intro coordinates
    funext coordinate
    cases coordinate with
    | inl inner =>
        exact congrFun
          (nativeUnitCellAmplitudeCoordinateEquiv.right_inv
            (fun coordinate => coordinates (Sum.inl coordinate))) inner
    | inr inner =>
        exact congrFun
          (nativeUnitCellAmplitudeCoordinateEquiv.right_inv
            (fun coordinate => coordinates (Sum.inr coordinate))) inner

/-- The equivalence between two layers of amplitudes and two-layer states in the eight-site
sector, applying `alignedEightSiteStateFromAmplitudes` to each layer. -/
def nativeTwoLayerAmplitudeSectorEquiv :
    NativeTwoLayerAmplitudes ≃ NativeTwoLayerSector where
  toFun amplitudes :=
    ⟨⟨alignedEightSiteStateFromAmplitudes amplitudes.1,
        alignedEightSiteStateFromAmplitudes amplitudes.2⟩,
      ⟨⟨amplitudes.1.1, amplitudes.1.2, rfl⟩,
        ⟨amplitudes.2.1, amplitudes.2.2, rfl⟩⟩⟩
  invFun layers :=
    (recoverEightSiteAmplitudes layers.1.previous,
      recoverEightSiteAmplitudes layers.1.current)
  left_inv := by
    intro amplitudes
    apply Prod.ext
    · exact recover_aligned_eight_site_amplitudes amplitudes.1
    · exact recover_aligned_eight_site_amplitudes amplitudes.2
  right_inv := by
    intro layers
    apply Subtype.ext
    apply congrArg₂ NativeTwoLayerState.mk
    · exact aligned_recovered_state_of_in_eight_site_sector
        layers.1.previous layers.2.1
    · exact aligned_recovered_state_of_in_eight_site_sector
        layers.1.current layers.2.2

/-- For nonzero `dt`, the restriction of `nativeLayersRunningEquiv` to an equivalence between
the eight-site two-layer sector and the eight-site position-velocity sector. -/
def nativeTwoLayerRunningSectorEquiv (dt : ℝ) (hdt : dt ≠ 0) :
    NativeTwoLayerSector ≃ NativeRunningSector where
  toFun layers :=
    ⟨nativePairedReadout dt layers.1,
      native_paired_readout_preserves_eight_site_sector dt layers.1
        layers.2.1 layers.2.2⟩
  invFun running :=
    ⟨rebuildNativeLayers dt running.1,
      rebuild_native_layers_preserves_eight_site_sector dt running.1
        running.2⟩
  left_inv := by
    intro layers
    apply Subtype.ext
    exact rebuild_after_native_readout dt hdt layers.1
  right_inv := by
    intro running
    apply Subtype.ext
    exact native_readout_after_rebuild dt hdt running.1

/-- For nonzero `dt`, the equivalence between the eight-site position-velocity sector and
functions on the thirty-two coordinates, through the two-layer sector and its amplitudes. -/
def nativeRunningSectorCoordinateEquiv (dt : ℝ) (hdt : dt ≠ 0) :
    NativeRunningSector ≃ (NativeUnitCellRunningCoordinate → ℂ) :=
  (nativeTwoLayerRunningSectorEquiv dt hdt).symm |>.trans
    (nativeTwoLayerAmplitudeSectorEquiv.symm.trans
      nativeTwoLayerAmplitudeCoordinateEquiv)

theorem native_running_sector_coordinate_roundtrip
    (dt : ℝ) (hdt : dt ≠ 0) (running : NativeRunningSector) :
    (nativeRunningSectorCoordinateEquiv dt hdt).symm
        (nativeRunningSectorCoordinateEquiv dt hdt running) = running :=
  (nativeRunningSectorCoordinateEquiv dt hdt).left_inv running

theorem native_coordinate_running_sector_roundtrip
    (dt : ℝ) (hdt : dt ≠ 0)
    (coordinates : NativeUnitCellRunningCoordinate → ℂ) :
    nativeRunningSectorCoordinateEquiv dt hdt
        ((nativeRunningSectorCoordinateEquiv dt hdt).symm coordinates) =
      coordinates :=
  (nativeRunningSectorCoordinateEquiv dt hdt).right_inv coordinates

theorem native_unit_cell_running_coordinate_count :
    Fintype.card NativeUnitCellRunningCoordinate = 32 := by
  exact native_unit_cell_two_layer_coordinate_count

/-- The DIRAC-007 statement bundle: `nativePairedReadout dt` and `rebuildNativeLayers dt` are
mutually inverse, both preserve the eight-site sectors, the sector coordinate equivalence
round-trips, and there are `32` coordinates. -/
structure Dirac007Certificate (dt : ℝ) (hdt : dt ≠ 0) : Prop where
  layerRoundTrip : ∀ layers : NativeTwoLayerState CubeCorner,
    rebuildNativeLayers dt (nativePairedReadout dt layers) = layers
  runningRoundTrip : ∀ running : NativeRunningState CubeCorner,
    nativePairedReadout dt (rebuildNativeLayers dt running) = running
  sectorForward : ∀ layers : NativeTwoLayerState CubeCorner,
    InEightSiteSector layers.previous →
    InEightSiteSector layers.current →
    InEightSiteRunningSector (nativePairedReadout dt layers)
  sectorBackward : ∀ running : NativeRunningState CubeCorner,
    InEightSiteRunningSector running →
    InEightSiteSector (rebuildNativeLayers dt running).previous ∧
      InEightSiteSector (rebuildNativeLayers dt running).current
  sectorCoordinateRoundTrip : ∀ running : NativeRunningSector,
    (nativeRunningSectorCoordinateEquiv dt hdt).symm
        (nativeRunningSectorCoordinateEquiv dt hdt running) = running
  coordinateSectorRoundTrip :
    ∀ coordinates : NativeUnitCellRunningCoordinate → ℂ,
      nativeRunningSectorCoordinateEquiv dt hdt
          ((nativeRunningSectorCoordinateEquiv dt hdt).symm coordinates) =
        coordinates
  runningCoordinateCount :
    Fintype.card NativeUnitCellRunningCoordinate = 32

theorem dirac007_lossless_native_paired_readout
    (dt : ℝ) (hdt : dt ≠ 0) : Dirac007Certificate dt hdt where
  layerRoundTrip := rebuild_after_native_readout dt hdt
  runningRoundTrip := native_readout_after_rebuild dt hdt
  sectorForward := native_paired_readout_preserves_eight_site_sector dt
  sectorBackward := rebuild_native_layers_preserves_eight_site_sector dt
  sectorCoordinateRoundTrip := native_running_sector_coordinate_roundtrip dt hdt
  coordinateSectorRoundTrip := native_coordinate_running_sector_roundtrip dt hdt
  runningCoordinateCount := native_unit_cell_running_coordinate_count

end
end LeanDirac
