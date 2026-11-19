/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac004.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac003Contract

/-!
This supporting module constructs the force-coordinate and centered-update
algebra used by the final DIRAC-004 discrete-action proof.  By itself it does
not claim that the update follows from stationarity; that non-circular
derivation is proved in `Dirac004DiscreteAction`.

The real and imaginary coordinate directions below are only a basis used to
reconstruct the two complex-C3 accelerations from their action variations.
They are not additional state, a spinor, or a runtime projection.  The
resulting update evolves exactly the two native fields, uses the actual C19
bond action, is time reversible, and satisfies both action-derived equations
coordinate by coordinate.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators Complex

/-- The `C3`-valued field equal to the standard basis vector `selectedComponent` at `selectedSite`
and zero elsewhere. -/
def realCoordinateDirection [DecidableEq Site]
    (selectedSite : Site) (selectedComponent : Fin 3) : Site → C3 :=
  fun site component =>
    if site = selectedSite then
      if component = selectedComponent then 1 else 0
    else 0

/-- The `C3`-valued field equal to `I` times the standard basis vector `selectedComponent` at
`selectedSite` and zero elsewhere. -/
def imagCoordinateDirection [DecidableEq Site]
    (selectedSite : Site) (selectedComponent : Fin 3) : Site → C3 :=
  fun site component =>
    if site = selectedSite then
      if component = selectedComponent then I else 0
    else 0

/-- The `psi` acceleration field whose real and imaginary parts at each site and component are the
values of `psiEulerLagrangeForce` on `realCoordinateDirection` and `imagCoordinateDirection`
there. -/
def psiAcceleration [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site) : Site → C3 :=
  fun site component =>
    (psiEulerLagrangeForce chi0 state bond
      (realCoordinateDirection site component) : ℂ) +
    (psiEulerLagrangeForce chi0 state bond
      (imagCoordinateDirection site component) : ℂ) * I

/-- The `chi` acceleration field whose real and imaginary parts at each site and component are the
values of `chiEulerLagrangeForce` on `realCoordinateDirection` and `imagCoordinateDirection` there,
divided by `B`. -/
def chiAcceleration [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site) : Site → C3 :=
  fun site component =>
    ((chiEulerLagrangeForce chi0 state bond
      (realCoordinateDirection site component) / B : ℝ) : ℂ) +
    ((chiEulerLagrangeForce chi0 state bond
      (imagCoordinateDirection site component) / B : ℝ) : ℂ) * I

/-- The pair of fields `psiAcceleration` and `chiAcceleration`, packaged as a `Velocity`. -/
def accelerationVelocity [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site) : Velocity Site where
  psiDot := psiAcceleration chi0 state bond
  chiDot := chiAcceleration chi0 B state bond

theorem psi_acceleration_real_coordinate
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (site : Site) (component : Fin 3) :
    psiMomentumPair (accelerationVelocity chi0 B state bond)
        (realCoordinateDirection site component) =
      psiEulerLagrangeForce chi0 state bond
        (realCoordinateDirection site component) := by
  classical
  unfold psiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [accelerationVelocity, psiAcceleration,
        realCoordinateDirection]
    · intro other _ hne
      simp [realCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, realCoordinateDirection, hne]
  · simp

theorem psi_acceleration_imag_coordinate
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (site : Site) (component : Fin 3) :
    psiMomentumPair (accelerationVelocity chi0 B state bond)
        (imagCoordinateDirection site component) =
      psiEulerLagrangeForce chi0 state bond
        (imagCoordinateDirection site component) := by
  classical
  unfold psiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [accelerationVelocity, psiAcceleration,
        imagCoordinateDirection]
    · intro other _ hne
      simp [imagCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, imagCoordinateDirection, hne]
  · simp

theorem chi_acceleration_real_coordinate
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (hB : B ≠ 0) (site : Site) (component : Fin 3) :
    chiMomentumPair B (accelerationVelocity chi0 B state bond)
        (realCoordinateDirection site component) =
      chiEulerLagrangeForce chi0 state bond
        (realCoordinateDirection site component) := by
  classical
  unfold chiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [accelerationVelocity, chiAcceleration,
        realCoordinateDirection]
      field_simp
    · intro other _ hne
      simp [realCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, realCoordinateDirection, hne]
  · simp

theorem chi_acceleration_imag_coordinate
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (hB : B ≠ 0) (site : Site) (component : Fin 3) :
    chiMomentumPair B (accelerationVelocity chi0 B state bond)
        (imagCoordinateDirection site component) =
      chiEulerLagrangeForce chi0 state bond
        (imagCoordinateDirection site component) := by
  classical
  unfold chiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [accelerationVelocity, chiAcceleration,
        imagCoordinateDirection]
      field_simp
    · intro other _ hne
      simp [imagCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, imagCoordinateDirection, hne]
  · simp

/-- The next state of the centered update `next = 2 * current - previous + dt ^ 2 * acceleration`,
applied to both fields with the acceleration `accelerationVelocity chi0 B current bond`. -/
def nativeNextState [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) : State Site :=
  let acceleration := accelerationVelocity chi0 B current bond
  { psi := fun site component =>
      2 * current.psi site component - previous.psi site component +
        (dt ^ 2 : ℂ) * acceleration.psiDot site component
    chi := fun site component =>
      2 * current.chi site component - previous.chi site component +
        (dt ^ 2 : ℂ) * acceleration.chiDot site component }

/-- The centered second difference `(next - 2 * current + previous) / dt ^ 2` of three states,
applied to both fields. -/
def centeredSecondDifference (dt : ℝ)
    (previous current next : State Site) : Velocity Site where
  psiDot := fun site component =>
    (next.psi site component - 2 * current.psi site component +
      previous.psi site component) / (dt ^ 2 : ℂ)
  chiDot := fun site component =>
    (next.chi site component - 2 * current.chi site component +
      previous.chi site component) / (dt ^ 2 : ℂ)

theorem native_next_is_reversible
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) :
    nativeNextState chi0 B dt bond
        (nativeNextState chi0 B dt bond previous current) current = previous := by
  apply congrArg₂ State.mk <;> funext site component <;>
    simp [nativeNextState] <;> ring

theorem centered_difference_native_next
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hdt : dt ≠ 0) :
    centeredSecondDifference dt previous current
        (nativeNextState chi0 B dt bond previous current) =
      accelerationVelocity chi0 B current bond := by
  apply congrArg₂ Velocity.mk <;> funext site component <;>
    simp [nativeNextState, accelerationVelocity] <;>
    field_simp [hdt] <;> ring

theorem native_next_psi_real_equation
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hdt : dt ≠ 0)
    (site : Site) (component : Fin 3) :
    psiMomentumPair
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (realCoordinateDirection site component) =
      psiEulerLagrangeForce chi0 current bond
        (realCoordinateDirection site component) := by
  rw [centered_difference_native_next chi0 B dt bond previous current hdt]
  exact psi_acceleration_real_coordinate chi0 B current bond site component

theorem native_next_psi_imag_equation
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hdt : dt ≠ 0)
    (site : Site) (component : Fin 3) :
    psiMomentumPair
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (imagCoordinateDirection site component) =
      psiEulerLagrangeForce chi0 current bond
        (imagCoordinateDirection site component) := by
  rw [centered_difference_native_next chi0 B dt bond previous current hdt]
  exact psi_acceleration_imag_coordinate chi0 B current bond site component

theorem native_next_chi_real_equation
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hB : B ≠ 0) (hdt : dt ≠ 0)
    (site : Site) (component : Fin 3) :
    chiMomentumPair B
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (realCoordinateDirection site component) =
      chiEulerLagrangeForce chi0 current bond
        (realCoordinateDirection site component) := by
  rw [centered_difference_native_next chi0 B dt bond previous current hdt]
  exact chi_acceleration_real_coordinate chi0 B current bond hB site component

theorem native_next_chi_imag_equation
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hB : B ≠ 0) (hdt : dt ≠ 0)
    (site : Site) (component : Fin 3) :
    chiMomentumPair B
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (imagCoordinateDirection site component) =
      chiEulerLagrangeForce chi0 current bond
        (imagCoordinateDirection site component) := by
  rw [centered_difference_native_next chi0 B dt bond previous current hdt]
  exact chi_acceleration_imag_coordinate chi0 B current bond hB site component

/-- The properties of `nativeNextState` for the given data: time reversibility, agreement of its
centered second difference with `accelerationVelocity`, and the four coordinate equations against
`psiEulerLagrangeForce` and `chiEulerLagrangeForce`. -/
structure NativeUpdateCertificate
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) : Prop where
  reversible :
    nativeNextState chi0 B dt bond
        (nativeNextState chi0 B dt bond previous current) current = previous
  centeredEquation :
    centeredSecondDifference dt previous current
        (nativeNextState chi0 B dt bond previous current) =
      accelerationVelocity chi0 B current bond
  psiRealEquation : ∀ site component,
    psiMomentumPair
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (realCoordinateDirection site component) =
      psiEulerLagrangeForce chi0 current bond
        (realCoordinateDirection site component)
  psiImagEquation : ∀ site component,
    psiMomentumPair
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (imagCoordinateDirection site component) =
      psiEulerLagrangeForce chi0 current bond
        (imagCoordinateDirection site component)
  chiRealEquation : ∀ site component,
    chiMomentumPair B
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (realCoordinateDirection site component) =
      chiEulerLagrangeForce chi0 current bond
        (realCoordinateDirection site component)
  chiImagEquation : ∀ site component,
    chiMomentumPair B
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current))
        (imagCoordinateDirection site component) =
      chiEulerLagrangeForce chi0 current bond
        (imagCoordinateDirection site component)

theorem dirac004_c19_reversible_action_update
    [Fintype Site] [DecidableEq Site]
    (dt : ℝ) (geometry : C19Lattice Site)
    (previous current : State Site) (hdt : dt ≠ 0) :
    NativeUpdateCertificate chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current := by
  have hB : chiKineticNormalization ≠ 0 := by
    rw [chi_kinetic_normalization_eq_1197]
    norm_num
  constructor
  · exact native_next_is_reversible chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current
  · exact centered_difference_native_next chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current hdt
  · intro site component
    exact native_next_psi_real_equation chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current hdt site component
  · intro site component
    exact native_next_psi_imag_equation chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current hdt site component
  · intro site component
    exact native_next_chi_real_equation chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current hB hdt site component
  · intro site component
    exact native_next_chi_imag_equation chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current hB hdt site component

end
end LeanDirac
