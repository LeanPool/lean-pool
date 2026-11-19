/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac004DiscreteAction.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac004

/-!
This module closes the DIRAC-004 derivation boundary without defining the
equations as the desired recurrence.  It constructs the two-step discrete
action directly from the frozen kinetic energy and potential, differentiates
that action under arbitrary combined complex-C3 field variations, and proves
that stationarity is equivalent to the native centered update.  The proof also
upgrades the coordinate probes in `Dirac004` to all field directions.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators Complex

def stateDifferenceVelocity (dt : ℝ) (left right : State Site) : Velocity Site where
  psiDot := fun site component =>
    (right.psi site component - left.psi site component) / (dt : ℂ)
  chiDot := fun site component =>
    (right.chi site component - left.chi site component) / (dt : ℂ)

def stateDirectionVelocity (dt : ℝ) (direction : State Site) : Velocity Site where
  psiDot := fun site component => direction.psi site component / (dt : ℂ)
  chiDot := fun site component => direction.chi site component / (dt : ℂ)

theorem difference_velocity_vary_right (dt : ℝ)
    (left right direction : State Site) (eps : ℝ) :
    stateDifferenceVelocity dt left (stateLine right direction eps) =
      velocityLine (stateDifferenceVelocity dt left right)
        (stateDirectionVelocity dt direction) eps := by
  apply congrArg₂ Velocity.mk <;> funext site component <;>
    simp [stateDifferenceVelocity, stateDirectionVelocity,
      stateLine, c3Line, c3Add, c3ScaleReal] <;> ring

theorem difference_velocity_vary_left (dt : ℝ)
    (left right direction : State Site) (eps : ℝ) :
    stateDifferenceVelocity dt (stateLine left direction eps) right =
      velocityLine (stateDifferenceVelocity dt left right)
        (stateDirectionVelocity (-dt) direction) eps := by
  apply congrArg₂ Velocity.mk <;> funext site component <;>
    simp [stateDifferenceVelocity, stateDirectionVelocity,
      stateLine, c3Line, c3Add, c3ScaleReal] <;> ring

def discreteLagrangian [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (left right : State Site)
    (bond : Edge → Bond Site) : ℝ :=
  dt * (kinetic B (stateDifferenceVelocity dt left right) -
    potential chi0 left bond)

def discreteTwoStepAction [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (previous current next : State Site)
    (bond : Edge → Bond Site) : ℝ :=
  discreteLagrangian chi0 B dt previous current bond +
    discreteLagrangian chi0 B dt current next bond

def discreteActionFirstVariation [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (previous current next direction : State Site)
    (bond : Edge → Bond Site) : ℝ :=
  dt * (kineticVelocityFirstVariation B
        (stateDifferenceVelocity dt previous current)
        (stateDirectionVelocity dt direction) +
      kineticVelocityFirstVariation B
        (stateDifferenceVelocity dt current next)
        (stateDirectionVelocity (-dt) direction) +
      lagrangianStateFirstVariation chi0 current direction bond)

theorem discrete_action_hasDerivAt [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (previous current next direction : State Site)
    (bond : Edge → Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => discreteTwoStepAction chi0 B dt previous
        (stateLine current direction eps) next bond)
      (discreteActionFirstVariation chi0 B dt previous current next direction bond) 0 := by
  have hleft := kinetic_velocity_hasDerivAt B
    (stateDifferenceVelocity dt previous current)
    (stateDirectionVelocity dt direction)
  have hright := kinetic_velocity_hasDerivAt B
    (stateDifferenceVelocity dt current next)
    (stateDirectionVelocity (-dt) direction)
  have hpotential := potential_hasDerivAt chi0 current direction bond
  have hnormalized := hleft.add hright |>.sub hpotential
  have hscaled := HasDerivAt.const_mul dt hnormalized
  have hboundary := hasDerivAt_const (𝕜 := ℝ) 0
    (dt * potential chi0 previous bond)
  have h := hscaled.sub hboundary
  convert h using 1
  · funext eps
    simp only [discreteTwoStepAction, discreteLagrangian,
      Pi.add_apply, Pi.sub_apply]
    rw [difference_velocity_vary_right, difference_velocity_vary_left]
    ring
  · simp only [discreteActionFirstVariation, lagrangianStateFirstVariation, sub_zero,
        mul_eq_mul_left_iff]
    left
    trivial

def addC3Field (eta zeta : Site → C3) : Site → C3 :=
  fun site component => eta site component + zeta site component

def addStateDirection (direction other : State Site) : State Site where
  psi := addC3Field direction.psi other.psi
  chi := addC3Field direction.chi other.chi

theorem c3_real_pair_add_right (u v z : C3) :
    c3RealPair u (fun component => v component + z component) =
      c3RealPair u v + c3RealPair u z := by
  unfold c3RealPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro component _
  simp
  ring

theorem wedge_first_variation_add (state direction other : State Site)
    (site : Site) :
    wedgeFirstVariation state (addStateDirection direction other) site =
      fun component =>
        wedgeFirstVariation state direction site component +
          wedgeFirstVariation state other site component := by
  funext component
  fin_cases component <;>
    simp [wedgeFirstVariation, addStateDirection, addC3Field,
      c3Add, wedge] <;> ring

theorem bond_area_first_variation_add (state direction other : State Site)
    (edge : Bond Site) :
    bondAreaFirstVariation state (addStateDirection direction other) edge =
      fun component =>
        bondAreaFirstVariation state direction edge component +
          bondAreaFirstVariation state other edge component := by
  funext component
  simp [bondAreaFirstVariation, difference, wedge_first_variation_add]
  ring

theorem exterior_area_first_variation_add (chi0 : ℝ)
    (state direction other : State Site) (edge : Bond Site) :
    exteriorAreaBondFirstVariation chi0 state
        (addStateDirection direction other) edge =
      exteriorAreaBondFirstVariation chi0 state direction edge +
        exteriorAreaBondFirstVariation chi0 state other edge := by
  simp [exteriorAreaBondFirstVariation, bond_area_first_variation_add,
    c3_real_pair_add_right]
  ring

theorem site_potential_first_variation_add (chi0 : ℝ)
    (state direction other : State Site) (site : Site) :
    sitePotentialFirstVariation chi0 state
        (addStateDirection direction other) site =
      sitePotentialFirstVariation chi0 state direction site +
        sitePotentialFirstVariation chi0 state other site := by
  have hChi := c3_real_pair_add_right (state.chi site)
    (direction.chi site) (other.chi site)
  have hPsi := c3_real_pair_add_right (state.psi site)
    (direction.psi site) (other.psi site)
  change c3RealPair (state.chi site)
      (fun component => direction.chi site component + other.chi site component) =
        _ at hChi
  change c3RealPair (state.psi site)
      (fun component => direction.psi site component + other.psi site component) =
        _ at hPsi
  unfold sitePotentialFirstVariation
  dsimp [addStateDirection, addC3Field]
  rw [show addC3Field direction.chi other.chi site =
      (fun component => direction.chi site component +
        other.chi site component) by rfl]
  rw [show addC3Field direction.psi other.psi site =
      (fun component => direction.psi site component +
        other.psi site component) by rfl]
  rw [hChi, hPsi]
  ring

theorem potential_first_variation_add [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state direction other : State Site)
    (bond : Edge → Bond Site) :
    potentialFirstVariation chi0 state (addStateDirection direction other) bond =
      potentialFirstVariation chi0 state direction bond +
        potentialFirstVariation chi0 state other bond := by
  simp [potentialFirstVariation, site_potential_first_variation_add,
    exterior_area_first_variation_add, Finset.sum_add_distrib]
  ring

theorem psi_force_add [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (eta zeta : Site → C3) :
    psiEulerLagrangeForce chi0 state bond (addC3Field eta zeta) =
      psiEulerLagrangeForce chi0 state bond eta +
        psiEulerLagrangeForce chi0 state bond zeta := by
  change lagrangianStateFirstVariation chi0 state
      (purePsiDirection (addC3Field eta zeta)) bond = _
  rw [show purePsiDirection (addC3Field eta zeta) =
      addStateDirection (purePsiDirection eta) (purePsiDirection zeta) by
        apply congrArg₂ State.mk <;> funext site component <;>
          simp [purePsiDirection, addC3Field, c3Zero]]
  simp [lagrangianStateFirstVariation, potential_first_variation_add,
    psiEulerLagrangeForce]
  ring

theorem chi_force_add [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (eta zeta : Site → C3) :
    chiEulerLagrangeForce chi0 state bond (addC3Field eta zeta) =
      chiEulerLagrangeForce chi0 state bond eta +
        chiEulerLagrangeForce chi0 state bond zeta := by
  change lagrangianStateFirstVariation chi0 state
      (pureChiDirection (addC3Field eta zeta)) bond = _
  rw [show pureChiDirection (addC3Field eta zeta) =
      addStateDirection (pureChiDirection eta) (pureChiDirection zeta) by
        apply congrArg₂ State.mk <;> funext site component <;>
          simp [pureChiDirection, addC3Field, c3Zero]]
  simp [lagrangianStateFirstVariation, potential_first_variation_add,
    chiEulerLagrangeForce]
  ring

def coordinateTerm [DecidableEq Site] (eta : Site → C3)
    (site : Site) (component : Fin 3) : Site → C3 :=
  addC3Field
    (scaleC3Field (eta site component).re
      (realCoordinateDirection site component))
    (scaleC3Field (eta site component).im
      (imagCoordinateDirection site component))

def coordinateExpansion [Fintype Site] [DecidableEq Site]
    (eta : Site → C3) : Site → C3 :=
  ∑ site, ∑ component, coordinateTerm eta site component

theorem coordinate_expansion_exact [Fintype Site] [DecidableEq Site]
    (eta : Site → C3) : coordinateExpansion eta = eta := by
  classical
  funext site component
  unfold coordinateExpansion
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single site]
  · rw [Finset.sum_eq_single component]
    · simp [coordinateTerm, addC3Field, scaleC3Field, c3ScaleReal,
        realCoordinateDirection, imagCoordinateDirection]
    · intro other _ hne
      simp [coordinateTerm, addC3Field, scaleC3Field, c3ScaleReal,
        realCoordinateDirection, imagCoordinateDirection, Ne.symm hne]
    · simp
  · intro other _ hne
    simp [coordinateTerm, addC3Field, scaleC3Field, c3ScaleReal,
      realCoordinateDirection, imagCoordinateDirection, Ne.symm hne]
  · simp

theorem psi_momentum_add [Fintype Site] (velocity : Velocity Site)
    (eta zeta : Site → C3) :
    psiMomentumPair velocity (addC3Field eta zeta) =
      psiMomentumPair velocity eta + psiMomentumPair velocity zeta := by
  unfold psiMomentumPair
  calc
    (∑ site, c3RealPair (velocity.psiDot site) (addC3Field eta zeta site)) =
        ∑ site, (c3RealPair (velocity.psiDot site) (eta site) +
          c3RealPair (velocity.psiDot site) (zeta site)) := by
            apply Finset.sum_congr rfl
            intro site _
            rw [show addC3Field eta zeta site =
              (fun component => eta site component + zeta site component) by rfl]
            exact c3_real_pair_add_right _ _ _
    _ = _ := Finset.sum_add_distrib

theorem chi_momentum_add [Fintype Site] (B : ℝ) (velocity : Velocity Site)
    (eta zeta : Site → C3) :
    chiMomentumPair B velocity (addC3Field eta zeta) =
      chiMomentumPair B velocity eta + chiMomentumPair B velocity zeta := by
  unfold chiMomentumPair
  rw [show (∑ site, c3RealPair (velocity.chiDot site)
      (addC3Field eta zeta site)) =
      (∑ site, c3RealPair (velocity.chiDot site) (eta site)) +
        ∑ site, c3RealPair (velocity.chiDot site) (zeta site) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro site _
    rw [show addC3Field eta zeta site =
      (fun component => eta site component + zeta site component) by rfl]
    exact c3_real_pair_add_right _ _ _]
  ring

theorem psi_force_zero [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site) :
    psiEulerLagrangeForce chi0 state bond (0 : Site → C3) = 0 := by
  have h := psi_force_scale chi0 0 state bond (0 : Site → C3)
  have hz : scaleC3Field 0 (0 : Site → C3) = (0 : Site → C3) := by
    funext site component
    simp [scaleC3Field, c3ScaleReal]
  rw [hz] at h
  simpa using h

theorem chi_force_zero [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site) :
    chiEulerLagrangeForce chi0 state bond (0 : Site → C3) = 0 := by
  have h := chi_force_scale chi0 0 state bond (0 : Site → C3)
  have hz : scaleC3Field 0 (0 : Site → C3) = (0 : Site → C3) := by
    funext site component
    simp [scaleC3Field, c3ScaleReal]
  rw [hz] at h
  simpa using h

theorem psi_force_finset_sum [Fintype Site] [Fintype Edge]
    {Index : Type} (chi0 : ℝ) (state : State Site)
    (bond : Edge → Bond Site) (terms : Index → Site → C3)
    (indices : Finset Index) :
    psiEulerLagrangeForce chi0 state bond (∑ index ∈ indices, terms index) =
      ∑ index ∈ indices, psiEulerLagrangeForce chi0 state bond (terms index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using psi_force_zero chi0 state bond
  | @insert index indices hnot ih =>
      rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
      rw [show (terms index + ∑ x ∈ indices, terms x) =
          addC3Field (terms index) (∑ x ∈ indices, terms x) by rfl]
      rw [psi_force_add, ih]

theorem chi_force_finset_sum [Fintype Site] [Fintype Edge]
    {Index : Type} (chi0 : ℝ) (state : State Site)
    (bond : Edge → Bond Site) (terms : Index → Site → C3)
    (indices : Finset Index) :
    chiEulerLagrangeForce chi0 state bond (∑ index ∈ indices, terms index) =
      ∑ index ∈ indices, chiEulerLagrangeForce chi0 state bond (terms index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using chi_force_zero chi0 state bond
  | @insert index indices hnot ih =>
      rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
      rw [show (terms index + ∑ x ∈ indices, terms x) =
          addC3Field (terms index) (∑ x ∈ indices, terms x) by rfl]
      rw [chi_force_add, ih]

theorem psi_momentum_zero [Fintype Site] (velocity : Velocity Site) :
    psiMomentumPair velocity (0 : Site → C3) = 0 := by
  simp [psiMomentumPair, c3RealPair]

theorem chi_momentum_zero [Fintype Site] (B : ℝ) (velocity : Velocity Site) :
    chiMomentumPair B velocity (0 : Site → C3) = 0 := by
  simp [chiMomentumPair, c3RealPair]

theorem psi_momentum_finset_sum [Fintype Site]
    {Index : Type} (velocity : Velocity Site)
    (terms : Index → Site → C3) (indices : Finset Index) :
    psiMomentumPair velocity (∑ index ∈ indices, terms index) =
      ∑ index ∈ indices, psiMomentumPair velocity (terms index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using psi_momentum_zero velocity
  | @insert index indices hnot ih =>
      rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
      rw [show (terms index + ∑ x ∈ indices, terms x) =
          addC3Field (terms index) (∑ x ∈ indices, terms x) by rfl]
      rw [psi_momentum_add, ih]

theorem chi_momentum_finset_sum [Fintype Site]
    {Index : Type} (B : ℝ) (velocity : Velocity Site)
    (terms : Index → Site → C3) (indices : Finset Index) :
    chiMomentumPair B velocity (∑ index ∈ indices, terms index) =
      ∑ index ∈ indices, chiMomentumPair B velocity (terms index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using chi_momentum_zero B velocity
  | @insert index indices hnot ih =>
      rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
      rw [show (terms index + ∑ x ∈ indices, terms x) =
          addC3Field (terms index) (∑ x ∈ indices, terms x) by rfl]
      rw [chi_momentum_add, ih]

theorem psi_acceleration_coordinate_term
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (eta : Site → C3) (site : Site) (component : Fin 3) :
    psiMomentumPair (accelerationVelocity chi0 B state bond)
        (coordinateTerm eta site component) =
      psiEulerLagrangeForce chi0 state bond
        (coordinateTerm eta site component) := by
  unfold coordinateTerm
  rw [psi_momentum_add, psi_momentum_scale, psi_momentum_scale]
  rw [psi_acceleration_real_coordinate, psi_acceleration_imag_coordinate]
  rw [psi_force_add, psi_force_scale, psi_force_scale]

theorem chi_acceleration_coordinate_term
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (hB : B ≠ 0) (eta : Site → C3) (site : Site) (component : Fin 3) :
    chiMomentumPair B (accelerationVelocity chi0 B state bond)
        (coordinateTerm eta site component) =
      chiEulerLagrangeForce chi0 state bond
        (coordinateTerm eta site component) := by
  unfold coordinateTerm
  rw [chi_momentum_add, chi_momentum_scale, chi_momentum_scale]
  rw [chi_acceleration_real_coordinate, chi_acceleration_imag_coordinate]
  · rw [chi_force_add, chi_force_scale, chi_force_scale]
  · exact hB
  · exact hB

theorem psi_acceleration_all_directions
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (eta : Site → C3) :
    psiMomentumPair (accelerationVelocity chi0 B state bond) eta =
      psiEulerLagrangeForce chi0 state bond eta := by
  classical
  rw [← coordinate_expansion_exact eta]
  unfold coordinateExpansion
  rw [psi_momentum_finset_sum
      (accelerationVelocity chi0 B state bond)
      (fun site => ∑ component, coordinateTerm eta site component)
      Finset.univ]
  rw [psi_force_finset_sum chi0 state bond
      (fun site => ∑ component, coordinateTerm eta site component)
      Finset.univ]
  apply Finset.sum_congr rfl
  intro site _
  rw [psi_momentum_finset_sum
      (accelerationVelocity chi0 B state bond)
      (coordinateTerm eta site) Finset.univ]
  rw [psi_force_finset_sum chi0 state bond
      (coordinateTerm eta site) Finset.univ]
  apply Finset.sum_congr rfl
  intro component _
  exact psi_acceleration_coordinate_term chi0 B state bond eta site component

theorem chi_acceleration_all_directions
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (hB : B ≠ 0) (eta : Site → C3) :
    chiMomentumPair B (accelerationVelocity chi0 B state bond) eta =
      chiEulerLagrangeForce chi0 state bond eta := by
  classical
  rw [← coordinate_expansion_exact eta]
  unfold coordinateExpansion
  rw [chi_momentum_finset_sum B
      (accelerationVelocity chi0 B state bond)
      (fun site => ∑ component, coordinateTerm eta site component)
      Finset.univ]
  rw [chi_force_finset_sum chi0 state bond
      (fun site => ∑ component, coordinateTerm eta site component)
      Finset.univ]
  apply Finset.sum_congr rfl
  intro site _
  rw [chi_momentum_finset_sum B
      (accelerationVelocity chi0 B state bond)
      (coordinateTerm eta site) Finset.univ]
  rw [chi_force_finset_sum chi0 state bond
      (coordinateTerm eta site) Finset.univ]
  apply Finset.sum_congr rfl
  intro component _
  exact chi_acceleration_coordinate_term chi0 B state bond hB eta site component

def addVelocity (velocity other : Velocity Site) : Velocity Site where
  psiDot := addC3Field velocity.psiDot other.psiDot
  chiDot := addC3Field velocity.chiDot other.chiDot

def scaleVelocity (a : ℝ) (velocity : Velocity Site) : Velocity Site where
  psiDot := scaleC3Field a velocity.psiDot
  chiDot := scaleC3Field a velocity.chiDot

theorem c3_real_pair_scale_left (a : ℝ) (u v : C3) :
    c3RealPair (c3ScaleReal a u) v = a * c3RealPair u v := by
  simp only [c3RealPair, c3ScaleReal, RCLike.star_def, mul_re, ofReal_re, ofReal_im, zero_mul,
      sub_zero, conj_re, mul_im, add_zero, conj_im, mul_neg, sub_neg_eq_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  ring

theorem c3_real_pair_add_left (u v z : C3) :
    c3RealPair (fun component => u component + v component) z =
      c3RealPair u z + c3RealPair v z := by
  unfold c3RealPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro component _
  simp
  ring

theorem psi_momentum_velocity_add [Fintype Site]
    (velocity other : Velocity Site) (eta : Site → C3) :
    psiMomentumPair (addVelocity velocity other) eta =
      psiMomentumPair velocity eta + psiMomentumPair other eta := by
  unfold psiMomentumPair addVelocity addC3Field
  simp_rw [c3_real_pair_add_left]
  rw [Finset.sum_add_distrib]

theorem chi_momentum_velocity_add [Fintype Site]
    (B : ℝ) (velocity other : Velocity Site) (eta : Site → C3) :
    chiMomentumPair B (addVelocity velocity other) eta =
      chiMomentumPair B velocity eta + chiMomentumPair B other eta := by
  unfold chiMomentumPair addVelocity addC3Field
  simp_rw [c3_real_pair_add_left]
  rw [Finset.sum_add_distrib]
  ring

theorem psi_momentum_velocity_scale [Fintype Site]
    (a : ℝ) (velocity : Velocity Site) (eta : Site → C3) :
    psiMomentumPair (scaleVelocity a velocity) eta =
      a * psiMomentumPair velocity eta := by
  unfold psiMomentumPair scaleVelocity scaleC3Field
  simp_rw [c3_real_pair_scale_left]
  rw [← Finset.mul_sum]

theorem chi_momentum_velocity_scale [Fintype Site]
    (B a : ℝ) (velocity : Velocity Site) (eta : Site → C3) :
    chiMomentumPair B (scaleVelocity a velocity) eta =
      a * chiMomentumPair B velocity eta := by
  unfold chiMomentumPair scaleVelocity scaleC3Field
  simp_rw [c3_real_pair_scale_left]
  rw [← Finset.mul_sum]
  ring

theorem centered_difference_as_velocity_difference (dt : ℝ)
    (previous current next : State Site) (hdt : dt ≠ 0) :
    centeredSecondDifference dt previous current next =
      scaleVelocity (1 / dt)
        (addVelocity (stateDifferenceVelocity dt current next)
          (scaleVelocity (-1) (stateDifferenceVelocity dt previous current))) := by
  apply congrArg₂ Velocity.mk <;> funext site component <;>
    simp [scaleVelocity, addVelocity,
      stateDifferenceVelocity, scaleC3Field, addC3Field, c3ScaleReal] <;>
    field_simp [hdt] <;> ring

theorem state_direction_velocity_pure_psi (dt : ℝ) (eta : Site → C3) :
    stateDirectionVelocity dt (purePsiDirection eta) =
      purePsiVelocity (scaleC3Field (1 / dt) eta) := by
  apply congrArg₂ Velocity.mk <;> funext site component
  · simp [purePsiDirection, scaleC3Field, c3ScaleReal]
    ring
  · simp [purePsiDirection, c3Zero]

theorem state_direction_velocity_pure_chi (dt : ℝ) (eta : Site → C3) :
    stateDirectionVelocity dt (pureChiDirection eta) =
      pureChiVelocity (scaleC3Field (1 / dt) eta) := by
  apply congrArg₂ Velocity.mk <;> funext site component
  · simp [pureChiDirection, c3Zero]
  · simp [pureChiDirection, scaleC3Field, c3ScaleReal]
    ring

theorem discrete_psi_variation_eq_residual
    [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (previous current next : State Site)
    (bond : Edge → Bond Site) (hdt : dt ≠ 0) (eta : Site → C3) :
    discreteActionFirstVariation chi0 B dt previous current next
        (purePsiDirection eta) bond =
      dt * (psiEulerLagrangeForce chi0 current bond eta -
        psiMomentumPair (centeredSecondDifference dt previous current next) eta) := by
  unfold discreteActionFirstVariation kineticVelocityFirstVariation
  rw [state_direction_velocity_pure_psi, state_direction_velocity_pure_psi]
  simp only [purePsiVelocity, one_div, chiMomentumPair, c3RealPair, c3Zero, star_zero, mul_zero,
      zero_re, Finset.sum_const_zero, add_zero, inv_neg, mul_eq_mul_left_iff]
  rw [psi_momentum_scale, psi_momentum_scale]
  rw [centered_difference_as_velocity_difference dt previous current next hdt]
  rw [psi_momentum_velocity_scale, psi_momentum_velocity_add,
    psi_momentum_velocity_scale]
  simp [lagrangianStateFirstVariation, psiEulerLagrangeForce]
  field_simp [hdt]; ring_nf; simp

theorem discrete_chi_variation_eq_residual
    [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (previous current next : State Site)
    (bond : Edge → Bond Site) (hdt : dt ≠ 0) (eta : Site → C3) :
    discreteActionFirstVariation chi0 B dt previous current next
        (pureChiDirection eta) bond =
      dt * (chiEulerLagrangeForce chi0 current bond eta -
        chiMomentumPair B
          (centeredSecondDifference dt previous current next) eta) := by
  unfold discreteActionFirstVariation kineticVelocityFirstVariation
  rw [state_direction_velocity_pure_chi, state_direction_velocity_pure_chi]
  simp only [psiMomentumPair, c3RealPair, pureChiVelocity, one_div, c3Zero, star_zero, mul_zero,
      zero_re, Finset.sum_const_zero, zero_add, inv_neg, mul_eq_mul_left_iff]
  rw [chi_momentum_scale, chi_momentum_scale]
  rw [centered_difference_as_velocity_difference dt previous current next hdt]
  rw [chi_momentum_velocity_scale, chi_momentum_velocity_add,
    chi_momentum_velocity_scale]
  simp [lagrangianStateFirstVariation, chiEulerLagrangeForce]
  field_simp [hdt]; ring_nf; simp

theorem native_next_discrete_psi_variation_zero
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hdt : dt ≠ 0)
    (eta : Site → C3) :
    discreteActionFirstVariation chi0 B dt previous current
        (nativeNextState chi0 B dt bond previous current)
        (purePsiDirection eta) bond = 0 := by
  rw [discrete_psi_variation_eq_residual chi0 B dt previous current
    (nativeNextState chi0 B dt bond previous current) bond hdt eta]
  rw [centered_difference_native_next chi0 B dt bond previous current hdt]
  rw [psi_acceleration_all_directions]
  ring

theorem native_next_discrete_chi_variation_zero
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hB : B ≠ 0) (hdt : dt ≠ 0)
    (eta : Site → C3) :
    discreteActionFirstVariation chi0 B dt previous current
        (nativeNextState chi0 B dt bond previous current)
        (pureChiDirection eta) bond = 0 := by
  rw [discrete_chi_variation_eq_residual chi0 B dt previous current
    (nativeNextState chi0 B dt bond previous current) bond hdt eta]
  rw [centered_difference_native_next chi0 B dt bond previous current hdt]
  rw [chi_acceleration_all_directions chi0 B current bond hB eta]
  ring

theorem state_direction_velocity_add (dt : ℝ)
    (direction other : State Site) :
    stateDirectionVelocity dt (addStateDirection direction other) =
      addVelocity (stateDirectionVelocity dt direction)
        (stateDirectionVelocity dt other) := by
  apply congrArg₂ Velocity.mk <;> funext site component <;>
    simp [stateDirectionVelocity, addStateDirection,
      addC3Field] <;> ring

theorem kinetic_first_variation_add [Fintype Site] (B : ℝ)
    (velocity direction other : Velocity Site) :
    kineticVelocityFirstVariation B velocity (addVelocity direction other) =
      kineticVelocityFirstVariation B velocity direction +
        kineticVelocityFirstVariation B velocity other := by
  unfold kineticVelocityFirstVariation addVelocity
  rw [show (addC3Field direction.psiDot other.psiDot) =
      addC3Field direction.psiDot other.psiDot by rfl]
  rw [psi_momentum_add, chi_momentum_add]
  ring

theorem discrete_first_variation_add
    [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (previous current next direction other : State Site)
    (bond : Edge → Bond Site) :
    discreteActionFirstVariation chi0 B dt previous current next
        (addStateDirection direction other) bond =
      discreteActionFirstVariation chi0 B dt previous current next direction bond +
        discreteActionFirstVariation chi0 B dt previous current next other bond := by
  unfold discreteActionFirstVariation
  rw [state_direction_velocity_add, state_direction_velocity_add]
  rw [kinetic_first_variation_add, kinetic_first_variation_add]
  simp [lagrangianStateFirstVariation, potential_first_variation_add]
  ring

theorem state_direction_psi_chi_decomposition (direction : State Site) :
    direction = addStateDirection
      (purePsiDirection direction.psi) (pureChiDirection direction.chi) := by
  apply congrArg₂ State.mk <;> funext site component <;>
    simp [addC3Field, purePsiDirection,
      pureChiDirection, c3Zero]

def IsDiscreteActionStationary [Fintype Site] [Fintype Edge]
    (chi0 B dt : ℝ) (previous current next : State Site)
    (bond : Edge → Bond Site) : Prop :=
  ∀ direction : State Site,
    AnalyticHasDerivAt
      (fun eps : ℝ => discreteTwoStepAction chi0 B dt previous
        (stateLine current direction eps) next bond) 0 0

theorem native_next_is_discrete_action_stationary
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) (hB : B ≠ 0) (hdt : dt ≠ 0) :
    IsDiscreteActionStationary chi0 B dt previous current
      (nativeNextState chi0 B dt bond previous current) bond := by
  intro direction
  have hderiv := discrete_action_hasDerivAt chi0 B dt previous current
    (nativeNextState chi0 B dt bond previous current) direction bond
  have hdecomp := state_direction_psi_chi_decomposition direction
  have hzero : discreteActionFirstVariation chi0 B dt previous current
      (nativeNextState chi0 B dt bond previous current) direction bond = 0 := by
    rw [hdecomp, discrete_first_variation_add]
    rw [native_next_discrete_psi_variation_zero chi0 B dt bond
      previous current hdt direction.psi]
    rw [native_next_discrete_chi_variation_zero chi0 B dt bond
      previous current hB hdt direction.chi]
    ring
  rw [hzero] at hderiv
  exact hderiv

theorem psi_momentum_real_coordinate_value
    [Fintype Site] [DecidableEq Site]
    (velocity : Velocity Site) (site : Site) (component : Fin 3) :
    psiMomentumPair velocity (realCoordinateDirection site component) =
      (velocity.psiDot site component).re := by
  classical
  unfold psiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [realCoordinateDirection]
    · intro other _ hne
      simp [realCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, realCoordinateDirection, hne]
  · simp

theorem psi_momentum_imag_coordinate_value
    [Fintype Site] [DecidableEq Site]
    (velocity : Velocity Site) (site : Site) (component : Fin 3) :
    psiMomentumPair velocity (imagCoordinateDirection site component) =
      (velocity.psiDot site component).im := by
  classical
  unfold psiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [imagCoordinateDirection]
    · intro other _ hne
      simp [imagCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, imagCoordinateDirection, hne]
  · simp

theorem chi_momentum_real_coordinate_value
    [Fintype Site] [DecidableEq Site]
    (B : ℝ) (velocity : Velocity Site) (site : Site) (component : Fin 3) :
    chiMomentumPair B velocity (realCoordinateDirection site component) =
      B * (velocity.chiDot site component).re := by
  classical
  unfold chiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [realCoordinateDirection]
    · intro other _ hne
      simp [realCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, realCoordinateDirection, hne]
  · simp

theorem chi_momentum_imag_coordinate_value
    [Fintype Site] [DecidableEq Site]
    (B : ℝ) (velocity : Velocity Site) (site : Site) (component : Fin 3) :
    chiMomentumPair B velocity (imagCoordinateDirection site component) =
      B * (velocity.chiDot site component).im := by
  classical
  unfold chiMomentumPair
  rw [Finset.sum_eq_single site]
  · unfold c3RealPair
    rw [Finset.sum_eq_single component]
    · simp [imagCoordinateDirection]
    · intro other _ hne
      simp [imagCoordinateDirection, hne]
    · simp
  · intro other _ hne
    simp [c3RealPair, imagCoordinateDirection, hne]
  · simp

theorem coordinate_equations_determine_acceleration
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (velocity : Velocity Site) (hB : B ≠ 0)
    (hPsiReal : ∀ site component,
      psiMomentumPair velocity (realCoordinateDirection site component) =
        psiEulerLagrangeForce chi0 state bond
          (realCoordinateDirection site component))
    (hPsiImag : ∀ site component,
      psiMomentumPair velocity (imagCoordinateDirection site component) =
        psiEulerLagrangeForce chi0 state bond
          (imagCoordinateDirection site component))
    (hChiReal : ∀ site component,
      chiMomentumPair B velocity (realCoordinateDirection site component) =
        chiEulerLagrangeForce chi0 state bond
          (realCoordinateDirection site component))
    (hChiImag : ∀ site component,
      chiMomentumPair B velocity (imagCoordinateDirection site component) =
        chiEulerLagrangeForce chi0 state bond
          (imagCoordinateDirection site component)) :
    velocity = accelerationVelocity chi0 B state bond := by
  apply congrArg₂ Velocity.mk
  · funext site component
    apply Complex.ext
    · rw [← psi_momentum_real_coordinate_value velocity site component]
      rw [hPsiReal]
      rw [← psi_acceleration_real_coordinate chi0 B state bond site component]
      exact psi_momentum_real_coordinate_value
        (accelerationVelocity chi0 B state bond) site component
    · rw [← psi_momentum_imag_coordinate_value velocity site component]
      rw [hPsiImag]
      rw [← psi_acceleration_imag_coordinate chi0 B state bond site component]
      exact psi_momentum_imag_coordinate_value
        (accelerationVelocity chi0 B state bond) site component
  · funext site component
    apply Complex.ext
    · have h := hChiReal site component
      rw [chi_momentum_real_coordinate_value] at h
      have ha := chi_acceleration_real_coordinate
        chi0 B state bond hB site component
      rw [chi_momentum_real_coordinate_value] at ha
      exact mul_left_cancel₀ hB (h.trans ha.symm)
    · have h := hChiImag site component
      rw [chi_momentum_imag_coordinate_value] at h
      have ha := chi_acceleration_imag_coordinate
        chi0 B state bond hB site component
      rw [chi_momentum_imag_coordinate_value] at ha
      exact mul_left_cancel₀ hB (h.trans ha.symm)

theorem centered_second_difference_injective_next (dt : ℝ)
    (previous current next other : State Site) (hdt : dt ≠ 0)
    (heq : centeredSecondDifference dt previous current next =
      centeredSecondDifference dt previous current other) :
    next = other := by
  have hPsi := congrArg Velocity.psiDot heq
  have hChi := congrArg Velocity.chiDot heq
  apply congrArg₂ State.mk
  · funext site component
    have h := congrFun (congrFun hPsi site) component
    simp [centeredSecondDifference] at h
    field_simp [hdt] at h
    linear_combination h
  · funext site component
    have h := congrFun (congrFun hChi site) component
    simp [centeredSecondDifference] at h
    field_simp [hdt] at h
    linear_combination h

theorem discrete_stationarity_determines_native_next
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current next : State Site) (hB : B ≠ 0) (hdt : dt ≠ 0)
    (hstationary : IsDiscreteActionStationary chi0 B dt
      previous current next bond) :
    next = nativeNextState chi0 B dt bond previous current := by
  have hPsiReal : ∀ site component,
      psiMomentumPair (centeredSecondDifference dt previous current next)
          (realCoordinateDirection site component) =
        psiEulerLagrangeForce chi0 current bond
          (realCoordinateDirection site component) := by
    intro site component
    have hcalc := discrete_action_hasDerivAt chi0 B dt previous current next
      (purePsiDirection (realCoordinateDirection site component)) bond
    have hstat := hstationary
      (purePsiDirection (realCoordinateDirection site component))
    have hzero : discreteActionFirstVariation chi0 B dt previous current next
        (purePsiDirection (realCoordinateDirection site component)) bond = 0 :=
      hcalc.unique hstat
    rw [discrete_psi_variation_eq_residual chi0 B dt previous current next
      bond hdt] at hzero
    have hresidual := (mul_eq_zero.mp hzero).resolve_left hdt
    linarith
  have hPsiImag : ∀ site component,
      psiMomentumPair (centeredSecondDifference dt previous current next)
          (imagCoordinateDirection site component) =
        psiEulerLagrangeForce chi0 current bond
          (imagCoordinateDirection site component) := by
    intro site component
    have hcalc := discrete_action_hasDerivAt chi0 B dt previous current next
      (purePsiDirection (imagCoordinateDirection site component)) bond
    have hstat := hstationary
      (purePsiDirection (imagCoordinateDirection site component))
    have hzero : discreteActionFirstVariation chi0 B dt previous current next
        (purePsiDirection (imagCoordinateDirection site component)) bond = 0 :=
      hcalc.unique hstat
    rw [discrete_psi_variation_eq_residual chi0 B dt previous current next
      bond hdt] at hzero
    have hresidual := (mul_eq_zero.mp hzero).resolve_left hdt
    linarith
  have hChiReal : ∀ site component,
      chiMomentumPair B (centeredSecondDifference dt previous current next)
          (realCoordinateDirection site component) =
        chiEulerLagrangeForce chi0 current bond
          (realCoordinateDirection site component) := by
    intro site component
    have hcalc := discrete_action_hasDerivAt chi0 B dt previous current next
      (pureChiDirection (realCoordinateDirection site component)) bond
    have hstat := hstationary
      (pureChiDirection (realCoordinateDirection site component))
    have hzero : discreteActionFirstVariation chi0 B dt previous current next
        (pureChiDirection (realCoordinateDirection site component)) bond = 0 :=
      hcalc.unique hstat
    rw [discrete_chi_variation_eq_residual chi0 B dt previous current next
      bond hdt] at hzero
    have hresidual := (mul_eq_zero.mp hzero).resolve_left hdt
    linarith
  have hChiImag : ∀ site component,
      chiMomentumPair B (centeredSecondDifference dt previous current next)
          (imagCoordinateDirection site component) =
        chiEulerLagrangeForce chi0 current bond
          (imagCoordinateDirection site component) := by
    intro site component
    have hcalc := discrete_action_hasDerivAt chi0 B dt previous current next
      (pureChiDirection (imagCoordinateDirection site component)) bond
    have hstat := hstationary
      (pureChiDirection (imagCoordinateDirection site component))
    have hzero : discreteActionFirstVariation chi0 B dt previous current next
        (pureChiDirection (imagCoordinateDirection site component)) bond = 0 :=
      hcalc.unique hstat
    rw [discrete_chi_variation_eq_residual chi0 B dt previous current next
      bond hdt] at hzero
    have hresidual := (mul_eq_zero.mp hzero).resolve_left hdt
    linarith
  have hacceleration : centeredSecondDifference dt previous current next =
      accelerationVelocity chi0 B current bond :=
    coordinate_equations_determine_acceleration chi0 B current bond
      (centeredSecondDifference dt previous current next) hB
      hPsiReal hPsiImag hChiReal hChiImag
  apply centered_second_difference_injective_next dt previous current next
    (nativeNextState chi0 B dt bond previous current) hdt
  rw [hacceleration]
  exact (centered_difference_native_next chi0 B dt bond previous current hdt).symm

structure DiscreteActionUpdateCertificate
    [Fintype Site] [DecidableEq Site] [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond Site)
    (previous current : State Site) : Prop where
  stationary : IsDiscreteActionStationary chi0 B dt previous current
    (nativeNextState chi0 B dt bond previous current) bond
  uniqueStationary : ∀ next : State Site,
    IsDiscreteActionStationary chi0 B dt previous current next bond →
      next = nativeNextState chi0 B dt bond previous current
  reversible :
    nativeNextState chi0 B dt bond
        (nativeNextState chi0 B dt bond previous current) current = previous
  psiEquation : ∀ eta : Site → C3,
    psiMomentumPair
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current)) eta =
      psiEulerLagrangeForce chi0 current bond eta
  chiEquation : ∀ eta : Site → C3,
    chiMomentumPair B
        (centeredSecondDifference dt previous current
          (nativeNextState chi0 B dt bond previous current)) eta =
      chiEulerLagrangeForce chi0 current bond eta

theorem dirac004_c19_update_iff_discrete_action_stationary
    [Fintype Site] [DecidableEq Site]
    (dt : ℝ) (geometry : C19Lattice Site)
    (previous current : State Site) (hdt : dt ≠ 0) :
    DiscreteActionUpdateCertificate chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current := by
  have hB : chiKineticNormalization ≠ 0 := by
    rw [chi_kinetic_normalization_eq_1197]
    norm_num
  constructor
  · exact native_next_is_discrete_action_stationary
      chi0 chiKineticNormalization dt (c19Bond geometry)
      previous current hB hdt
  · intro next hstationary
    exact discrete_stationarity_determines_native_next
      chi0 chiKineticNormalization dt (c19Bond geometry)
      previous current next hB hdt hstationary
  · exact native_next_is_reversible chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current
  · intro eta
    rw [centered_difference_native_next chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current hdt]
    exact psi_acceleration_all_directions chi0 chiKineticNormalization
      current (c19Bond geometry) eta
  · intro eta
    rw [centered_difference_native_next chi0 chiKineticNormalization dt
      (c19Bond geometry) previous current hdt]
    exact chi_acceleration_all_directions chi0 chiKineticNormalization
      current (c19Bond geometry) hB eta

end
end LeanDirac
