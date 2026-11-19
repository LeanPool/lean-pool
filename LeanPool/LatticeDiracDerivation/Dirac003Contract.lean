/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac003Contract.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac003

/-!
Independent source-shape contracts for the local DIRAC-003 boundary.

Each expected curve is written directly from the native Lagrangian rather
than through a force, momentum, Euler--Lagrange equation, or stationarity
predicate. The derivative theorems therefore check that the admitted force
and momentum readouts are genuinely derivatives of the declared action.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section

def ExpectedPsiStateCurve
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) (eps : ℝ) : ℝ :=
  lagrangian chi0 B
    (stateLine state (purePsiDirection etaPsi) eps) velocity bond

def ExpectedChiStateCurve
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) (eps : ℝ) : ℝ :=
  lagrangian chi0 B
    (stateLine state (pureChiDirection etaChi) eps) velocity bond

def ExpectedPsiVelocityCurve
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) (eps : ℝ) : ℝ :=
  lagrangian chi0 B state
    (velocityLine velocity (purePsiVelocity etaPsi) eps) bond

def ExpectedChiVelocityCurve
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) (eps : ℝ) : ℝ :=
  lagrangian chi0 B state
    (velocityLine velocity (pureChiVelocity etaChi) eps) bond

theorem psi_state_curve_is_raw_lagrangian
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) :
    ExpectedPsiStateCurve chi0 B state velocity bond etaPsi =
      fun eps : ℝ => lagrangian chi0 B
        (stateLine state (purePsiDirection etaPsi) eps) velocity bond := by
  rfl

theorem chi_state_curve_is_raw_lagrangian
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) :
    ExpectedChiStateCurve chi0 B state velocity bond etaChi =
      fun eps : ℝ => lagrangian chi0 B
        (stateLine state (pureChiDirection etaChi) eps) velocity bond := by
  rfl

theorem psi_velocity_curve_is_raw_lagrangian
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) :
    ExpectedPsiVelocityCurve chi0 B state velocity bond etaPsi =
      fun eps : ℝ => lagrangian chi0 B state
        (velocityLine velocity (purePsiVelocity etaPsi) eps) bond := by
  rfl

theorem chi_velocity_curve_is_raw_lagrangian
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) :
    ExpectedChiVelocityCurve chi0 B state velocity bond etaChi =
      fun eps : ℝ => lagrangian chi0 B state
        (velocityLine velocity (pureChiVelocity etaChi) eps) bond := by
  rfl

theorem psi_state_curve_derivative_is_native_force
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) :
    AnalyticHasDerivAt
      (ExpectedPsiStateCurve chi0 B state velocity bond etaPsi)
      (psiEulerLagrangeForce chi0 state bond etaPsi) 0 := by
  exact psi_force_is_full_action_variation
    chi0 B state velocity bond etaPsi

theorem chi_state_curve_derivative_is_native_force
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) :
    AnalyticHasDerivAt
      (ExpectedChiStateCurve chi0 B state velocity bond etaChi)
      (chiEulerLagrangeForce chi0 state bond etaChi) 0 := by
  exact chi_force_is_full_action_variation
    chi0 B state velocity bond etaChi

theorem psi_velocity_curve_derivative_is_native_momentum
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) :
    AnalyticHasDerivAt
      (ExpectedPsiVelocityCurve chi0 B state velocity bond etaPsi)
      (psiMomentumPair velocity etaPsi) 0 := by
  exact psi_momentum_is_full_action_velocity_variation
    chi0 B state velocity bond etaPsi

theorem chi_velocity_curve_derivative_is_native_momentum
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) :
    AnalyticHasDerivAt
      (ExpectedChiVelocityCurve chi0 B state velocity bond etaChi)
      (chiMomentumPair B velocity etaChi) 0 := by
  exact chi_momentum_is_full_action_velocity_variation
    chi0 B state velocity bond etaChi

end
end LeanDirac
