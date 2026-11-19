/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac003.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac002

/-!
DIRAC-003 derives the reciprocal local force and conjugate-momentum families
from independent state and velocity variations of the frozen DIRAC-002
action. The admitted gate is pointwise on the finite lattice and applies to
every state and velocity; it assumes no all-time decay, continuum equation or
stationary trajectory. A more restrictive global weak-form theorem remains
below as an auxiliary result, not as the production proof boundary. No time
integrator or Dirac claim is made.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators

abbrev AnalyticHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ inferInstance ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    inferInstance inferInstance f f' x

def c3RealPair (u v : C3) : ℝ :=
  ∑ component, (u component * star (v component)).re

def c3Add (u v : C3) : C3 := fun component => u component + v component

def c3ScaleReal (a : ℝ) (u : C3) : C3 :=
  fun component => (a : ℂ) * u component

def c3QuadraticLine (u v q : C3) (eps : ℝ) : C3 :=
  c3Add (c3Add u (c3ScaleReal eps v)) (c3ScaleReal (eps ^ 2) q)

theorem density_quadratic_line_exact (u v q : C3) (eps : ℝ) :
    density (c3QuadraticLine u v q eps) =
      density u + 2 * eps * c3RealPair u v +
      eps ^ 2 * (density v + 2 * c3RealPair u q) +
      2 * eps ^ 3 * c3RealPair v q + eps ^ 4 * density q := by
  simp [density, c3QuadraticLine, c3Add, c3ScaleReal, c3RealPair,
    Fin.sum_univ_succ, Complex.normSq]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

theorem density_quadratic_line_hasDerivAt (u v q : C3) :
    AnalyticHasDerivAt (fun eps : ℝ => density (c3QuadraticLine u v q eps))
      (2 * c3RealPair u v) 0 := by
  have hfun :
      (fun eps : ℝ => density (c3QuadraticLine u v q eps)) =
      (fun eps : ℝ =>
        density u + 2 * eps * c3RealPair u v +
        eps ^ 2 * (density v + 2 * c3RealPair u q) +
        2 * eps ^ 3 * c3RealPair v q + eps ^ 4 * density q) := by
    funext eps
    exact density_quadratic_line_exact u v q eps
  rw [hfun]
  have hconst := hasDerivAt_const (𝕜 := ℝ) 0 (density u)
  have hlinear := (HasDerivAt.const_mul (2 : ℝ)
    (hasDerivAt_id (0 : ℝ))).mul_const (c3RealPair u v)
  have hquad := (hasDerivAt_pow 2 (0 : ℝ)).mul_const
    (density v + 2 * c3RealPair u q)
  have hcubic := (HasDerivAt.const_mul (2 : ℝ)
    (hasDerivAt_pow 3 (0 : ℝ))).mul_const (c3RealPair v q)
  have hquartic := (hasDerivAt_pow 4 (0 : ℝ)).mul_const (density q)
  have hsum := (((hconst.add hlinear).add hquad).add hcubic).add hquartic
  convert hsum using 1
  · funext eps
    simp only [Pi.add_apply, id_eq]
  · norm_num

def c3Zero : C3 := fun _ => 0

@[simp] theorem c3_scale_zero (a : ℝ) : c3ScaleReal a c3Zero = c3Zero := by
  funext component
  simp [c3ScaleReal, c3Zero]

@[simp] theorem c3_zero_scale (u : C3) : c3ScaleReal 0 u = c3Zero := by
  funext component
  simp [c3ScaleReal, c3Zero]

@[simp] theorem c3_add_zero_right (u : C3) : c3Add u c3Zero = u := by
  funext component
  simp [c3Add, c3Zero]

def c3Line (u v : C3) (eps : ℝ) : C3 :=
  c3Add u (c3ScaleReal eps v)

def stateLine (state direction : State Site) (eps : ℝ) : State Site where
  psi site := c3Line (state.psi site) (direction.psi site) eps
  chi site := c3Line (state.chi site) (direction.chi site) eps

def wedgeFirstVariation (state direction : State Site) (site : Site) : C3 :=
  c3Add
    (wedge (direction.chi site) (state.psi site))
    (wedge (state.chi site) (direction.psi site))

def wedgeSecondVariation (direction : State Site) (site : Site) : C3 :=
  wedge (direction.chi site) (direction.psi site)

theorem wedge_state_line_exact (state direction : State Site)
    (site : Site) (eps : ℝ) :
    wedge ((stateLine state direction eps).chi site)
      ((stateLine state direction eps).psi site) =
      c3QuadraticLine
        (wedge (state.chi site) (state.psi site))
        (wedgeFirstVariation state direction site)
        (wedgeSecondVariation direction site) eps := by
  funext component
  fin_cases component <;>
    simp [stateLine, c3Line, c3Add, c3ScaleReal, c3QuadraticLine,
      wedgeFirstVariation, wedgeSecondVariation, wedge] <;>
    ring

def bondAreaDifference (state : State Site) (edge : Bond Site) : C3 :=
  difference
    (wedge (state.chi edge.source) (state.psi edge.source))
    (wedge (state.chi edge.target) (state.psi edge.target))

def bondAreaFirstVariation (state direction : State Site)
    (edge : Bond Site) : C3 :=
  difference
    (wedgeFirstVariation state direction edge.source)
    (wedgeFirstVariation state direction edge.target)

def bondAreaSecondVariation (direction : State Site)
    (edge : Bond Site) : C3 :=
  difference
    (wedgeSecondVariation direction edge.source)
    (wedgeSecondVariation direction edge.target)

theorem bond_area_state_line_exact (state direction : State Site)
    (edge : Bond Site) (eps : ℝ) :
    bondAreaDifference (stateLine state direction eps) edge =
      c3QuadraticLine
        (bondAreaDifference state edge)
        (bondAreaFirstVariation state direction edge)
        (bondAreaSecondVariation direction edge) eps := by
  funext component
  simp only [bondAreaDifference, difference,
    wedge_state_line_exact, c3QuadraticLine, c3Add, c3ScaleReal,
    bondAreaFirstVariation, bondAreaSecondVariation]
  ring_nf

def exteriorAreaBondFirstVariation (chi0 : ℝ)
    (state direction : State Site) (edge : Bond Site) : ℝ :=
  edge.weight / chi0 ^ 2 *
    c3RealPair (bondAreaDifference state edge)
      (bondAreaFirstVariation state direction edge)

theorem exterior_area_bond_hasDerivAt (chi0 : ℝ)
    (state direction : State Site) (edge : Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => exteriorAreaBond chi0 (stateLine state direction eps) edge)
      (exteriorAreaBondFirstVariation chi0 state direction edge) 0 := by
  have h := HasDerivAt.const_mul (edge.weight / (2 * chi0 ^ 2))
    (density_quadratic_line_hasDerivAt
      (bondAreaDifference state edge)
      (bondAreaFirstVariation state direction edge)
      (bondAreaSecondVariation direction edge))
  convert h using 1
  · funext eps
    unfold exteriorAreaBond
    change edge.weight / (2 * chi0 ^ 2) *
      density (bondAreaDifference (stateLine state direction eps) edge) = _
    rw [bond_area_state_line_exact]
  · unfold exteriorAreaBondFirstVariation
    ring

def sitePotentialFirstVariation (chi0 : ℝ)
    (state direction : State Site) (site : Site) : ℝ :=
  let rhoPsi := density (state.psi site)
  let rhoChi := density (state.chi site)
  (rhoChi - chi0 ^ 2 + rhoPsi) *
      c3RealPair (state.chi site) (direction.chi site) +
    (rhoChi + rhoPsi) *
      c3RealPair (state.psi site) (direction.psi site)

theorem site_potential_hasDerivAt (chi0 : ℝ)
    (state direction : State Site) (site : Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => sitePotential chi0 (stateLine state direction eps) site)
      (sitePotentialFirstVariation chi0 state direction site) 0 := by
  have hChi := density_quadratic_line_hasDerivAt
    (state.chi site) (direction.chi site) c3Zero
  have hPsi := density_quadratic_line_hasDerivAt
    (state.psi site) (direction.psi site) c3Zero
  have hChi' : AnalyticHasDerivAt
      (fun eps : ℝ => density ((stateLine state direction eps).chi site))
      (2 * c3RealPair (state.chi site) (direction.chi site)) 0 := by
    convert hChi using 1
    funext eps
    simp [stateLine, c3Line, c3QuadraticLine]
  have hPsi' : AnalyticHasDerivAt
      (fun eps : ℝ => density ((stateLine state direction eps).psi site))
      (2 * c3RealPair (state.psi site) (direction.psi site)) 0 := by
    convert hPsi using 1
    funext eps
    simp [stateLine, c3Line, c3QuadraticLine]
  have h :=
    ((((hChi'.sub_const (chi0 ^ 2)).pow 2).div_const 4).add
      ((hChi'.mul hPsi').div_const 2)).add
      ((hPsi'.pow 2).div_const 4)
  convert h using 1
  · funext eps
    simp [sitePotential, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  · unfold sitePotentialFirstVariation
    dsimp
    simp [stateLine, c3Line]
    ring

def potentialFirstVariation [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state direction : State Site)
    (bond : Edge → Bond Site) : ℝ :=
  (∑ site, sitePotentialFirstVariation chi0 state direction site) +
    ∑ edge, exteriorAreaBondFirstVariation chi0 state direction (bond edge)

theorem potential_hasDerivAt [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state direction : State Site)
    (bond : Edge → Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => potential chi0 (stateLine state direction eps) bond)
      (potentialFirstVariation chi0 state direction bond) 0 := by
  have hsites := HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun site _ => site_potential_hasDerivAt chi0 state direction site)
  have hedges := HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun edge _ => exterior_area_bond_hasDerivAt
      chi0 state direction (bond edge))
  have h := hsites.add hedges
  convert h using 1
  · funext eps
    simp [potential]
  · rfl

def lagrangianStateFirstVariation [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state direction : State Site)
    (bond : Edge → Bond Site) : ℝ :=
  -potentialFirstVariation chi0 state direction bond

theorem lagrangian_state_hasDerivAt [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state direction : State Site)
    (velocity : Velocity Site) (bond : Edge → Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        lagrangian chi0 B (stateLine state direction eps) velocity bond)
      (lagrangianStateFirstVariation chi0 state direction bond) 0 := by
  have hkinetic := hasDerivAt_const (𝕜 := ℝ) 0 (kinetic B velocity)
  have hpotential := potential_hasDerivAt chi0 state direction bond
  have h := hkinetic.sub hpotential
  convert h using 1
  · funext eps
    rfl
  · simp [lagrangianStateFirstVariation]

def purePsiDirection (etaPsi : Site → C3) : State Site where
  psi := etaPsi
  chi := fun _ => c3Zero

def pureChiDirection (etaChi : Site → C3) : State Site where
  psi := fun _ => c3Zero
  chi := etaChi

def psiEulerLagrangeForce [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (etaPsi : Site → C3) : ℝ :=
  lagrangianStateFirstVariation chi0 state
    (purePsiDirection etaPsi) bond

def chiEulerLagrangeForce [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (etaChi : Site → C3) : ℝ :=
  lagrangianStateFirstVariation chi0 state
    (pureChiDirection etaChi) bond

theorem psi_force_is_full_action_variation
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) :
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state (purePsiDirection etaPsi) eps) velocity bond)
      (psiEulerLagrangeForce chi0 state bond etaPsi) 0 := by
  exact lagrangian_state_hasDerivAt chi0 B state
    (purePsiDirection etaPsi) velocity bond

theorem chi_force_is_full_action_variation
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) :
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state (pureChiDirection etaChi) eps) velocity bond)
      (chiEulerLagrangeForce chi0 state bond etaChi) 0 := by
  exact lagrangian_state_hasDerivAt chi0 B state
    (pureChiDirection etaChi) velocity bond

def psiMomentumPair [Fintype Site]
    (velocity : Velocity Site) (etaPsi : Site → C3) : ℝ :=
  ∑ site, c3RealPair (velocity.psiDot site) (etaPsi site)

def chiMomentumPair [Fintype Site]
    (B : ℝ) (velocity : Velocity Site) (etaChi : Site → C3) : ℝ :=
  B * ∑ site, c3RealPair (velocity.chiDot site) (etaChi site)

def velocityLine (velocity direction : Velocity Site) (eps : ℝ) :
    Velocity Site where
  psiDot site := c3Line (velocity.psiDot site) (direction.psiDot site) eps
  chiDot site := c3Line (velocity.chiDot site) (direction.chiDot site) eps

def purePsiVelocity (etaPsi : Site → C3) : Velocity Site where
  psiDot := etaPsi
  chiDot := fun _ => c3Zero

def pureChiVelocity (etaChi : Site → C3) : Velocity Site where
  psiDot := fun _ => c3Zero
  chiDot := etaChi

theorem density_line_hasDerivAt (u v : C3) :
    AnalyticHasDerivAt (fun eps : ℝ => density (c3Line u v eps))
      (2 * c3RealPair u v) 0 := by
  convert density_quadratic_line_hasDerivAt u v c3Zero using 1
  funext eps
  simp [c3Line, c3QuadraticLine]

def kineticVelocityFirstVariation [Fintype Site]
    (B : ℝ) (velocity direction : Velocity Site) : ℝ :=
  psiMomentumPair velocity direction.psiDot +
    chiMomentumPair B velocity direction.chiDot

theorem kinetic_velocity_hasDerivAt [Fintype Site]
    (B : ℝ) (velocity direction : Velocity Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => kinetic B (velocityLine velocity direction eps))
      (kineticVelocityFirstVariation B velocity direction) 0 := by
  have hPsi := HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun site _ => density_line_hasDerivAt
      (velocity.psiDot site) (direction.psiDot site))
  have hChi := HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun site _ => density_line_hasDerivAt
      (velocity.chiDot site) (direction.chiDot site))
  have h := (hPsi.div_const 2).add
    ((HasDerivAt.const_mul B hChi).div_const 2)
  convert h using 1
  · funext eps
    simp [kinetic, velocityLine]
  · unfold kineticVelocityFirstVariation psiMomentumPair chiMomentumPair
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring

theorem lagrangian_velocity_hasDerivAt
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity direction : Velocity Site)
    (bond : Edge → Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        lagrangian chi0 B state (velocityLine velocity direction eps) bond)
      (kineticVelocityFirstVariation B velocity direction) 0 := by
  have hkinetic := kinetic_velocity_hasDerivAt B velocity direction
  have hpotential := hasDerivAt_const (𝕜 := ℝ) 0 (potential chi0 state bond)
  have h := hkinetic.sub hpotential
  convert h using 1
  · funext eps
    rfl
  · ring

theorem psi_momentum_is_full_action_velocity_variation
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) :
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B state
        (velocityLine velocity (purePsiVelocity etaPsi) eps) bond)
      (psiMomentumPair velocity etaPsi) 0 := by
  convert lagrangian_velocity_hasDerivAt chi0 B state velocity
    (purePsiVelocity etaPsi) bond using 1
  simp [kineticVelocityFirstVariation, purePsiVelocity,
    psiMomentumPair, chiMomentumPair, c3RealPair, c3Zero]

theorem chi_momentum_is_full_action_velocity_variation
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) :
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B state
        (velocityLine velocity (pureChiVelocity etaChi) eps) bond)
      (chiMomentumPair B velocity etaChi) 0 := by
  convert lagrangian_velocity_hasDerivAt chi0 B state velocity
    (pureChiVelocity etaChi) bond using 1
  simp [kineticVelocityFirstVariation, pureChiVelocity,
    psiMomentumPair, chiMomentumPair, c3RealPair, c3Zero]

structure NativeTrajectory (Site : Type) where
  state : ℝ → State Site
  velocity : ℝ → Velocity Site

def PsiEulerLagrangeEquationAt [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (t : ℝ) : Prop :=
  ∀ etaPsi : Site → C3,
    AnalyticHasDerivAt
      (fun tau => psiMomentumPair (trajectory.velocity tau) etaPsi)
      (psiEulerLagrangeForce chi0 (trajectory.state t) bond etaPsi) t

def ChiEulerLagrangeEquationAt [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (t : ℝ) : Prop :=
  ∀ etaChi : Site → C3,
    AnalyticHasDerivAt
      (fun tau => chiMomentumPair B (trajectory.velocity tau) etaChi)
      (chiEulerLagrangeForce chi0 (trajectory.state t) bond etaChi) t

structure TwoEulerLagrangeEquationFamiliesAt
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (t : ℝ) : Prop where
  psiEquation : PsiEulerLagrangeEquationAt chi0 bond trajectory t
  chiEquation : ChiEulerLagrangeEquationAt chi0 B bond trajectory t

/-!
The definitions below close the gap that the historical DIRAC-003 attempt
left open.  Stationarity is expressed as the vanishing of the integrated
first variation, containing the independently derived state force and
velocity momentum terms.  It is deliberately not defined as the
Euler--Lagrange equation.
-/

open MeasureTheory SchwartzMap

def integratedFirstVariation
    (force momentum test : SchwartzMap ℝ ℝ) : ℝ :=
  ∫ t : ℝ, test t * force t + deriv test t * momentum t

def IsIntegratedActionStationary
    (force momentum : SchwartzMap ℝ ℝ) : Prop :=
  ∀ test : SchwartzMap ℝ ℝ, integratedFirstVariation force momentum test = 0

def eulerLagrangeResidual
    (force momentum : SchwartzMap ℝ ℝ) : ℝ → ℝ :=
  fun t => force t - deriv momentum t

theorem integrated_first_variation_eq_residual
    (force momentum test : SchwartzMap ℝ ℝ) :
    integratedFirstVariation force momentum test =
      ∫ t : ℝ, test t * eulerLagrangeResidual force momentum t := by
  unfold integratedFirstVariation eulerLagrangeResidual
  have htf : Integrable (fun t : ℝ => test t * force t) := by
    change Integrable (pairing (ContinuousLinearMap.mul ℝ ℝ) test force)
    exact (pairing (ContinuousLinearMap.mul ℝ ℝ) test force).integrable
  have hdtm : Integrable (fun t : ℝ => deriv test t * momentum t) := by
    change Integrable (pairing (ContinuousLinearMap.mul ℝ ℝ)
      (derivCLM ℝ ℝ test) momentum)
    exact (pairing (ContinuousLinearMap.mul ℝ ℝ)
      (derivCLM ℝ ℝ test) momentum).integrable
  have htdm : Integrable (fun t : ℝ => test t * deriv momentum t) := by
    change Integrable (pairing (ContinuousLinearMap.mul ℝ ℝ) test
      (derivCLM ℝ ℝ momentum))
    exact (pairing (ContinuousLinearMap.mul ℝ ℝ) test
      (derivCLM ℝ ℝ momentum)).integrable
  calc
    (∫ t : ℝ, test t * force t + deriv test t * momentum t) =
        (∫ t : ℝ, test t * force t) +
          ∫ t : ℝ, deriv test t * momentum t := integral_add htf hdtm
    _ = (∫ t : ℝ, test t * force t) +
          ∫ t : ℝ, momentum t * deriv test t := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun t => mul_comm _ _)
    _ = (∫ t : ℝ, test t * force t) -
          ∫ t : ℝ, deriv momentum t * test t := by
          rw [integral_mul_deriv_eq_neg_deriv_mul momentum test]
          ring
    _ = (∫ t : ℝ, test t * force t) -
          ∫ t : ℝ, test t * deriv momentum t := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun t => mul_comm _ _)
    _ = ∫ t : ℝ, test t * force t - test t * deriv momentum t := by
          rw [integral_sub htf htdm]
    _ = ∫ t : ℝ, test t * (force t - deriv momentum t) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun t => by ring)

theorem integrated_stationarity_forces_euler_lagrange
    (force momentum : SchwartzMap ℝ ℝ)
    (hstationary : IsIntegratedActionStationary force momentum) :
    ∀ t : ℝ, eulerLagrangeResidual force momentum t = 0 := by
  have hzero_ae : ∀ᵐ t : ℝ,
      eulerLagrangeResidual force momentum t = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    · exact (force - derivCLM ℝ ℝ momentum).integrable.locallyIntegrable
    · intro g hgSmooth hgCompact
      let test : SchwartzMap ℝ ℝ := hgCompact.toSchwartzMap hgSmooth
      have htest := hstationary test
      rw [integrated_first_variation_eq_residual] at htest
      simpa [test, eulerLagrangeResidual, smul_eq_mul] using htest
  have hcontinuous : Continuous (eulerLagrangeResidual force momentum) := by
    exact force.continuous.sub (derivCLM ℝ ℝ momentum).continuous
  have hfun : eulerLagrangeResidual force momentum = (0 : ℝ → ℝ) :=
    MeasureTheory.Measure.eq_of_ae_eq hzero_ae hcontinuous continuous_const
  exact fun t => congrFun hfun t

def scaleC3Field (a : ℝ) (eta : Site → C3) : Site → C3 :=
  fun site => c3ScaleReal a (eta site)

def scaleStateDirection (a : ℝ) (direction : State Site) : State Site where
  psi := scaleC3Field a direction.psi
  chi := scaleC3Field a direction.chi

theorem c3_real_pair_scale_right (a : ℝ) (u v : C3) :
    c3RealPair u (c3ScaleReal a v) = a * c3RealPair u v := by
  simp [c3RealPair, c3ScaleReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  ring

theorem wedge_first_variation_scale (a : ℝ)
    (state direction : State Site) (site : Site) :
    wedgeFirstVariation state (scaleStateDirection a direction) site =
      c3ScaleReal a (wedgeFirstVariation state direction site) := by
  funext component
  fin_cases component <;>
    simp [wedgeFirstVariation, scaleStateDirection, scaleC3Field,
      c3ScaleReal, c3Add, wedge] <;>
    ring

theorem bond_area_first_variation_scale (a : ℝ)
    (state direction : State Site) (edge : Bond Site) :
    bondAreaFirstVariation state (scaleStateDirection a direction) edge =
      c3ScaleReal a (bondAreaFirstVariation state direction edge) := by
  funext component
  simp [bondAreaFirstVariation, difference,
    wedge_first_variation_scale, c3ScaleReal]
  ring

theorem site_potential_first_variation_scale (chi0 a : ℝ)
    (state direction : State Site) (site : Site) :
    sitePotentialFirstVariation chi0 state
      (scaleStateDirection a direction) site =
      a * sitePotentialFirstVariation chi0 state direction site := by
  unfold sitePotentialFirstVariation
  rw [show (scaleStateDirection a direction).chi site =
      c3ScaleReal a (direction.chi site) by rfl]
  rw [show (scaleStateDirection a direction).psi site =
      c3ScaleReal a (direction.psi site) by rfl]
  rw [c3_real_pair_scale_right, c3_real_pair_scale_right]
  ring

theorem exterior_area_bond_first_variation_scale (chi0 a : ℝ)
    (state direction : State Site) (edge : Bond Site) :
    exteriorAreaBondFirstVariation chi0 state
      (scaleStateDirection a direction) edge =
      a * exteriorAreaBondFirstVariation chi0 state direction edge := by
  unfold exteriorAreaBondFirstVariation
  rw [bond_area_first_variation_scale,
    c3_real_pair_scale_right]
  ring

theorem lagrangian_state_first_variation_scale
    [Fintype Site] [Fintype Edge]
    (chi0 a : ℝ) (state direction : State Site)
    (bond : Edge → Bond Site) :
    lagrangianStateFirstVariation chi0 state
      (scaleStateDirection a direction) bond =
      a * lagrangianStateFirstVariation chi0 state direction bond := by
  unfold lagrangianStateFirstVariation potentialFirstVariation
  simp_rw [site_potential_first_variation_scale,
    exterior_area_bond_first_variation_scale]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem scale_pure_psi_direction (a : ℝ) (etaPsi : Site → C3) :
    purePsiDirection (scaleC3Field a etaPsi) =
      scaleStateDirection a (purePsiDirection etaPsi) := by
  have hz : scaleC3Field a (fun _ : Site => c3Zero) =
      (fun _ : Site => c3Zero) := by
    funext site
    exact c3_scale_zero a
  unfold purePsiDirection scaleStateDirection
  dsimp
  rw [hz]

theorem scale_pure_chi_direction (a : ℝ) (etaChi : Site → C3) :
    pureChiDirection (scaleC3Field a etaChi) =
      scaleStateDirection a (pureChiDirection etaChi) := by
  have hz : scaleC3Field a (fun _ : Site => c3Zero) =
      (fun _ : Site => c3Zero) := by
    funext site
    exact c3_scale_zero a
  unfold pureChiDirection scaleStateDirection
  dsimp
  rw [hz]

theorem psi_force_scale [Fintype Site] [Fintype Edge]
    (chi0 a : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (etaPsi : Site → C3) :
    psiEulerLagrangeForce chi0 state bond (scaleC3Field a etaPsi) =
      a * psiEulerLagrangeForce chi0 state bond etaPsi := by
  unfold psiEulerLagrangeForce
  rw [scale_pure_psi_direction,
    lagrangian_state_first_variation_scale]

theorem chi_force_scale [Fintype Site] [Fintype Edge]
    (chi0 a : ℝ) (state : State Site) (bond : Edge → Bond Site)
    (etaChi : Site → C3) :
    chiEulerLagrangeForce chi0 state bond (scaleC3Field a etaChi) =
      a * chiEulerLagrangeForce chi0 state bond etaChi := by
  unfold chiEulerLagrangeForce
  rw [scale_pure_chi_direction,
    lagrangian_state_first_variation_scale]

theorem psi_momentum_scale [Fintype Site]
    (a : ℝ) (velocity : Velocity Site) (etaPsi : Site → C3) :
    psiMomentumPair velocity (scaleC3Field a etaPsi) =
      a * psiMomentumPair velocity etaPsi := by
  unfold psiMomentumPair scaleC3Field
  simp_rw [c3_real_pair_scale_right]
  rw [← Finset.mul_sum]

theorem chi_momentum_scale [Fintype Site]
    (B a : ℝ) (velocity : Velocity Site) (etaChi : Site → C3) :
    chiMomentumPair B velocity (scaleC3Field a etaChi) =
      a * chiMomentumPair B velocity etaChi := by
  unfold chiMomentumPair scaleC3Field
  simp_rw [c3_real_pair_scale_right]
  rw [← Finset.mul_sum]
  ring

theorem lagrangian_state_velocity_hasDerivAt
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state stateDirection : State Site)
    (velocity velocityDirection : Velocity Site)
    (bond : Edge → Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state stateDirection eps)
        (velocityLine velocity velocityDirection eps) bond)
      (lagrangianStateFirstVariation chi0 state stateDirection bond +
        kineticVelocityFirstVariation B velocity velocityDirection) 0 := by
  have hkinetic := kinetic_velocity_hasDerivAt B velocity velocityDirection
  have hpotential := potential_hasDerivAt chi0 state stateDirection bond
  have h := hkinetic.sub hpotential
  convert h using 1
  · funext eps
    rfl
  · simp [lagrangianStateFirstVariation]
    ring

theorem psi_test_variation_is_lagrangian_derivative
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaPsi : Site → C3) (g gDot : ℝ) :
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state
          (purePsiDirection (scaleC3Field g etaPsi)) eps)
        (velocityLine velocity
          (purePsiVelocity (scaleC3Field gDot etaPsi)) eps) bond)
      (g * psiEulerLagrangeForce chi0 state bond etaPsi +
        gDot * psiMomentumPair velocity etaPsi) 0 := by
  convert lagrangian_state_velocity_hasDerivAt chi0 B state
    (purePsiDirection (scaleC3Field g etaPsi)) velocity
    (purePsiVelocity (scaleC3Field gDot etaPsi)) bond using 1
  simp only [kineticVelocityFirstVariation, purePsiVelocity]
  simp [chiMomentumPair, c3RealPair, c3Zero]
  change g * psiEulerLagrangeForce chi0 state bond etaPsi +
      gDot * psiMomentumPair velocity etaPsi =
    psiEulerLagrangeForce chi0 state bond (scaleC3Field g etaPsi) +
      psiMomentumPair velocity (scaleC3Field gDot etaPsi)
  rw [psi_force_scale, psi_momentum_scale]

theorem chi_test_variation_is_lagrangian_derivative
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (etaChi : Site → C3) (g gDot : ℝ) :
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state
          (pureChiDirection (scaleC3Field g etaChi)) eps)
        (velocityLine velocity
          (pureChiVelocity (scaleC3Field gDot etaChi)) eps) bond)
      (g * chiEulerLagrangeForce chi0 state bond etaChi +
        gDot * chiMomentumPair B velocity etaChi) 0 := by
  convert lagrangian_state_velocity_hasDerivAt chi0 B state
    (pureChiDirection (scaleC3Field g etaChi)) velocity
    (pureChiVelocity (scaleC3Field gDot etaChi)) bond using 1
  simp only [kineticVelocityFirstVariation, pureChiVelocity]
  simp [psiMomentumPair, c3RealPair, c3Zero]
  change g * chiEulerLagrangeForce chi0 state bond etaChi +
      gDot * chiMomentumPair B velocity etaChi =
    chiEulerLagrangeForce chi0 state bond (scaleC3Field g etaChi) +
      chiMomentumPair B velocity (scaleC3Field gDot etaChi)
  rw [chi_force_scale, chi_momentum_scale]

structure PsiProjectedActionData
    [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaPsi : Site → C3) where
  force : SchwartzMap ℝ ℝ
  momentum : SchwartzMap ℝ ℝ
  force_eq : ∀ t : ℝ,
    force t = psiEulerLagrangeForce chi0 (trajectory.state t) bond etaPsi
  momentum_eq : ∀ t : ℝ,
    momentum t = psiMomentumPair (trajectory.velocity t) etaPsi

structure ChiProjectedActionData
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaChi : Site → C3) where
  force : SchwartzMap ℝ ℝ
  momentum : SchwartzMap ℝ ℝ
  force_eq : ∀ t : ℝ,
    force t = chiEulerLagrangeForce chi0 (trajectory.state t) bond etaChi
  momentum_eq : ∀ t : ℝ,
    momentum t = chiMomentumPair B (trajectory.velocity t) etaChi

def TrajectoryVelocityCompatible
    (trajectory : NativeTrajectory Site) : Prop :=
  (∀ (site : Site) (component : Fin 3) (t : ℝ),
    AnalyticHasDerivAt
      (fun tau => (trajectory.state tau).psi site component |>.re)
      ((trajectory.velocity t).psiDot site component |>.re) t) ∧
  (∀ (site : Site) (component : Fin 3) (t : ℝ),
    AnalyticHasDerivAt
      (fun tau => (trajectory.state tau).psi site component |>.im)
      ((trajectory.velocity t).psiDot site component |>.im) t) ∧
  (∀ (site : Site) (component : Fin 3) (t : ℝ),
    AnalyticHasDerivAt
      (fun tau => (trajectory.state tau).chi site component |>.re)
      ((trajectory.velocity t).chiDot site component |>.re) t) ∧
  (∀ (site : Site) (component : Fin 3) (t : ℝ),
    AnalyticHasDerivAt
      (fun tau => (trajectory.state tau).chi site component |>.im)
      ((trajectory.velocity t).chiDot site component |>.im) t)

theorem psi_euler_lagrange_of_integrated_stationarity
    [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaPsi : Site → C3)
    (data : PsiProjectedActionData chi0 bond trajectory etaPsi)
    (hstationary : IsIntegratedActionStationary data.force data.momentum) :
    ∀ t : ℝ,
      AnalyticHasDerivAt
        (fun tau => psiMomentumPair (trajectory.velocity tau) etaPsi)
        (psiEulerLagrangeForce chi0 (trajectory.state t) bond etaPsi) t := by
  have hresidual := integrated_stationarity_forces_euler_lagrange
    data.force data.momentum hstationary
  intro t
  have hmomentum := data.momentum.hasDerivAt t
  have hfunctions :
      (fun tau => psiMomentumPair (trajectory.velocity tau) etaPsi) =
        data.momentum := by
    funext tau
    exact (data.momentum_eq tau).symm
  rw [hfunctions]
  convert hmomentum using 1
  have hforce_deriv : data.force t = deriv data.momentum t :=
    sub_eq_zero.mp (hresidual t)
  rw [← data.force_eq t]
  exact hforce_deriv

theorem chi_euler_lagrange_of_integrated_stationarity
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaChi : Site → C3)
    (data : ChiProjectedActionData chi0 B bond trajectory etaChi)
    (hstationary : IsIntegratedActionStationary data.force data.momentum) :
    ∀ t : ℝ,
      AnalyticHasDerivAt
        (fun tau => chiMomentumPair B (trajectory.velocity tau) etaChi)
        (chiEulerLagrangeForce chi0 (trajectory.state t) bond etaChi) t := by
  have hresidual := integrated_stationarity_forces_euler_lagrange
    data.force data.momentum hstationary
  intro t
  have hmomentum := data.momentum.hasDerivAt t
  have hfunctions :
      (fun tau => chiMomentumPair B (trajectory.velocity tau) etaChi) =
        data.momentum := by
    funext tau
    exact (data.momentum_eq tau).symm
  rw [hfunctions]
  convert hmomentum using 1
  have hforce_deriv : data.force t = deriv data.momentum t :=
    sub_eq_zero.mp (hresidual t)
  rw [← data.force_eq t]
  exact hforce_deriv

theorem dirac003_two_equation_families_from_stationary_action
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site)
    (hcompatible : TrajectoryVelocityCompatible trajectory)
    (psiData : ∀ etaPsi : Site → C3,
      PsiProjectedActionData chi0 bond trajectory etaPsi)
    (chiData : ∀ etaChi : Site → C3,
      ChiProjectedActionData chi0 B bond trajectory etaChi)
    (hPsiStationary : ∀ etaPsi : Site → C3,
      IsIntegratedActionStationary
        (psiData etaPsi).force (psiData etaPsi).momentum)
    (hChiStationary : ∀ etaChi : Site → C3,
      IsIntegratedActionStationary
        (chiData etaChi).force (chiData etaChi).momentum) :
    TrajectoryVelocityCompatible trajectory ∧
      ∀ t : ℝ,
        TwoEulerLagrangeEquationFamiliesAt chi0 B bond trajectory t := by
  refine ⟨hcompatible, fun t => ?_⟩
  constructor
  · intro etaPsi
    exact psi_euler_lagrange_of_integrated_stationarity
      chi0 bond trajectory etaPsi (psiData etaPsi)
      (hPsiStationary etaPsi) t
  · intro etaChi
    exact chi_euler_lagrange_of_integrated_stationarity
      chi0 B bond trajectory etaChi (chiData etaChi)
      (hChiStationary etaChi) t

def psiActionIncrementIntegrand
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaPsi : Site → C3)
    (test : SchwartzMap ℝ ℝ) (eps t : ℝ) : ℝ :=
  let direction := scaleC3Field (test t) etaPsi
  let velocityDirection := scaleC3Field (deriv test t) etaPsi
  lagrangian chi0 B
      (stateLine (trajectory.state t) (purePsiDirection direction) eps)
      (velocityLine (trajectory.velocity t)
        (purePsiVelocity velocityDirection) eps) bond -
    lagrangian chi0 B (trajectory.state t) (trajectory.velocity t) bond

def chiActionIncrementIntegrand
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaChi : Site → C3)
    (test : SchwartzMap ℝ ℝ) (eps t : ℝ) : ℝ :=
  let direction := scaleC3Field (test t) etaChi
  let velocityDirection := scaleC3Field (deriv test t) etaChi
  lagrangian chi0 B
      (stateLine (trajectory.state t) (pureChiDirection direction) eps)
      (velocityLine (trajectory.velocity t)
        (pureChiVelocity velocityDirection) eps) bond -
    lagrangian chi0 B (trajectory.state t) (trajectory.velocity t) bond

def psiActionIncrement
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaPsi : Site → C3)
    (test : SchwartzMap ℝ ℝ) (eps : ℝ) : ℝ :=
  ∫ t : ℝ,
    psiActionIncrementIntegrand chi0 B bond trajectory etaPsi test eps t

def chiActionIncrement
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaChi : Site → C3)
    (test : SchwartzMap ℝ ℝ) (eps : ℝ) : ℝ :=
  ∫ t : ℝ,
    chiActionIncrementIntegrand chi0 B bond trajectory etaChi test eps t

structure IntegralVariationControl (F : ℝ → ℝ → ℝ) where
  neighborhood : Set ℝ
  neighborhood_mem : neighborhood ∈ nhds 0
  measurable_near_zero : ∀ᶠ eps in nhds 0,
    AEStronglyMeasurable (F eps)
  bound : ℝ → ℝ
  bound_integrable : Integrable bound
  locally_lipschitz : ∀ᵐ t : ℝ,
    LipschitzOnWith (Real.nnabs (bound t)) (fun eps => F eps t) neighborhood

def HasStationaryPsiAction
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaPsi : Site → C3) : Prop :=
  ∀ test : SchwartzMap ℝ ℝ,
    AnalyticHasDerivAt
      (psiActionIncrement chi0 B bond trajectory etaPsi test) 0 0

def HasStationaryChiAction
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaChi : Site → C3) : Prop :=
  ∀ test : SchwartzMap ℝ ℝ,
    AnalyticHasDerivAt
      (chiActionIncrement chi0 B bond trajectory etaChi test) 0 0

theorem psi_action_increment_pointwise_hasDerivAt
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaPsi : Site → C3)
    (data : PsiProjectedActionData chi0 bond trajectory etaPsi)
    (test : SchwartzMap ℝ ℝ) (t : ℝ) :
    AnalyticHasDerivAt
      (fun eps => psiActionIncrementIntegrand
        chi0 B bond trajectory etaPsi test eps t)
      (test t * data.force t + deriv test t * data.momentum t) 0 := by
  have h := psi_test_variation_is_lagrangian_derivative
    chi0 B (trajectory.state t) (trajectory.velocity t) bond etaPsi
    (test t) (deriv test t)
  have hsub := h.sub_const
    (lagrangian chi0 B (trajectory.state t) (trajectory.velocity t) bond)
  convert hsub using 1
  · funext eps
    rfl
  · rw [data.force_eq t, data.momentum_eq t]

theorem chi_action_increment_pointwise_hasDerivAt
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaChi : Site → C3)
    (data : ChiProjectedActionData chi0 B bond trajectory etaChi)
    (test : SchwartzMap ℝ ℝ) (t : ℝ) :
    AnalyticHasDerivAt
      (fun eps => chiActionIncrementIntegrand
        chi0 B bond trajectory etaChi test eps t)
      (test t * data.force t + deriv test t * data.momentum t) 0 := by
  have h := chi_test_variation_is_lagrangian_derivative
    chi0 B (trajectory.state t) (trajectory.velocity t) bond etaChi
    (test t) (deriv test t)
  have hsub := h.sub_const
    (lagrangian chi0 B (trajectory.state t) (trajectory.velocity t) bond)
  convert hsub using 1
  · funext eps
    rfl
  · rw [data.force_eq t, data.momentum_eq t]

theorem psi_integrated_stationarity_of_actual_action
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaPsi : Site → C3)
    (data : PsiProjectedActionData chi0 bond trajectory etaPsi)
    (hstationary : HasStationaryPsiAction
      chi0 B bond trajectory etaPsi)
    (hcontrol : ∀ test : SchwartzMap ℝ ℝ,
      IntegralVariationControl (psiActionIncrementIntegrand
        chi0 B bond trajectory etaPsi test)) :
    IsIntegratedActionStationary data.force data.momentum := by
  intro test
  let F := psiActionIncrementIntegrand
    chi0 B bond trajectory etaPsi test
  let F' : ℝ → ℝ := fun t =>
    test t * data.force t + deriv test t * data.momentum t
  have hF0 : Integrable (F 0) := by
    have hzero : F 0 = (0 : ℝ → ℝ) := by
      funext t
      simp [F, psiActionIncrementIntegrand, stateLine, velocityLine,
        c3Line]
    rw [hzero]
    exact integrable_zero ℝ ℝ volume
  have hF' : Integrable F' := by
    have htf : Integrable (fun t : ℝ => test t * data.force t) := by
      change Integrable (pairing (ContinuousLinearMap.mul ℝ ℝ)
        test data.force)
      exact (pairing (ContinuousLinearMap.mul ℝ ℝ) test data.force).integrable
    have hdm : Integrable
        (fun t : ℝ => deriv test t * data.momentum t) := by
      change Integrable (pairing (ContinuousLinearMap.mul ℝ ℝ)
        (derivCLM ℝ ℝ test) data.momentum)
      exact (pairing (ContinuousLinearMap.mul ℝ ℝ)
        (derivCLM ℝ ℝ test) data.momentum).integrable
    exact htf.add hdm
  have hdiff : ∀ᵐ t : ℝ,
      AnalyticHasDerivAt (fun eps => F eps t) (F' t) 0 :=
    Filter.Eventually.of_forall (fun t =>
      psi_action_increment_pointwise_hasDerivAt
        chi0 B bond trajectory etaPsi data test t)
  obtain ⟨_, hderived⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_lip
      (hcontrol test).neighborhood_mem
      (hcontrol test).measurable_near_zero hF0
      hF'.aestronglyMeasurable
      (hcontrol test).locally_lipschitz
      (hcontrol test).bound_integrable hdiff
  have hactual := hstationary test
  have heq : (∫ t : ℝ, F' t) = 0 := by
    exact hderived.unique hactual
  simpa [integratedFirstVariation, F'] using heq

theorem chi_integrated_stationarity_of_actual_action
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (bond : Edge → Bond Site)
    (trajectory : NativeTrajectory Site) (etaChi : Site → C3)
    (data : ChiProjectedActionData chi0 B bond trajectory etaChi)
    (hstationary : HasStationaryChiAction
      chi0 B bond trajectory etaChi)
    (hcontrol : ∀ test : SchwartzMap ℝ ℝ,
      IntegralVariationControl (chiActionIncrementIntegrand
        chi0 B bond trajectory etaChi test)) :
    IsIntegratedActionStationary data.force data.momentum := by
  intro test
  let F := chiActionIncrementIntegrand
    chi0 B bond trajectory etaChi test
  let F' : ℝ → ℝ := fun t =>
    test t * data.force t + deriv test t * data.momentum t
  have hF0 : Integrable (F 0) := by
    have hzero : F 0 = (0 : ℝ → ℝ) := by
      funext t
      simp [F, chiActionIncrementIntegrand, stateLine, velocityLine,
        c3Line]
    rw [hzero]
    exact integrable_zero ℝ ℝ volume
  have hF' : Integrable F' := by
    have htf : Integrable (fun t : ℝ => test t * data.force t) := by
      change Integrable (pairing (ContinuousLinearMap.mul ℝ ℝ)
        test data.force)
      exact (pairing (ContinuousLinearMap.mul ℝ ℝ) test data.force).integrable
    have hdm : Integrable
        (fun t : ℝ => deriv test t * data.momentum t) := by
      change Integrable (pairing (ContinuousLinearMap.mul ℝ ℝ)
        (derivCLM ℝ ℝ test) data.momentum)
      exact (pairing (ContinuousLinearMap.mul ℝ ℝ)
        (derivCLM ℝ ℝ test) data.momentum).integrable
    exact htf.add hdm
  have hdiff : ∀ᵐ t : ℝ,
      AnalyticHasDerivAt (fun eps => F eps t) (F' t) 0 :=
    Filter.Eventually.of_forall (fun t =>
      chi_action_increment_pointwise_hasDerivAt
        chi0 B bond trajectory etaChi data test t)
  obtain ⟨_, hderived⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_lip
      (hcontrol test).neighborhood_mem
      (hcontrol test).measurable_near_zero hF0
      hF'.aestronglyMeasurable
      (hcontrol test).locally_lipschitz
      (hcontrol test).bound_integrable hdiff
  have hactual := hstationary test
  have heq : (∫ t : ℝ, F' t) = 0 := by
    exact hderived.unique hactual
  simpa [integratedFirstVariation, F'] using heq

theorem dirac003_c19_equations_from_actual_stationary_action
    [Fintype Site]
    (chi0 B : ℝ) (geometry : C19Lattice Site)
    (trajectory : NativeTrajectory Site)
    (hcompatible : TrajectoryVelocityCompatible trajectory)
    (psiData : ∀ etaPsi : Site → C3,
      PsiProjectedActionData chi0 (c19Bond geometry) trajectory etaPsi)
    (chiData : ∀ etaChi : Site → C3,
      ChiProjectedActionData chi0 B (c19Bond geometry) trajectory etaChi)
    (hPsiStationary : ∀ etaPsi : Site → C3,
      HasStationaryPsiAction chi0 B (c19Bond geometry) trajectory etaPsi)
    (hChiStationary : ∀ etaChi : Site → C3,
      HasStationaryChiAction chi0 B (c19Bond geometry) trajectory etaChi)
    (hPsiControl : ∀ (etaPsi : Site → C3) (test : SchwartzMap ℝ ℝ),
      IntegralVariationControl (psiActionIncrementIntegrand
        chi0 B (c19Bond geometry) trajectory etaPsi test))
    (hChiControl : ∀ (etaChi : Site → C3) (test : SchwartzMap ℝ ℝ),
      IntegralVariationControl (chiActionIncrementIntegrand
        chi0 B (c19Bond geometry) trajectory etaChi test)) :
    TrajectoryVelocityCompatible trajectory ∧
      ∀ t : ℝ, TwoEulerLagrangeEquationFamiliesAt
        chi0 B (c19Bond geometry) trajectory t := by
  apply dirac003_two_equation_families_from_stationary_action
    chi0 B (c19Bond geometry) trajectory hcompatible psiData chiData
  · intro etaPsi
    exact psi_integrated_stationarity_of_actual_action
      chi0 B (c19Bond geometry) trajectory etaPsi (psiData etaPsi)
      (hPsiStationary etaPsi) (hPsiControl etaPsi)
  · intro etaChi
    exact chi_integrated_stationarity_of_actual_action
      chi0 B (c19Bond geometry) trajectory etaChi (chiData etaChi)
      (hChiStationary etaChi) (hChiControl etaChi)

/-!
The admitted DIRAC-003 boundary is local and lattice-first.  It does not
require a trajectory extending over all real time, decay of a running state,
or a continuum equation.  It records the four independent derivatives of
the same native Lagrangian: state and velocity variations for each of the two
field families.  The older global weak-form theorem above remains a valid
auxiliary theorem, but is not the production gate.
-/

structure LocalTwoFieldVariationCertificate
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) : Prop where
  psiState : ∀ etaPsi : Site → C3,
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state (purePsiDirection etaPsi) eps) velocity bond)
      (psiEulerLagrangeForce chi0 state bond etaPsi) 0
  chiState : ∀ etaChi : Site → C3,
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state (pureChiDirection etaChi) eps) velocity bond)
      (chiEulerLagrangeForce chi0 state bond etaChi) 0
  psiVelocity : ∀ etaPsi : Site → C3,
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B state
        (velocityLine velocity (purePsiVelocity etaPsi) eps) bond)
      (psiMomentumPair velocity etaPsi) 0
  chiVelocity : ∀ etaChi : Site → C3,
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B state
        (velocityLine velocity (pureChiVelocity etaChi) eps) bond)
      (chiMomentumPair B velocity etaChi) 0
  combined : ∀ (stateDirection : State Site)
      (velocityDirection : Velocity Site),
    AnalyticHasDerivAt
      (fun eps : ℝ => lagrangian chi0 B
        (stateLine state stateDirection eps)
        (velocityLine velocity velocityDirection eps) bond)
      (lagrangianStateFirstVariation chi0 state stateDirection bond +
        kineticVelocityFirstVariation B velocity velocityDirection) 0

theorem dirac003_local_variations_from_actual_action
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) :
    LocalTwoFieldVariationCertificate chi0 B state velocity bond := by
  constructor
  · exact fun etaPsi =>
      psi_force_is_full_action_variation
        chi0 B state velocity bond etaPsi
  · exact fun etaChi =>
      chi_force_is_full_action_variation
        chi0 B state velocity bond etaChi
  · exact fun etaPsi =>
      psi_momentum_is_full_action_velocity_variation
        chi0 B state velocity bond etaPsi
  · exact fun etaChi =>
      chi_momentum_is_full_action_velocity_variation
        chi0 B state velocity bond etaChi
  · exact fun stateDirection velocityDirection =>
      lagrangian_state_velocity_hasDerivAt chi0 B state stateDirection
        velocity velocityDirection bond

theorem dirac003_c19_local_variations_from_actual_action
    [Fintype Site]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (geometry : C19Lattice Site) :
    LocalTwoFieldVariationCertificate chi0 B state velocity
      (c19Bond geometry) :=
  dirac003_local_variations_from_actual_action
    chi0 B state velocity (c19Bond geometry)

end
end LeanDirac
