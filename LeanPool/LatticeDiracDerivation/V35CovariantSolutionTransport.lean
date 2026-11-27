/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit 43859849eb6ed37e16c802fbae3fd50dd731665c.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V35GeneratedLorentzTransformations

/-!
# V3.5 Stage 4: finite boost covariance and compositional solution transport

This is algebraic transport in momentum space, not packet transport.  The
finite spinor boost is the V3.2 exponential of the cube-derived generator.
Its momentum action is written with the same half-rapidity coefficients, so
no external Lorentz matrix is inserted.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The standard-coordinate energy action fixed by covariance with the
cube-generator orientation: axis 0 is +z, axis 1 is -y, and axis 2 is -x. -/
def v35FiniteBoostEnergy
    (axis : Fin 3) (rapidity energy px py pz : ℝ) : ℝ :=
  let c := Real.cosh (rapidity / 2)
  let s := Real.sinh (rapidity / 2)
  let cosine := c^2 + s^2
  let sine := 2 * c * s
  match axis with
  | 0 => cosine * energy + sine * pz
  | 1 => cosine * energy - sine * py
  | _ => cosine * energy - sine * px

/-- Spatial momentum after the inherited finite boost along a cubical axis. -/
def v35FiniteBoostMomentum
    (axis : Fin 3) (rapidity energy px py pz : ℝ) : Fin 3 → ℝ :=
  let c := Real.cosh (rapidity / 2)
  let s := Real.sinh (rapidity / 2)
  let cosine := c^2 + s^2
  let sine := 2 * c * s
  match axis with
  | 0 => ![px, py, cosine * pz + sine * energy]
  | 1 => ![px, cosine * py - sine * energy, pz]
  | _ => ![cosine * px - sine * energy, py, pz]

/-- Spatial momentum after the inherited finite rotation about a cubical axis. -/
def v35FiniteRotationMomentum
    (axis : Fin 3) (angle px py pz : ℝ) : Fin 3 → ℝ :=
  let c := Real.cos (nativeCubicalSpinScale * angle)
  let s := Real.sin (nativeCubicalSpinScale * angle)
  let cosine := c^2 - s^2
  let sine := 2 * c * s
  match axis with
  | 0 => ![cosine * px + sine * py, -sine * px + cosine * py, pz]
  | 1 => ![cosine * px + sine * pz, py, -sine * px + cosine * pz]
  | _ => ![px, cosine * py - sine * pz, sine * py + cosine * pz]

theorem v35_finite_boost_mass_shell
    (axis : Fin 3) (rapidity energy px py pz : ℝ) :
    v35FiniteBoostEnergy axis rapidity energy px py pz ^ 2 -
        (v35FiniteBoostMomentum axis rapidity energy px py pz 0)^2 -
        (v35FiniteBoostMomentum axis rapidity energy px py pz 1)^2 -
        (v35FiniteBoostMomentum axis rapidity energy px py pz 2)^2 =
      energy^2 - px^2 - py^2 - pz^2 := by
  have hunit := Real.cosh_sq_sub_sinh_sq (rapidity / 2)
  have hboost (e p : ℝ) :
      ((Real.cosh (rapidity / 2)^2 + Real.sinh (rapidity / 2)^2) * e +
          2 * Real.cosh (rapidity / 2) * Real.sinh (rapidity / 2) * p)^2 -
        ((Real.cosh (rapidity / 2)^2 + Real.sinh (rapidity / 2)^2) * p +
          2 * Real.cosh (rapidity / 2) * Real.sinh (rapidity / 2) * e)^2 =
        e^2 - p^2 := by
    calc
      _ = (Real.cosh (rapidity / 2)^2 - Real.sinh (rapidity / 2)^2)^2 *
          (e^2 - p^2) := by ring
      _ = e^2 - p^2 := by rw [hunit]; ring
  fin_cases axis
  · simp [v35FiniteBoostEnergy, v35FiniteBoostMomentum]
    nlinarith [hboost energy pz]
  · simp [v35FiniteBoostEnergy, v35FiniteBoostMomentum]
    nlinarith [hboost energy (-py)]
  · simp [v35FiniteBoostEnergy, v35FiniteBoostMomentum]
    nlinarith [hboost energy (-px)]

theorem v35_finite_rotation_momentum_norm
    (axis : Fin 3) (angle px py pz : ℝ) :
    (v35FiniteRotationMomentum axis angle px py pz 0)^2 +
        (v35FiniteRotationMomentum axis angle px py pz 1)^2 +
        (v35FiniteRotationMomentum axis angle px py pz 2)^2 =
      px^2 + py^2 + pz^2 := by
  have hunit := Real.cos_sq_add_sin_sq ((1 / 2 : ℝ) * angle)
  have hrotation (first second : ℝ) :
      ((Real.cos ((1 / 2 : ℝ) * angle)^2 -
          Real.sin ((1 / 2 : ℝ) * angle)^2) * first -
          2 * Real.cos ((1 / 2 : ℝ) * angle) *
            Real.sin ((1 / 2 : ℝ) * angle) * second)^2 +
        (2 * Real.cos ((1 / 2 : ℝ) * angle) *
            Real.sin ((1 / 2 : ℝ) * angle) * first +
          (Real.cos ((1 / 2 : ℝ) * angle)^2 -
            Real.sin ((1 / 2 : ℝ) * angle)^2) * second)^2 =
        first^2 + second^2 := by
    calc
      _ = (Real.cos ((1 / 2 : ℝ) * angle)^2 +
          Real.sin ((1 / 2 : ℝ) * angle)^2)^2 *
          (first^2 + second^2) := by ring
      _ = first^2 + second^2 := by rw [hunit]; ring
  fin_cases axis
  · simp [v35FiniteRotationMomentum, native_cubical_spin_scale_eq_half]
    nlinarith [hrotation px py]
  · simp [v35FiniteRotationMomentum, native_cubical_spin_scale_eq_half]
    nlinarith [hrotation px pz]
  · simp [v35FiniteRotationMomentum, native_cubical_spin_scale_eq_half]
    nlinarith [hrotation py pz]

theorem v35_finite_boost_covariant
    (axis : Fin 3) (rapidity mass energy px py pz : ℝ)
    (z : CubicalCell4) :
    v34DiracResidual mass
        (v35FiniteBoostEnergy axis rapidity energy px py pz)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 0)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 1)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 2)
        (standardCubicalFiniteBoost axis rapidity z) =
      standardCubicalFiniteBoost axis rapidity
        (v34DiracResidual mass energy px py pz z) := by
  have hunitC := Complex.cosh_sq_sub_sinh_sq ((rapidity : ℂ) / 2)
  have hc3 : Complex.cosh ((rapidity : ℂ) / 2)^3 =
      Complex.cosh ((rapidity : ℂ) / 2) +
        Complex.cosh ((rapidity : ℂ) / 2) *
          Complex.sinh ((rapidity : ℂ) / 2)^2 := by
    calc
      _ = Complex.cosh ((rapidity : ℂ) / 2) *
          Complex.cosh ((rapidity : ℂ) / 2)^2 := by ring
      _ = _ := by
        rw [show Complex.cosh ((rapidity : ℂ) / 2)^2 =
          1 + Complex.sinh ((rapidity : ℂ) / 2)^2 by
            linear_combination hunitC]
        ring
  have hcs : Complex.cosh ((rapidity : ℂ) / 2)^2 *
      Complex.sinh ((rapidity : ℂ) / 2) =
      Complex.sinh ((rapidity : ℂ) / 2) +
        Complex.sinh ((rapidity : ℂ) / 2)^3 := by
    rw [show Complex.cosh ((rapidity : ℂ) / 2)^2 =
      1 + Complex.sinh ((rapidity : ℂ) / 2)^2 by
        linear_combination hunitC]
    ring
  ring_nf at hc3 hcs
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [v34DiracResidual, v34MomentumSlash, v34CovariantMomentum,
      v34Gamma, v35FiniteBoostEnergy, v35FiniteBoostMomentum,
      standardCubicalFiniteBoost,
      cubicalGammaTime, cubicalGammaSpace, cubicalAlpha,
      cubicalStandardBeta, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, Fin.sum_univ_four] <;>
    ring_nf
  all_goals simp only [hc3, hcs, Complex.I_sq]
  all_goals ring

theorem v35_finite_rotation_covariant
    (axis : Fin 3) (angle mass energy px py pz : ℝ)
    (z : CubicalCell4) :
    v34DiracResidual mass energy
        (v35FiniteRotationMomentum axis angle px py pz 0)
        (v35FiniteRotationMomentum axis angle px py pz 1)
        (v35FiniteRotationMomentum axis angle px py pz 2)
        (standardCubicalContinuousTurn angle axis z) =
      standardCubicalContinuousTurn angle axis
        (v34DiracResidual mass energy px py pz z) := by
  have hunitC := Complex.cos_sq_add_sin_sq ((1 / 2 : ℂ) * (angle : ℂ))
  have hc2 : Complex.cos ((1 / 2 : ℂ) * (angle : ℂ))^2 =
      1 - Complex.sin ((1 / 2 : ℂ) * (angle : ℂ))^2 := by
    linear_combination hunitC
  have hc3 : Complex.cos ((1 / 2 : ℂ) * (angle : ℂ))^3 =
      Complex.cos ((1 / 2 : ℂ) * (angle : ℂ)) -
        Complex.cos ((1 / 2 : ℂ) * (angle : ℂ)) *
          Complex.sin ((1 / 2 : ℂ) * (angle : ℂ))^2 := by
    calc
      _ = Complex.cos ((1 / 2 : ℂ) * (angle : ℂ)) *
          Complex.cos ((1 / 2 : ℂ) * (angle : ℂ))^2 := by ring
      _ = _ := by rw [hc2]; ring
  ring_nf at hc2 hc3
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [v34DiracResidual, v34MomentumSlash, v34CovariantMomentum,
      v34Gamma, v35FiniteRotationMomentum,
      standardCubicalContinuousTurn, standardCubicalRotorCoefficients,
      standardCubicalSpin, standardCubicalPlaneBivector,
      cubicalGammaTime, cubicalGammaSpace, cubicalAlpha,
      cubicalStandardBeta, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, Fin.sum_univ_four] <;>
    ring_nf
  all_goals norm_num [pow_succ, Complex.I_sq]
  all_goals ring_nf
  all_goals rw [hc2, hc3]
  all_goals ring

theorem v35_finite_boost_preserves_solutions
    (axis : Fin 3) (rapidity mass energy px py pz : ℝ)
    (z : CubicalCell4)
    (hsolution : v34DiracResidual mass energy px py pz z = 0) :
    v34DiracResidual mass
        (v35FiniteBoostEnergy axis rapidity energy px py pz)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 0)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 1)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 2)
        (standardCubicalFiniteBoost axis rapidity z) = 0 := by
  rw [v35_finite_boost_covariant]
  rw [hsolution]
  funext component
  fin_cases axis <;> fin_cases component <;>
  simp [standardCubicalFiniteBoost, standardCubicalGamma,
    cubicalStandardAlphaX, cubicalStandardAlphaY,
    cubicalStandardAlphaZ]

/-- Energy and three-momentum data transformed alongside a free spinor. -/
structure V35MomentumState where
  /-- Energy component. -/
  energy : ℝ
  /-- Spatial momentum components. -/
  momentum : Fin 3 → ℝ

/-- Apply one rotation or boost to energy-momentum data. -/
def v35ApplyKinematicStep
    (step : V35LorentzStep) (state : V35MomentumState) : V35MomentumState :=
  match step with
  | .rotation axis angle =>
      { energy := state.energy
        momentum := v35FiniteRotationMomentum axis angle
          (state.momentum 0) (state.momentum 1) (state.momentum 2) }
  | .boost axis rapidity =>
      { energy := v35FiniteBoostEnergy axis rapidity state.energy
          (state.momentum 0) (state.momentum 1) (state.momentum 2)
        momentum := v35FiniteBoostMomentum axis rapidity state.energy
          (state.momentum 0) (state.momentum 1) (state.momentum 2) }

/-- Apply a finite generated word to energy-momentum data. -/
def v35ApplyKinematicWord : V35LorentzWord → V35MomentumState → V35MomentumState
  | [], state => state
  | step :: rest, state =>
      v35ApplyKinematicWord rest (v35ApplyKinematicStep step state)

/-- Evaluate the inherited free Dirac residual at an energy-momentum state. -/
def v35ResidualAt
    (mass : ℝ) (state : V35MomentumState) (z : CubicalCell4) : CubicalCell4 :=
  v34DiracResidual mass state.energy
    (state.momentum 0) (state.momentum 1) (state.momentum 2) z

theorem v35_lorentz_step_covariant
    (step : V35LorentzStep) (mass : ℝ)
    (state : V35MomentumState) (z : CubicalCell4) :
    v35ResidualAt mass (v35ApplyKinematicStep step state)
        (v35ApplyLorentzStep step z) =
      v35ApplyLorentzStep step (v35ResidualAt mass state z) := by
  cases step with
  | rotation axis angle =>
      exact v35_finite_rotation_covariant axis angle mass state.energy
        (state.momentum 0) (state.momentum 1) (state.momentum 2) z
  | boost axis rapidity =>
      exact v35_finite_boost_covariant axis rapidity mass state.energy
        (state.momentum 0) (state.momentum 1) (state.momentum 2) z

theorem v35_lorentz_word_covariant
    (word : V35LorentzWord) (mass : ℝ)
    (state : V35MomentumState) (z : CubicalCell4) :
    v35ResidualAt mass (v35ApplyKinematicWord word state)
        (v35ApplyLorentzWord word z) =
      v35ApplyLorentzWord word (v35ResidualAt mass state z) := by
  induction word generalizing state z with
  | nil => rfl
  | cons step rest ih =>
      simp only [v35ApplyKinematicWord, v35ApplyLorentzWord]
      rw [ih]
      rw [v35_lorentz_step_covariant]

theorem v35_lorentz_step_zero (step : V35LorentzStep) :
    v35ApplyLorentzStep step (0 : CubicalCell4) = 0 := by
  cases step with
  | rotation axis angle =>
      funext component
      fin_cases axis <;> fin_cases component <;>
        simp [v35ApplyLorentzStep, standardCubicalContinuousTurn,
          standardCubicalRotorCoefficients, standardCubicalSpin,
          standardCubicalPlaneBivector, standardCubicalGamma,
          cubicalStandardAlphaX, cubicalStandardAlphaY,
          cubicalStandardAlphaZ]
  | boost axis rapidity =>
      funext component
      fin_cases axis <;> fin_cases component <;>
        simp [v35ApplyLorentzStep, standardCubicalFiniteBoost,
          standardCubicalGamma, cubicalStandardAlphaX,
          cubicalStandardAlphaY, cubicalStandardAlphaZ]

theorem v35_lorentz_word_zero (word : V35LorentzWord) :
    v35ApplyLorentzWord word (0 : CubicalCell4) = 0 := by
  induction word with
  | nil => rfl
  | cons step rest ih =>
      simp only [v35ApplyLorentzWord]
      rw [v35_lorentz_step_zero]
      exact ih

theorem v35_lorentz_word_preserves_solutions
    (word : V35LorentzWord) (mass : ℝ)
    (state : V35MomentumState) (z : CubicalCell4)
    (hsolution : v35ResidualAt mass state z = 0) :
    v35ResidualAt mass (v35ApplyKinematicWord word state)
        (v35ApplyLorentzWord word z) = 0 := by
  rw [v35_lorentz_word_covariant, hsolution, v35_lorentz_word_zero]

/-- Certificate for finite generated covariance and preservation of
zero-residual free solutions. -/
structure V35CovariantSolutionTransportCertificate : Prop where
  massShell : ∀ axis rapidity energy px py pz,
    v35FiniteBoostEnergy axis rapidity energy px py pz ^ 2 -
        (v35FiniteBoostMomentum axis rapidity energy px py pz 0)^2 -
        (v35FiniteBoostMomentum axis rapidity energy px py pz 1)^2 -
        (v35FiniteBoostMomentum axis rapidity energy px py pz 2)^2 =
      energy^2 - px^2 - py^2 - pz^2
  rotationNorm : ∀ axis angle px py pz,
    (v35FiniteRotationMomentum axis angle px py pz 0)^2 +
        (v35FiniteRotationMomentum axis angle px py pz 1)^2 +
        (v35FiniteRotationMomentum axis angle px py pz 2)^2 =
      px^2 + py^2 + pz^2
  covariance : ∀ axis rapidity mass energy px py pz z,
    v34DiracResidual mass
        (v35FiniteBoostEnergy axis rapidity energy px py pz)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 0)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 1)
        (v35FiniteBoostMomentum axis rapidity energy px py pz 2)
        (standardCubicalFiniteBoost axis rapidity z) =
      standardCubicalFiniteBoost axis rapidity
        (v34DiracResidual mass energy px py pz z)
  rotationCovariance : ∀ axis angle mass energy px py pz z,
    v34DiracResidual mass energy
        (v35FiniteRotationMomentum axis angle px py pz 0)
        (v35FiniteRotationMomentum axis angle px py pz 1)
        (v35FiniteRotationMomentum axis angle px py pz 2)
        (standardCubicalContinuousTurn angle axis z) =
      standardCubicalContinuousTurn angle axis
        (v34DiracResidual mass energy px py pz z)
  generatedCovariance : ∀ word mass state z,
    v35ResidualAt mass (v35ApplyKinematicWord word state)
        (v35ApplyLorentzWord word z) =
      v35ApplyLorentzWord word (v35ResidualAt mass state z)
  generatedSolutions : ∀ word mass state z,
    v35ResidualAt mass state z = 0 →
      v35ResidualAt mass (v35ApplyKinematicWord word state)
          (v35ApplyLorentzWord word z) = 0

theorem v35_covariant_solution_transport :
    V35CovariantSolutionTransportCertificate where
  massShell := v35_finite_boost_mass_shell
  rotationNorm := v35_finite_rotation_momentum_norm
  covariance := v35_finite_boost_covariant
  rotationCovariance := v35_finite_rotation_covariant
  generatedCovariance := v35_lorentz_word_covariant
  generatedSolutions := v35_lorentz_word_preserves_solutions

end
end LeanDirac.V2
