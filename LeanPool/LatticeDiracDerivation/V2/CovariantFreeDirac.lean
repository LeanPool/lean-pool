/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumCurrentBridge

/-!
# Covariant coordinates for the cube-derived free Dirac equation

The cubical incidence construction first supplies `beta` and the three
Hamiltonian `alpha` operators.  This file derives the covariant gamma
operators from them and proves both the Minkowski Clifford relations and the
equivalence between Hamiltonian and covariant forms.  No independent gamma
matrices are assumed.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

/-- The time-like gamma operator is the cubical degree grading. -/
def cubicalGammaTime (z : CubicalCell4) : CubicalCell4 :=
  cubicalStandardBeta z

/-- Coordinate form of the incidence-derived spatial alpha operator. -/
def cubicalAlpha (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  match axis with
  | 0 => cubicalStandardAlphaX z
  | 1 => cubicalStandardAlphaY z
  | _ => cubicalStandardAlphaZ z

/-- `gamma^j = beta alpha^j`, derived from the same cubical operators. -/
def cubicalGammaSpace (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  cubicalGammaTime (cubicalAlpha axis z)

theorem cubical_gamma_time_square (z : CubicalCell4) :
    cubicalGammaTime (cubicalGammaTime z) = z := by
  funext component
  fin_cases component <;>
    simp [cubicalGammaTime, cubicalStandardBeta]

theorem cubical_gamma_space_square (axis : Fin 3) (z : CubicalCell4) :
    cubicalGammaSpace axis (cubicalGammaSpace axis z) =
      fun component => -z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalGammaSpace, cubicalGammaTime, cubicalAlpha,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_gamma_time_space_anticommute
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalGammaTime (cubicalGammaSpace axis z) =
      fun component =>
        -cubicalGammaSpace axis (cubicalGammaTime z) component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalGammaSpace, cubicalGammaTime, cubicalAlpha,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ]

theorem cubical_gamma_space_anticommute
    (axis other : Fin 3) (haxis : axis ≠ other) (z : CubicalCell4) :
    cubicalGammaSpace axis (cubicalGammaSpace other z) =
      fun component =>
        -cubicalGammaSpace other (cubicalGammaSpace axis z) component := by
  funext component
  fin_cases axis <;> fin_cases other <;> try { contradiction }
  all_goals
    fin_cases component <;>
      simp [cubicalGammaSpace, cubicalGammaTime, cubicalAlpha,
        cubicalStandardBeta, cubicalStandardAlphaX,
        cubicalStandardAlphaY, cubicalStandardAlphaZ]

/-- The displayed covariant residual
`(i gamma ^ 0 d_t + i c gamma^j d_j - m) z`. -/
def cubicalCovariantDiracResidual
    (mass : ℝ) (z timeDerivative : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) : CubicalCell4 :=
  fun component =>
    I * cubicalGammaTime timeDerivative component +
      I * ∑ axis : Fin 3,
        (c19ContinuumSpeed : ℂ) *
          cubicalGammaSpace axis (spatialDerivative axis) component -
      (mass : ℂ) * z component

/-- Multiplying the covariant residual by `gamma ^ 0` recovers exactly `i`
times the difference between the proposed time derivative and the already
derived Hamiltonian evolution. -/
theorem cubical_gamma_time_covariant_residual
    (mass : ℝ) (z timeDerivative : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) :
    cubicalGammaTime
        (cubicalCovariantDiracResidual mass z timeDerivative
          spatialDerivative) =
      fun component =>
        I * (timeDerivative component -
          cubicalDiracTimeDerivative mass z spatialDerivative component) := by
  funext component
  fin_cases component <;>
    simp [cubicalGammaTime, cubicalCovariantDiracResidual,
      cubicalGammaSpace, cubicalAlpha, cubicalDiracTimeDerivative,
      cubicalVelocityOperator, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, Fin.sum_univ_succ] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- Hamiltonian and covariant free-Dirac equations are equivalent, with all
operators inherited from the cubical incidence construction. -/
theorem cubical_hamiltonian_iff_covariant_dirac
    (mass : ℝ) (z timeDerivative : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) :
    timeDerivative = cubicalDiracTimeDerivative mass z spatialDerivative ↔
      cubicalCovariantDiracResidual mass z timeDerivative
        spatialDerivative = fun _ => 0 := by
  constructor
  · intro htime
    subst timeDerivative
    have hgamma := cubical_gamma_time_covariant_residual
      mass z (cubicalDiracTimeDerivative mass z spatialDerivative)
        spatialDerivative
    have hzero : cubicalGammaTime
        (cubicalCovariantDiracResidual mass z
          (cubicalDiracTimeDerivative mass z spatialDerivative)
          spatialDerivative) = fun _ => 0 := by
      simpa using hgamma
    have hinvert := congrArg cubicalGammaTime hzero
    rw [cubical_gamma_time_square] at hinvert
    have hgammaZero : cubicalGammaTime (fun _ => 0) = fun _ => 0 := by
      funext component
      fin_cases component <;>
        simp [cubicalGammaTime, cubicalStandardBeta]
    rw [hgammaZero] at hinvert
    exact hinvert
  · intro hresidual
    funext component
    have hgamma := congrArg cubicalGammaTime hresidual
    rw [cubical_gamma_time_covariant_residual] at hgamma
    have hgammaZero : cubicalGammaTime (fun _ => 0) = fun _ => 0 := by
      funext output
      fin_cases output <;>
        simp [cubicalGammaTime, cubicalStandardBeta]
    rw [hgammaZero] at hgamma
    have hcomponent := congrFun hgamma component
    have hcomponent0 :
        I * (timeDerivative component -
          cubicalDiracTimeDerivative mass z spatialDerivative component) = 0 := by
      exact hcomponent
    have hdifference :
        timeDerivative component -
          cubicalDiracTimeDerivative mass z spatialDerivative component = 0 :=
      (mul_eq_zero.mp hcomponent0).resolve_left Complex.I_ne_zero
    exact sub_eq_zero.mp hdifference

/-- The Clifford relations and the covariant form of the cube-derived free Dirac equation. -/
structure CovariantFreeDiracCertificate : Prop where
  timeSquare : ∀ z,
    cubicalGammaTime (cubicalGammaTime z) = z
  spaceSquare : ∀ axis z,
    cubicalGammaSpace axis (cubicalGammaSpace axis z) =
      fun component => -z component
  timeSpaceAnticommute : ∀ axis z,
    cubicalGammaTime (cubicalGammaSpace axis z) =
      fun component =>
        -cubicalGammaSpace axis (cubicalGammaTime z) component
  spaceAnticommute : ∀ axis other,
    axis ≠ other → ∀ z,
      cubicalGammaSpace axis (cubicalGammaSpace other z) =
        fun component =>
          -cubicalGammaSpace other (cubicalGammaSpace axis z) component
  equationEquivalent : ∀ mass z timeDerivative spatialDerivative,
    timeDerivative = cubicalDiracTimeDerivative mass z spatialDerivative ↔
      cubicalCovariantDiracResidual mass z timeDerivative
        spatialDerivative = fun _ => 0

theorem covariant_free_dirac : CovariantFreeDiracCertificate where
  timeSquare := cubical_gamma_time_square
  spaceSquare := cubical_gamma_space_square
  timeSpaceAnticommute := cubical_gamma_time_space_anticommute
  spaceAnticommute := cubical_gamma_space_anticommute
  equationEquivalent := cubical_hamiltonian_iff_covariant_dirac

end
end LeanDirac.V2
