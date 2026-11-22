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

/-- `gamma^j = beta alpha^j`, derived from the same cubical operators. -/
def cubicalGammaSpace (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  cubicalGammaTime (cubicalAlpha axis z)

private def cubicalSpatialSign (axis : Fin 3) : ℂ := if axis = 2 then 1 else -1

private theorem cubical_spatial_sign_square (axis : Fin 3) :
    cubicalSpatialSign axis * cubicalSpatialSign axis = 1 := by
  unfold cubicalSpatialSign
  split <;> simp

private theorem cubical_alpha_eq_oriented_axis (axis : Fin 3) (z : CubicalCell4) :
    cubicalAlpha axis z = cubicalSpatialSign axis • cubicalStandardAxis axis.rev z := by
  have rev_zero : (0 : Fin 3).rev = 2 := rfl
  have rev_one : (1 : Fin 3).rev = 1 := rfl
  have rev_two : (2 : Fin 3).rev = 0 := rfl
  fin_cases axis <;> simp [cubicalAlpha, cubicalSpatialSign, cubicalStandardAxis,
    rev_zero, rev_one, rev_two]

private theorem cubical_gamma_scale (axis : Fin 3) (scalar : ℂ) (z : CubicalCell8) :
    cubicalGamma axis (scalar • z) = scalar • cubicalGamma axis z := by
  funext corner
  simp [cubicalGamma, Pi.smul_apply, smul_eq_mul, mul_left_comm]

private theorem cubical_beta_scale (scalar : ℂ) (z : CubicalCell8) :
    cubicalBeta (scalar • z) = scalar • cubicalBeta z := by
  funext corner
  unfold cubicalBeta
  simp only [Pi.smul_apply]
  split <;> simp only [smul_neg]

private theorem cubical_gamma_space_embedding (axis : Fin 3) (z : CubicalCell4) :
    cubicalDiracEmbedMinus (cubicalGammaSpace axis z) =
      cubicalSpatialSign axis • cubicalBeta (cubicalGamma axis.rev (cubicalDiracEmbedMinus z)) := by
  unfold cubicalGammaSpace cubicalGammaTime
  rw [← cubical_beta_intertwines_minus, cubical_alpha_eq_oriented_axis]
  change cubicalBeta (cubicalDiracLinearEmbedMinus (_ • _)) = _
  rw [map_smul, cubical_beta_scale]
  change _ • cubicalBeta (cubicalDiracEmbedMinus _) = _
  rw [cubical_gamma_intertwines_minus]

private theorem cubical_beta_gamma_beta (axis : Fin 3) (z : CubicalCell8) :
    cubicalBeta (cubicalGamma axis (cubicalBeta z)) = -cubicalGamma axis z := by
  rw [cubical_beta_anticommutes, cubical_beta_square]
  rfl

private theorem cubical_gamma_space_product_embedding (axis other : Fin 3) (z : CubicalCell4) :
    cubicalDiracEmbedMinus (cubicalGammaSpace axis (cubicalGammaSpace other z)) =
      -(cubicalSpatialSign axis * cubicalSpatialSign other) •
        cubicalGamma axis.rev (cubicalGamma other.rev (cubicalDiracEmbedMinus z)) := by
  rw [cubical_gamma_space_embedding, cubical_gamma_space_embedding,
    cubical_gamma_scale, cubical_beta_scale, smul_smul, cubical_beta_gamma_beta, smul_neg, neg_smul]

theorem cubical_gamma_time_square (z : CubicalCell4) :
    cubicalGammaTime (cubicalGammaTime z) = z := by
  apply cubical_dirac_embed_minus_injective
  simpa only [cubicalGammaTime, ← cubical_beta_intertwines_minus] using
    cubical_beta_square (cubicalDiracEmbedMinus z)

theorem cubical_gamma_space_square (axis : Fin 3) (z : CubicalCell4) :
    cubicalGammaSpace axis (cubicalGammaSpace axis z) =
      fun component => -z component := by
  apply cubical_dirac_embed_minus_injective
  change _ = cubicalDiracLinearEmbedMinus (-z)
  rw [map_neg]
  change _ = -cubicalDiracEmbedMinus z
  rw [cubical_gamma_space_product_embedding, cubical_spatial_sign_square,
    cubical_gamma_square, neg_smul, one_smul]

theorem cubical_gamma_time_space_anticommute
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalGammaTime (cubicalGammaSpace axis z) =
      fun component =>
        -cubicalGammaSpace axis (cubicalGammaTime z) component := by
  apply cubical_dirac_embed_minus_injective
  change cubicalDiracEmbedMinus (cubicalStandardBeta (cubicalGammaSpace axis z)) =
    cubicalDiracLinearEmbedMinus (-cubicalGammaSpace axis (cubicalStandardBeta z))
  rw [map_neg]
  change _ = -cubicalDiracEmbedMinus _
  rw [← cubical_beta_intertwines_minus, cubical_gamma_space_embedding,
    cubical_gamma_space_embedding, ← cubical_beta_intertwines_minus, cubical_beta_scale,
    cubical_beta_square, cubical_beta_gamma_beta, smul_neg, neg_neg]

theorem cubical_gamma_space_anticommute
    (axis other : Fin 3) (haxis : axis ≠ other) (z : CubicalCell4) :
    cubicalGammaSpace axis (cubicalGammaSpace other z) =
      fun component =>
        -cubicalGammaSpace other (cubicalGammaSpace axis z) component := by
  apply cubical_dirac_embed_minus_injective
  change _ = cubicalDiracLinearEmbedMinus (-cubicalGammaSpace other (cubicalGammaSpace axis z))
  rw [map_neg]
  change _ = -cubicalDiracEmbedMinus _
  have anti : cubicalGamma axis.rev (cubicalGamma other.rev (cubicalDiracEmbedMinus z)) =
      -cubicalGamma other.rev (cubicalGamma axis.rev (cubicalDiracEmbedMinus z)) :=
    cubical_gamma_anticommute axis.rev other.rev (Fin.rev_injective.ne haxis)
      (cubicalDiracEmbedMinus z)
  rw [cubical_gamma_space_product_embedding, cubical_gamma_space_product_embedding,
    mul_comm (cubicalSpatialSign axis) (cubicalSpatialSign other), anti, smul_neg]

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
  let sign : ℂ := if component.val < 2 then 1 else -1
  have beta (field : CubicalCell4) : cubicalGammaTime field component = sign * field component := by
    fin_cases component <;> simp [sign, cubicalGammaTime, cubicalStandardBeta]
  have time_square := congrFun (cubical_gamma_time_square timeDerivative) component
  change cubicalGammaTime (cubicalGammaTime timeDerivative) component = _ at time_square
  rw [beta] at time_square
  have spatial (axis : Fin 3) :
      sign * ((c19ContinuumSpeed : ℂ) * cubicalGammaSpace axis (spatialDerivative axis) component) =
        cubicalVelocityOperator axis (spatialDerivative axis) component := by
    have square := congrFun
      (cubical_gamma_time_square (cubicalAlpha axis (spatialDerivative axis))) component
    change cubicalGammaTime (cubicalGammaSpace axis (spatialDerivative axis)) component =
      _ at square
    rw [beta] at square
    change _ = (c19ContinuumSpeed : ℂ) * cubicalAlpha axis (spatialDerivative axis) component
    rw [← square]
    ring
  have spatial_sum :
      sign * (I * ∑ axis : Fin 3, (c19ContinuumSpeed : ℂ) *
        cubicalGammaSpace axis (spatialDerivative axis) component) =
        I * ∑ axis : Fin 3, cubicalVelocityOperator axis (spatialDerivative axis) component := by
    rw [mul_left_comm sign I, Finset.mul_sum]
    simp_rw [spatial]
  rw [beta]
  simp only [cubicalCovariantDiracResidual, cubicalDiracTimeDerivative, mul_add, mul_sub]
  rw [mul_left_comm sign I, spatial_sum, time_square]
  change _ = I * timeDerivative component -
    (I * (-I * (mass : ℂ) * cubicalGammaTime z component) -
      I * ∑ axis, cubicalVelocityOperator axis (spatialDerivative axis) component)
  rw [beta]
  linear_combination -(mass : ℂ) * (sign * z component) * Complex.I_sq

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
