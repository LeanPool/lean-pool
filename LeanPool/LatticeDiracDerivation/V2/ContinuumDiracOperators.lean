/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CubicalClifford
public import LeanPool.LatticeDiracDerivation.V2.C19Fourier

/-! # Continuum Dirac operators and plane waves -/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

/-- The Dirac transport matrix associated with the chosen axis. -/
def cubicalVelocityOperator (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  fun component => (c19ContinuumSpeed : ℂ) * cubicalAlpha axis z component

/-- The transport operator as a scaled massless Hamiltonian in a coordinate direction. -/
def cubicalVelocityLinear (axis : Fin 3) : CubicalCell4 →ₗ[ℂ] CubicalCell4 :=
  let px : ℂ := if axis = 0 then 1 else 0
  let py : ℂ := if axis = 1 then 1 else 0
  let pz : ℂ := if axis = 2 then 1 else 0
  (c19ContinuumSpeed : ℂ) •
    { toFun := cubicalStandardHamiltonian 0 px py pz
      map_add' := cubical_standard_hamiltonian_add 0 px py pz
      map_smul' := cubical_standard_hamiltonian_scale 0 px py pz }

theorem cubical_velocity_linear_apply (axis : Fin 3) (z : CubicalCell4) :
    cubicalVelocityLinear axis z = cubicalVelocityOperator axis z := by
  funext component
  fin_cases axis <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      cubicalVelocityLinear, cubicalVelocityOperator, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalAlpha, LinearMap.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, Fin.reduceEq, ↓reduceIte,
      zero_mul, one_mul, zero_add, add_zero]

theorem cubical_velocity_sum {Mode : Type*} [Fintype Mode]
    (axis : Fin 3) (field : Mode → CubicalCell4) :
    cubicalVelocityOperator axis
        (fun component => ∑ mode, field mode component) =
      fun component => ∑ mode,
        cubicalVelocityOperator axis (field mode) component := by
  have pointwise : (fun component => ∑ mode, field mode component) = ∑ mode, field mode := by
    funext component
    rw [Finset.sum_apply]
  rw [pointwise]
  funext component
  simpa only [cubical_velocity_linear_apply, Finset.sum_apply] using
    congrFun (map_sum (cubicalVelocityLinear axis) field Finset.univ) component

theorem cubical_velocity_mul (axis : Fin 3) (scale : ℂ) (spinor : CubicalCell4) :
    cubicalVelocityOperator axis (fun component => scale * spinor component) =
      fun component => scale * cubicalVelocityOperator axis spinor component := by
  change cubicalVelocityOperator axis (scale • spinor) = scale • cubicalVelocityOperator axis spinor
  simpa only [cubical_velocity_linear_apply] using
    (cubicalVelocityLinear axis).map_smul scale spinor

/-- The mode time evolution given by minus the imaginary unit times the Hamiltonian. -/
def cubicalDiracTimeDerivative
    (mass : ℝ) (z : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) : CubicalCell4 :=
  fun component =>
    -I * (mass : ℂ) * cubicalStandardBeta z component -
      ∑ axis : Fin 3,
        cubicalVelocityOperator axis
          (spatialDerivative axis) component

/-- The spatial derivative of a plane wave at the specified physical momentum. -/
def uniformPlaneWaveSpatialDerivative
    (momentum : LatticeMomentum) (z : CubicalCell4) :
    Fin 3 → CubicalCell4 :=
  fun axis component => I * (momentum axis : ℂ) * z component

/-- The Hamiltonian and position-space forms agree for arbitrary
four-component data; this lemma is independent of how the data were read out. -/
theorem cubical_standard_hamiltonian_is_position_dirac
    (mass : ℝ) (momentum : LatticeMomentum) (z : CubicalCell4) :
    (fun component =>
      -I * cubicalStandardHamiltonian (mass : ℂ)
        (c19ScaledMomentum momentum 0 : ℂ)
        (c19ScaledMomentum momentum 1 : ℂ)
        (c19ScaledMomentum momentum 2 : ℂ) z component) =
      cubicalDiracTimeDerivative mass z
        (uniformPlaneWaveSpatialDerivative momentum z) := by
  funext component
  have velocity (axis : Fin 3) :
      cubicalVelocityOperator axis (uniformPlaneWaveSpatialDerivative momentum z axis) component =
        (I * (momentum axis : ℂ)) * cubicalVelocityOperator axis z component :=
    congrFun (cubical_velocity_mul axis (I * (momentum axis : ℂ)) z) component
  simp only [cubicalDiracTimeDerivative, velocity]
  simp only [Fin.sum_univ_three, cubicalVelocityOperator, cubicalAlpha,
    c19ScaledMomentum,
    Complex.ofReal_mul, cubicalStandardHamiltonian, cubicalStandardSpatial]
  ring

end
end LeanDirac.V2
