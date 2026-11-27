/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit e2161e0936f181d4a5a9d49963a666f7cea42502.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V32FiniteLorentz

/-! # V3.2 Stage 8: discrete symmetries of the derived representation -/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The V3.2 P ar it y definition used by this stage. -/
def v32Parity (z : CubicalCell4) : CubicalCell4 := cubicalStandardBeta z

/-- The V3.2 C ha rg eC on ju ga te definition used by this stage. -/
def v32ChargeConjugate (z : CubicalCell4) : CubicalCell4
  | 0 => starRingEnd ℂ (z 3)
  | 1 => -starRingEnd ℂ (z 2)
  | 2 => -starRingEnd ℂ (z 1)
  | _ => starRingEnd ℂ (z 0)

/-- The V3.2 T im eR ev er se definition used by this stage. -/
def v32TimeReverse (z : CubicalCell4) : CubicalCell4
  | 0 => starRingEnd ℂ (z 1)
  | 1 => -starRingEnd ℂ (z 0)
  | 2 => starRingEnd ℂ (z 3)
  | _ => -starRingEnd ℂ (z 2)

/-- The V3.2 C PT definition used by this stage. -/
def v32CPT (z : CubicalCell4) : CubicalCell4 :=
  v32ChargeConjugate (v32Parity (v32TimeReverse z))

theorem v32_parity_square (z : CubicalCell4) :
    v32Parity (v32Parity z) = z := by
  funext component
  fin_cases component <;> simp [v32Parity, cubicalStandardBeta]

theorem v32_charge_conjugation_square (z : CubicalCell4) :
    v32ChargeConjugate (v32ChargeConjugate z) = z := by
  funext component
  fin_cases component <;> simp [v32ChargeConjugate]

theorem v32_time_reversal_square (z : CubicalCell4) :
    v32TimeReverse (v32TimeReverse z) = fun component => -z component := by
  funext component
  fin_cases component <;> simp [v32TimeReverse]

theorem v32_parity_hamiltonian
    (mass px py pz : ℝ) (z : CubicalCell4) :
    v32Parity (v32ContinuumHamiltonian mass px py pz z) =
      v32ContinuumHamiltonian mass (-px) (-py) (-pz) (v32Parity z) := by
  funext component
  fin_cases component <;>
    simp [v32Parity, v32ContinuumHamiltonian,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring

theorem v32_time_reversal_hamiltonian
    (mass px py pz : ℝ) (z : CubicalCell4) :
    v32TimeReverse (v32ContinuumHamiltonian mass px py pz z) =
      v32ContinuumHamiltonian mass (-px) (-py) (-pz) (v32TimeReverse z) := by
  funext component
  fin_cases component <;>
    simp [v32TimeReverse, v32ContinuumHamiltonian,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      map_add, map_mul] <;> ring

theorem v32_charge_conjugation_hamiltonian
    (mass px py pz : ℝ) (z : CubicalCell4) :
    v32ChargeConjugate (v32ContinuumHamiltonian mass px py pz z) =
      fun component =>
        -v32ContinuumHamiltonian mass (-px) (-py) (-pz)
          (v32ChargeConjugate z) component := by
  funext component
  fin_cases component <;>
    simp [v32ChargeConjugate, v32ContinuumHamiltonian,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      map_add, map_mul] <;> ring

theorem v32_cpt_square (z : CubicalCell4) :
    v32CPT (v32CPT z) = z := by
  funext component
  fin_cases component <;>
    simp [v32CPT, v32ChargeConjugate, v32Parity,
      v32TimeReverse, cubicalStandardBeta]

theorem v32_cpt_hamiltonian
    (mass px py pz : ℝ) (z : CubicalCell4) :
    v32CPT (v32ContinuumHamiltonian mass px py pz z) =
      fun component =>
        -v32ContinuumHamiltonian mass (-px) (-py) (-pz)
          (v32CPT z) component := by
  funext component
  fin_cases component <;>
    simp [v32CPT, v32ChargeConjugate, v32Parity,
      v32TimeReverse, v32ContinuumHamiltonian,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      map_add, map_mul] <;> ring

theorem v32_cpt_preserves_density (z : CubicalCell4) :
    cubicalCell4Density (v32CPT z) = cubicalCell4Density z := by
  simp [cubicalCell4Density, v32CPT, v32ChargeConjugate,
    v32Parity, v32TimeReverse, cubicalStandardBeta,
    Complex.normSq, Fin.sum_univ_four]
  ring

theorem v32_cpt_commutes_spin
    (axis : Fin 3) (z : CubicalCell4) :
    v32CPT (standardCubicalSpin axis z) =
      standardCubicalSpin axis (v32CPT z) := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [v32CPT, v32ChargeConjugate, v32Parity,
      v32TimeReverse, cubicalStandardBeta, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, map_mul]

/-- The bundled V3.2 D is cr et eS ym me tr yC er ti fi ca te. -/
structure V32DiscreteSymmetryCertificate : Prop where
  paritySquare : ∀ z, v32Parity (v32Parity z) = z
  chargeSquare : ∀ z, v32ChargeConjugate (v32ChargeConjugate z) = z
  timeSquare : ∀ z,
    v32TimeReverse (v32TimeReverse z) = fun component => -z component
  parityCovariance : ∀ mass px py pz z,
    v32Parity (v32ContinuumHamiltonian mass px py pz z) =
      v32ContinuumHamiltonian mass (-px) (-py) (-pz) (v32Parity z)
  timeCovariance : ∀ mass px py pz z,
    v32TimeReverse (v32ContinuumHamiltonian mass px py pz z) =
      v32ContinuumHamiltonian mass (-px) (-py) (-pz) (v32TimeReverse z)
  chargeBranchExchange : ∀ mass px py pz z,
    v32ChargeConjugate (v32ContinuumHamiltonian mass px py pz z) =
      fun component =>
        -v32ContinuumHamiltonian mass (-px) (-py) (-pz)
          (v32ChargeConjugate z) component
  cptSquare : ∀ z, v32CPT (v32CPT z) = z
  cptCovariance : ∀ mass px py pz z,
    v32CPT (v32ContinuumHamiltonian mass px py pz z) =
      fun component =>
        -v32ContinuumHamiltonian mass (-px) (-py) (-pz)
          (v32CPT z) component
  cptDensity : ∀ z,
    cubicalCell4Density (v32CPT z) = cubicalCell4Density z
  cptSpin : ∀ axis z,
    v32CPT (standardCubicalSpin axis z) =
      standardCubicalSpin axis (v32CPT z)

theorem v32_discrete_symmetries : V32DiscreteSymmetryCertificate where
  paritySquare := v32_parity_square
  chargeSquare := v32_charge_conjugation_square
  timeSquare := v32_time_reversal_square
  parityCovariance := v32_parity_hamiltonian
  timeCovariance := v32_time_reversal_hamiltonian
  chargeBranchExchange := v32_charge_conjugation_hamiltonian
  cptSquare := v32_cpt_square
  cptCovariance := v32_cpt_hamiltonian
  cptDensity := v32_cpt_preserves_density
  cptSpin := v32_cpt_commutes_spin


end
end LeanDirac.V2
