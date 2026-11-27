/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureMatrices
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumWilliamson
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeFaithfulness

/-!
# A concrete finite Gaussian realization for every admissible covariance

The Hilbert space is the actual full occupation space. The density is the
actual product thermal density, and the Weyl labels are transformed by
the transpose of the proved Williamson matrix. Their characteristic is
literally `exp (-ξᵀ V ξ / 2)` and their multiplication phase is literally
`exp (-i ξᵀ Ω η / 2)`. The state agrees with the positive density trace on
positive square-root sandwiches.

This constructs a Gaussian representation of the specified real phase
space.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Finite Gaussian Weyl given by `multiQuadratureWeyl (modeQuadratureTuple (Sᵀ *ᵥ x))`. -/
def finiteGaussianWeyl (S : Matrix ι (Fin m × Fin 2) ℝ) (x : ι → ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  multiQuadratureWeyl (modeQuadratureTuple (Sᵀ *ᵥ x))

/-- Covariance product state. -/
def covarianceProductState {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) :
    State (MultiModeOscillatorSpace m) :=
  multiThermalState (fun j => covarianceThermalParameter_nonneg (hν j))
    (fun j => covarianceThermalParameter_lt_one (hν j))

omit [DecidableEq ι] in
theorem finiteGaussianWeyl_mem_unitary (S : Matrix ι (Fin m × Fin 2) ℝ) (x : ι → ℝ) :
    finiteGaussianWeyl S x ∈
      unitary (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  multiQuadratureWeyl_mem_unitary _

omit [DecidableEq ι] in
/-- Literal Weyl multiplication for the transformed real phase space. -/
theorem finiteGaussianWeyl_mul (S : Matrix ι (Fin m × Fin 2) ℝ)
    (Ω : Matrix ι ι ℝ)
    (hΩ : (S * modeSymplecticForm : Matrix ι (Fin m × Fin 2) ℝ) * Sᵀ = Ω)
    (x y : ι → ℝ) :
    finiteGaussianWeyl S x * finiteGaussianWeyl S y =
      Complex.exp (-(Complex.I * (((x ⬝ᵥ (Ω *ᵥ y)) / 2 : ℝ) : ℂ))) •
        finiteGaussianWeyl S (x + y) := by
  subst Ω
  simp only [finiteGaussianWeyl, multiQuadratureWeyl_mul,
    Matrix.mulVec_add, modeQuadratureTuple_add]
  rw [← dotProduct_modeSymplecticForm, dotProduct_congruence]

omit [DecidableEq ι] in
/-- The characteristic of the actual density state has the prescribed
covariance after the genuine Williamson coordinate change. -/
theorem covarianceProductState_finiteGaussianWeyl {ν : Fin m → ℝ}
    (hν : ∀ j, 1 / 2 ≤ ν j) (S : Matrix ι (Fin m × Fin 2) ℝ)
    (V : Matrix ι ι ℝ) (hV : S * modeDiagonal ν * Sᵀ = V) (x : ι → ℝ) :
    covarianceProductState hν (finiteGaussianWeyl S x) =
      Complex.exp ((-(1 / 2) * (x ⬝ᵥ (V *ᵥ x)) : ℝ) : ℂ) := by
  rw [covarianceProductState, finiteGaussianWeyl, multiThermalState_quadratureWeyl]
  simp only [thermalQuadratureVariance_covarianceParameter (hν _), modeQuadratureTuple]
  rw [← dotProduct_modeDiagonal, dotProduct_congruence, hV]

/-- The constructed complex state is the actual density functional on
positive operators, where the positive extended trace is applicable. -/
theorem positiveTrace_covarianceProduct_sandwich {ν : Fin m → ℝ}
    (hν : ∀ j, 1 / 2 ≤ ν j)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    positiveTrace (CFC.sqrt (covarianceProductDensity ν) * A *
      CFC.sqrt (covarianceProductDensity ν)) =
        ENNReal.ofReal (covarianceProductState hν A).re :=
  positiveTrace_multiThermal_sandwich
    (fun j => covarianceThermalParameter_nonneg (hν j))
    (fun j => covarianceThermalParameter_lt_one (hν j)) hA

/-- Quantum uncertainty supplies an actual finite Gaussian realization.
The matrix inverse and dimension relation are retained explicitly. -/
theorem exists_finite_gaussian_realization (V Ω : Matrix ι ι ℝ)
    (hV : V.PosDef) (hΩ : Ωᵀ = -Ω) (hΩunit : IsUnit Ω)
    (hquantum : (quantumCovariance V Ω).PosSemidef) :
    ∃ (m : ℕ) (ν : Fin m → ℝ) (hν : ∀ j, 1 / 2 ≤ ν j)
      (S : Matrix ι (Fin m × Fin 2) ℝ) (T : Matrix (Fin m × Fin 2) ι ℝ),
      Fintype.card ι = 2 * m ∧ S * T = 1 ∧ T * S = 1 ∧
      0 ≤ covarianceProductDensity ν ∧ positiveTrace (covarianceProductDensity ν) = 1 ∧
      (∀ x, finiteGaussianWeyl S x ∈
        unitary (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)) ∧
      (∀ x y, finiteGaussianWeyl S x * finiteGaussianWeyl S y =
        Complex.exp (-(Complex.I * (((x ⬝ᵥ (Ω *ᵥ y)) / 2 : ℝ) : ℂ))) •
          finiteGaussianWeyl S (x + y)) ∧
      (∀ x, covarianceProductState hν (finiteGaussianWeyl S x) =
        Complex.exp ((-(1 / 2) * (x ⬝ᵥ (V *ᵥ x)) : ℝ) : ℂ)) := by
  obtain ⟨m, ν, S, T, hcard, hν, hST, hTS, hsymp, hcov⟩ :=
    exists_quantum_williamson_factorization V Ω hV hΩ hΩunit hquantum
  exact ⟨m, ν, hν, S, T, hcard, hST, hTS, covarianceProductDensity_nonneg hν,
    positiveTrace_covarianceProductDensity hν, finiteGaussianWeyl_mem_unitary S,
    finiteGaussianWeyl_mul S Ω hsymp,
    covarianceProductState_finiteGaussianWeyl hν S V hcov⟩

end VacuumBellSeparation.Gaussian
