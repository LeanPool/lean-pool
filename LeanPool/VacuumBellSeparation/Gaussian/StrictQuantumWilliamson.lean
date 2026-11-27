/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteGaussianRealization

/-!
# Strict uncertainty gives a faithful actual Gaussian density

Strict positivity of the literal finite uncertainty matrix is transported
using the actual inverse Williamson coordinates. The mode vector `(1,i)`
then forces each variance strictly above `1/2`. The resulting density is
injective on the full occupation Hilbert space. No bounded inverse for
that infinite-dimensional density is asserted.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem half_lt_of_quantum_mode_posDef (ν : ι → ℝ)
    (h : (quantumCovariance (modeDiagonal ν) modeSymplecticForm).PosDef) :
    ∀ i, (1 : ℝ) / 2 < ν i := by
  intro i
  have hblock := h.submatrix (e := fun a : Fin 2 => (i, a))
    (fun a b hab => congrArg Prod.snd hab)
  rw [quantumModeBlock] at hblock
  have hx : (![1, Complex.I] : Fin 2 → ℂ) ≠ 0 := by
    intro hx
    have hz := congrFun hx 0
    simp at hz
  have ht := hblock.dotProduct_mulVec_pos hx
  have hr := (Complex.pos_iff.mp ht).1
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] at hr
  linarith

omit [DecidableEq ι] in
theorem strict_quantum_williamson_variances {m : ℕ}
    (V Ω : Matrix ι ι ℝ) (ν : Fin m → ℝ)
    (S : Matrix ι (Fin m × Fin 2) ℝ) (T : Matrix (Fin m × Fin 2) ι ℝ)
    (hTS : T * S = 1) (hsymp : S * (modeSymplecticForm (ι := Fin m)) * Sᵀ = Ω)
    (hcov : S * modeDiagonal ν * Sᵀ = V)
    (hquantum : (quantumCovariance V Ω).PosDef) : ∀ j, 1 / 2 < ν j := by
  have hCTS : complexifyMatrix T * complexifyMatrix S = 1 := by
    rw [← complexifyMatrix_mul, hTS, complexifyMatrix_one]
  have hinj : Function.Injective (complexifyMatrix T).vecMul := by
    intro x y hxy
    have h := congrArg (fun z => z ᵥ* complexifyMatrix S) hxy
    simpa only [Matrix.vecMul_vecMul, hCTS, Matrix.vecMul_one] using h
  have hinv_cov : T * V * Tᵀ = modeDiagonal ν := by
    calc
      T * V * Tᵀ = (T * S) * modeDiagonal ν * (T * S)ᵀ := by
        rw [← hcov]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = modeDiagonal ν := by simp only [hTS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hinv_symp : T * Ω * Tᵀ = (modeSymplecticForm (ι := Fin m)) := by
    calc
      T * Ω * Tᵀ = (T * S) * (modeSymplecticForm (ι := Fin m)) * (T * S)ᵀ := by
        rw [← hsymp]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (modeSymplecticForm (ι := Fin m)) := by
        simp only [hTS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hnormal := hquantum.mul_mul_conjTranspose_same hinj
  rw [← quantumCovariance_congruence, hinv_cov, hinv_symp] at hnormal
  exact half_lt_of_quantum_mode_posDef ν hnormal

/-- Strict uncertainty produces an actual faithful density with the
specified covariance characteristic and Weyl phase. -/
theorem exists_faithful_finite_gaussian_realization (V Ω : Matrix ι ι ℝ)
    (hV : V.PosDef) (hΩ : Ωᵀ = -Ω) (hΩunit : IsUnit Ω)
    (hquantum : (quantumCovariance V Ω).PosDef) :
    ∃ (m : ℕ) (ν : Fin m → ℝ) (hν : ∀ j, 1 / 2 < ν j)
      (S : Matrix ι (Fin m × Fin 2) ℝ) (T : Matrix (Fin m × Fin 2) ι ℝ),
      Fintype.card ι = 2 * m ∧ S * T = 1 ∧ T * S = 1 ∧
      IsFaithfulDensity (covarianceProductDensity ν) ∧
      (∀ x, finiteGaussianWeyl S x ∈
        unitary (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)) ∧
      (∀ x y, finiteGaussianWeyl S x * finiteGaussianWeyl S y =
        Complex.exp (-(Complex.I * (((x ⬝ᵥ (Ω *ᵥ y)) / 2 : ℝ) : ℂ))) •
          finiteGaussianWeyl S (x + y)) ∧
      (∀ x, covarianceProductState (fun j => (hν j).le) (finiteGaussianWeyl S x) =
        Complex.exp ((-(1 / 2) * (x ⬝ᵥ (V *ᵥ x)) : ℝ) : ℂ)) := by
  obtain ⟨m, ν, S, T, hcard, _, hST, hTS, hsymp, hcov⟩ :=
    exists_quantum_williamson_factorization V Ω hV hΩ hΩunit hquantum.posSemidef
  have hν := strict_quantum_williamson_variances V Ω ν S T hTS hsymp hcov hquantum
  exact ⟨m, ν, hν, S, T, hcard, hST, hTS, covarianceProductDensity_isFaithfulDensity hν,
    finiteGaussianWeyl_mem_unitary S, finiteGaussianWeyl_mul S Ω hsymp,
    covarianceProductState_finiteGaussianWeyl (fun j => (hν j).le) S V hcov⟩

end VacuumBellSeparation.Gaussian
