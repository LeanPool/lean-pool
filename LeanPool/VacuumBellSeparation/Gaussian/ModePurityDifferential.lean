/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FaithfulPurityDerivative
public import LeanPool.VacuumBellSeparation.Gaussian.MatrixTraceNormDiagonal

/-!
# The actual aggregate purity differential in Williamson coordinates

The odd CFC slope is computed through the actual absolute Hamiltonian.
A trace identity and the genuine Sylvester inverse then eliminate the
square-root derivative. This gives the source's weighted diagonal formula
and its dimension-independent bound by the actual relative trace norm.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {m : ℕ}

theorem evenScalarSlope_eq_ratio_mul (f : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    evenScalarSlope f x = (deriv f |x| / |x|) * x := by
  by_cases hp : 0 ≤ x
  · rw [evenScalarSlope, ite_eq_left hp, abs_of_nonneg hp, div_mul_cancel₀ _ hx]
  · rw [evenScalarSlope, ite_eq_right hp, abs_of_neg (lt_of_not_ge hp)]
    field_simp [hx]

theorem cfc_evenScalarSlope_modeHamiltonian (f : ℝ → ℝ)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j) :
    cfc (evenScalarSlope f) (modeHamiltonian ν) =
      Complex.I • complexifyMatrix (modeDiagonal (fun j => deriv f
        (ν j)) * modeSymplecticForm) := by
  have hH := modeHamiltonian_isHermitian (fun j => (hν j).le)
  have hne : ∀ x ∈ spectrum ℝ (modeHamiltonian ν), x ≠ 0 := by
    intro x hx hx0
    have hspec : x ∈ spectrum ℝ
        (symplecticHamiltonian modeSymplecticForm
          ((1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) * modeDiagonal ν * 1ᵀ)) := by
      simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
        symplecticHamiltonian_modeDiagonal (fun j => (hν j).le)] using hx
    obtain ⟨j, hj⟩ := abs_eigenvalue_symplecticHamiltonian_williamson 1
      (by simp) hν hspec
    rw [hx0, abs_zero] at hj
    linarith [hν j]
  have he : cfc (evenScalarSlope f) (modeHamiltonian ν) =
      cfc (fun x : ℝ => (deriv f |x| / |x|) * x) (modeHamiltonian ν) :=
    cfc_congr fun x hx => evenScalarSlope_eq_ratio_mul f (hne x hx)
  rw [he, cfc_mul (fun x : ℝ => deriv f |x| / |x|) (fun x : ℝ => x)
      (modeHamiltonian ν) ((modeHamiltonian ν).finite_real_spectrum.continuousOn _) continuousOn_id,
    cfc_id' ℝ (modeHamiltonian ν) hH.isSelfAdjoint,
    cfc_complex_abs_composition hH (fun x => deriv f x / x),
    abs_modeHamiltonian (fun j => (hν j).le), complexifyMatrix_modeDiagonal,
    cfc_complex_real_diagonal,
    ← complexifyMatrix_modeDiagonal (fun j => deriv f (ν j) / ν j), modeHamiltonian,
    Matrix.mul_smul, ← complexifyMatrix_mul]
  congr 1
  congr 1
  rw [← Matrix.mul_assoc, modeDiagonal_mul]
  congr 2
  funext j
  exact div_mul_cancel₀ _ (hν j).ne'

theorem real_trace_complexifyMatrix {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) : (complexifyMatrix A).trace.re = A.trace := by
  simp only [Matrix.trace, Complex.re_sum, Matrix.diag_apply, complexifyMatrix,
    Matrix.map_apply, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re]

theorem trace_skew_sylvester_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω R W X : Matrix ι ι ℝ) (hΩ : Ω * Ω = -1)
    (hR : Commute R Ω) (hW : Commute W Ω) :
    (-(W * Ω) * (X * Ω * R + R * Ω * X)).trace =
      (W * (R * X + X * R)).trace := by
  have hΩRΩ : Ω * R * Ω = -R := by
    rw [← hR.eq, Matrix.mul_assoc, hΩ, Matrix.mul_neg, Matrix.mul_one]
  have hΩRWΩ : (Ω * R) * (W * Ω) = -(R * W) := by
    calc
      _ = R * (Ω * W) * Ω := by rw [← hR.eq]; noncomm_ring
      _ = R * (W * Ω) * Ω := by rw [← hW.eq]
      _ = R * W * (Ω * Ω) := by noncomm_ring
      _ = _ := by rw [hΩ, Matrix.mul_neg, Matrix.mul_one]
  have ht : (W * Ω * X * Ω * R).trace = -(W * X * R).trace := by
    calc
      _ = ((W * Ω) * X * (Ω * R)).trace := by congr 1; noncomm_ring
      _ = ((Ω * R) * (W * Ω) * X).trace := Matrix.trace_mul_cycle _ _ _
      _ = -(R * W * X).trace := by rw [hΩRWΩ, Matrix.neg_mul, Matrix.trace_neg]
      _ = _ := congrArg Neg.neg (Matrix.trace_mul_cycle W X R).symm
  have halg : -(W * Ω) * (X * Ω * R + R * Ω * X) =
      -(W * Ω * X * Ω * R) - W * (Ω * R * Ω) * X := by noncomm_ring
  rw [halg, Matrix.trace_sub, Matrix.trace_neg, ht, hΩRΩ,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_add, Matrix.trace_add]
  simp only [← Matrix.mul_assoc]
  ring

/-- Mode covariance space represented by `modeDiagonal ν`. -/
def modeCovarianceSpace (ν : Fin m → ℝ) : RealSymmetricMatrixSpace (Fin m × Fin 2) :=
  ⟨modeDiagonal ν, (Matrix.isHermitian_diagonal _).isSelfAdjoint⟩

theorem covariancePurityDerivative_mode (r : ℝ) {ν : Fin m → ℝ}
    (hν : ∀ j, 0 < ν j) (Δ : RealSymmetricMatrixSpace (Fin m × Fin 2)) :
    covariancePurityDerivative r (modeCovarianceSpace ν) (modeDiagonal_posDef hν) Δ =
      -(1 / 2) * ∑ i : Fin m × Fin 2, deriv (logPurityFactor r) (ν i.1) *
        (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) i i := by
  let R := CFC.sqrt (modeDiagonal ν)
  let X : RealSymmetricMatrixSpace (Fin m × Fin 2) :=
    (positiveSylvesterSelfAdjointContinuousEquiv
      (matrix_sqrt_posDef (modeDiagonal_posDef hν))).symm Δ
  have hsolve : R * (X : Matrix _ _ ℝ) + (X : Matrix _ _ ℝ) * R =
      (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :=
    positiveSylvester_inverse_solves (matrix_sqrt_posDef (modeDiagonal_posDef hν)) Δ
  have hR : Commute R modeSymplecticForm := by
    dsimp only [R]
    rw [modeDiagonal_sqrt (fun j => (hν j).le)]
    exact modeDiagonal_commute_symplectic _
  change -(1 / 2) * hamiltonianSpectralDerivative modeSymplecticForm
    transpose_modeSymplecticForm (modeCovarianceSpace ν) (modeDiagonal_posDef hν)
      (evenScalarSlope (logPurityFactor r)) Δ = _
  have hV : (modeCovarianceSpace ν : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef :=
    modeDiagonal_posDef hν
  have happly := hamiltonianSpectralDerivative_apply modeSymplecticForm
    transpose_modeSymplecticForm (modeCovarianceSpace ν) Δ hV
    (evenScalarSlope (logPurityFactor r))
  refine (congrArg (fun z : ℝ => -(1 / 2) * z) happly).trans ?_
  change -(1 / 2) * (cfc (evenScalarSlope (logPurityFactor r))
    (symplecticHamiltonian modeSymplecticForm (modeDiagonal ν)) *
      (Complex.I • complexifyMatrix ((X : Matrix _ _ ℝ) * modeSymplecticForm * R +
        R * modeSymplecticForm * (X : Matrix _ _ ℝ)))).trace.re = _
  rw [symplecticHamiltonian_modeDiagonal (fun j => (hν j).le),
    cfc_evenScalarSlope_modeHamiltonian _ hν,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
    neg_one_smul, ← complexifyMatrix_mul, ← complexifyMatrix_neg,
    real_trace_complexifyMatrix, ← Matrix.neg_mul,
    trace_skew_sylvester_identity _ _ _ _ modeSymplecticForm_mul_self hR
      (modeDiagonal_commute_symplectic _), hsolve]
  congr 1
  simp only [modeDiagonal, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

theorem mode_relativeCovariancePerturbation_diagonal {ν : Fin m → ℝ}
    (hν : ∀ j, 0 < ν j)
    (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (i : Fin m × Fin 2) :
    ν i.1 * relativeCovariancePerturbation (modeDiagonal ν) Δ i i = Δ i i := by
  rw [relativeCovariancePerturbation, modeDiagonal_sqrt (fun j => (hν j).le),
    modeDiagonal_inv (fun j => (Real.sqrt_pos.mpr (hν j)).ne')]
  simp only [modeDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hsq := Real.sq_sqrt (hν i.1).le
  have hne := (Real.sqrt_pos.mpr (hν i.1)).ne'
  field_simp [hne]
  rw [hsq]

/-- The source coefficient r/2 multiplies the actual finite matrix trace
norm; the proof does not introduce a dimension factor. -/
theorem abs_covariancePurityDerivative_mode_le {r : ℝ} (hr : 1 < r)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (Δ : RealSymmetricMatrixSpace (Fin m × Fin 2)) :
    |covariancePurityDerivative r (modeCovarianceSpace ν)
      (modeDiagonal_posDef (fun j => by linarith [hν j])) Δ| ≤
        (r / 2) * matrixTraceNorm (relativeCovariancePerturbation (modeDiagonal ν) Δ) := by
  have hν0 (j : Fin m) : 0 < ν j := by linarith [hν j]
  let Z := relativeCovariancePerturbation (modeDiagonal ν) (Δ : Matrix _ _ ℝ)
  have hZ : Z.IsHermitian := relativeCovariancePerturbation_isHermitian
    (modeDiagonal_posDef hν0) (realSymmetricMatrix_isHermitian Δ)
  have hw (i : Fin m × Fin 2) :
      |ν i.1 * deriv (logPurityFactor r) (ν i.1)| ≤ r := by
    obtain ⟨hl, hu⟩ := logPurityFactor_derivative_bound hr (hν i.1)
    rwa [abs_of_nonneg hl]
  have h := abs_weighted_diagonal_le_matrixTraceNorm hZ (by linarith : 0 ≤ r)
    (fun i => ν i.1 * deriv (logPurityFactor r) (ν i.1)) hw
  have he : (∑ i : Fin m × Fin 2,
      (ν i.1 * deriv (logPurityFactor r) (ν i.1)) * Z i i) =
      ∑ i : Fin m × Fin 2, deriv (logPurityFactor r) (ν i.1) *
        (Δ : Matrix _ _ ℝ) i i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = deriv (logPurityFactor r) (ν i.1) * (ν i.1 * Z i i) := by ring
      _ = _ := by rw [mode_relativeCovariancePerturbation_diagonal hν0]
  rw [he] at h
  rw [covariancePurityDerivative_mode r hν0, abs_mul]
  norm_num only [abs_neg, abs_div, abs_one]
  nlinarith

end VacuumBellSeparation.Gaussian
