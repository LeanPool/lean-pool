/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PurityScalarTaylor
public import LeanPool.VacuumBellSeparation.Gaussian.HamiltonianSpectralDerivative
public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticHamiltonianNormalForm
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Actual purity differentiation on the faithful covariance domain

Upper hemicontinuity of the actual spectrum preserves a strict spectral
gap. The proved disconnected scalar Taylor bound therefore supplies the
actual Hermitian spectral trace derivative even at repeated eigenvalues.
The genuine Williamson normal form proves the required gap when every
mode variance is strictly greater than 1/2.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter Set
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem finite_common_strict_lower_bound [Finite ι] (v : ι → ℝ) {b : ℝ}
    (hv : ∀ i, b < v i) : ∃ a : ℝ, b < a ∧ ∀ i, a < v i := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ s : Finset ι, ∃ a : ℝ, b < a ∧ ∀ i ∈ s, a < v i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨b + 1, by linarith, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, hba, ha⟩ := ih
      obtain ⟨c, hbc, hci⟩ := exists_between (hv i)
      refine ⟨min a c, lt_min hba hbc, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt hci
      · exact (min_le_left _ _).trans_lt (ha j hj)
  obtain ⟨a, ha, h⟩ := hfin Finset.univ
  exact ⟨a, ha, fun i => h i (Finset.mem_univ i)⟩

theorem eventually_eigenvalues_in_signed_interval
    (A : HermitianMatrixSpace ι) {a M : ℝ}
    (hA : ∀ i, a < |(hermitianMatrix_isHermitian A).eigenvalues i| ∧
      |(hermitianMatrix_isHermitian A).eigenvalues i| < M) :
    ∀ᶠ B : HermitianMatrixSpace ι in 𝓝 A, ∀ j,
      a < |(hermitianMatrix_isHermitian B).eigenvalues j| ∧
      |(hermitianMatrix_isHermitian B).eigenvalues j| < M := by
  let G : Set ℝ := {x | a < |x| ∧ |x| < M}
  have hG : IsOpen G :=
    (isOpen_lt continuous_const continuous_abs).inter
      (isOpen_lt continuous_abs continuous_const)
  have hspec : spectrum ℝ (A : Matrix ι ι ℂ) ⊆ G := by
    rw [(hermitianMatrix_isHermitian A).spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact hA i
  have he := (upperHemicontinuous_spectrum ℝ (Matrix ι ι ℂ)).forall_isOpen
    (A : Matrix ι ι ℂ) G hG hspec
  have hc : Continuous (fun B : HermitianMatrixSpace ι => (B : Matrix ι ι ℂ)) :=
    continuous_subtype_val
  filter_upwards [(hc.tendsto A).eventually he] with B hB j
  exact hB ((hermitianMatrix_isHermitian B).eigenvalues_mem_spectrum_real j)

/-- The actual spectral trace derivative, with no local scalar Taylor
hypothesis left and no differentiability of eigenvalue branches required. -/
theorem hasFDerivAt_faithfulHermitianPurity
    (A : HermitianMatrixSpace ι) {r : ℝ} (hr : 0 < r)
    (hgap : ∀ i, 1 / 2 < |(hermitianMatrix_isHermitian A).eigenvalues i|) :
    HasFDerivAt (hermitianSpectralTrace (fun x => logPurityFactor r |x|))
      (hermitianTraceDerivative A (evenScalarSlope (logPurityFactor r))) A := by
  obtain ⟨a, ha, hlow⟩ := finite_common_strict_lower_bound
    (fun i => |(hermitianMatrix_isHermitian A).eigenvalues i|) hgap
  let M := ‖(A : Matrix ι ι ℂ)‖ + 1
  have hbounds (i : ι) : a < |(hermitianMatrix_isHermitian A).eigenvalues i| ∧
      |(hermitianMatrix_isHermitian A).eigenvalues i| < M := by
    refine ⟨hlow i, ?_⟩
    have h := IsometricContinuousFunctionalCalculus.norm_spectrum_le
      (A : Matrix ι ι ℂ) ((hermitianMatrix_isHermitian A).eigenvalues_mem_spectrum_real i)
      (hermitianMatrix_isHermitian A).isSelfAdjoint
    simpa only [Real.norm_eq_abs] using h.trans_lt (lt_add_one _)
  obtain ⟨C, hC, hrem⟩ := exists_even_logPurityFactor_quadratic_remainder
    (M := M) hr ha
  apply hasFDerivAt_hermitianSpectralTrace_of_scalar_remainder A _ _ hC
  filter_upwards [eventually_eigenvalues_in_signed_interval A hbounds] with B hB i j
  exact hrem _ _ (hbounds i).1.le (hbounds i).2.le (hB j).1.le (hB j).2.le

theorem abs_eigenvalue_symplecticHamiltonian_williamson
    {m : ℕ} (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j)
    {x : ℝ} (hx : x ∈ spectrum ℝ
      (symplecticHamiltonian modeSymplecticForm (S * modeDiagonal ν * Sᵀ))) :
    ∃ j : Fin m, |x| = ν j := by
  let H := symplecticHamiltonian modeSymplecticForm (S * modeDiagonal ν * Sᵀ)
  have hH : H.IsHermitian := symplecticHamiltonian_isHermitian
    transpose_modeSymplecticForm _
  have habs : |x| ∈ spectrum ℝ (CFC.abs H) := by
    rw [CFC.abs_eq_cfc_norm H hH.isSelfAdjoint,
      cfc_map_spectrum (fun y : ℝ => ‖y‖) H hH.isSelfAdjoint continuous_norm.continuousOn]
    exact ⟨x, hx, by simp only [Real.norm_eq_abs]⟩
  have hw := canonical_williamson_covariance_posDef S hS hν
  rw [show H = _ from symplecticHamiltonian_eq_williamson_conjugate S hS hν hw,
    complex_matrix_abs_unitary_conjugate,
    abs_modeHamiltonian (fun j => (hν j).le)] at habs
  have hs : spectrum ℝ
      ((williamsonHamiltonianUnitary S ν hν hw : Matrix _ _ ℂ) *
        complexifyMatrix (modeDiagonal ν) *
        (williamsonHamiltonianUnitary S ν hν hw : Matrix _ _ ℂ)ᴴ) =
      spectrum ℝ (complexifyMatrix (modeDiagonal ν)) := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      (Unitary.spectrum_star_right_conjugate (R := ℝ)
        (a := complexifyMatrix (modeDiagonal ν))
        (U := williamsonHamiltonianUnitary S ν hν hw))
  rw [hs] at habs
  have hc : ((|x| : ℝ) : ℂ) ∈ spectrum ℂ (complexifyMatrix (modeDiagonal ν)) :=
    spectrum.algebraMap_mem ℂ habs
  rw [complexifyMatrix_modeDiagonal, _root_.spectrum_diagonal] at hc
  obtain ⟨j, hj⟩ := hc
  exact ⟨j.1, (Complex.ofReal_injective hj).symm⟩

theorem faithful_williamson_hamiltonian_gap
    {m : ℕ} (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 < ν j) :
    ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm
      (S * modeDiagonal ν * Sᵀ)), 1 / 2 < |x| := by
  intro x hx
  obtain ⟨j, hj⟩ := abs_eigenvalue_symplecticHamiltonian_williamson S hS
    (fun j => by linarith [hν j]) hx
  rw [hj]
  exact hν j

/-- Continuous linear map for the covariance purity derivative, of type `RealSymmetricMatrixSpace
(Fin m × Fin 2) →L[ℝ] ℝ`. -/
def covariancePurityDerivative {m : ℕ} (r : ℝ)
    (V : RealSymmetricMatrixSpace (Fin m × Fin 2))
    (hV : (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef) :
    RealSymmetricMatrixSpace (Fin m × Fin 2) →L[ℝ] ℝ :=
  (-(1 / 2) : ℝ) • hamiltonianSpectralDerivative modeSymplecticForm
    transpose_modeSymplecticForm V hV (evenScalarSlope (logPurityFactor r))

theorem hasFDerivAt_covariancePurityTrace_of_spectral_gap
    {m : ℕ} {r : ℝ} (hr : 0 < r)
    (V : RealSymmetricMatrixSpace (Fin m × Fin 2))
    (hV : (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef)
    (hgap : ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm
      (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)), 1 / 2 < |x|) :
    HasFDerivAt (fun X : RealSymmetricMatrixSpace (Fin m × Fin 2) =>
      covariancePurityTrace r (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ))
      (covariancePurityDerivative r V hV) V := by
  let H := symmetricHamiltonian modeSymplecticForm transpose_modeSymplecticForm V
  have hh := hasFDerivAt_faithfulHermitianPurity H hr
    (fun i => hgap _ ((hermitianMatrix_isHermitian H).eigenvalues_mem_spectrum_real i))
  have hc := hh.comp V (hasFDerivAt_symmetricHamiltonian transpose_modeSymplecticForm V hV)
  exact hc.const_smul (-(1 / 2) : ℝ)

end VacuumBellSeparation.Gaussian
