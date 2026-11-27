/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianWeylGram
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumNondegenerateCovariance

/-!
# Actual Gaussian characteristic forces quantum uncertainty

The positive finite density Gram of Weyl differences is divided by 2s.
Its exact exponential quotient converges entrywise to V+iΩ/2 in raw
real displacement coordinates. Closedness of the genuine matrix positive
cone proves uncertainty. The actual orthogonal Ω rotation then recovers
the physical covariance convention. No quadrature-domain assumptions or
positive-kernel surrogate are used.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ}

theorem real_coordinate_basis_bilinear
    (M : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (i j : Fin m × Fin 2) :
    (Pi.single i 1 : Fin m × Fin 2 → ℝ) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

theorem gaussianWeylCrossExponent_basis_limit
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.IsHermitian)
    (i j : Fin m × Fin 2) :
    (1 / 2 : ℝ) • (gaussianWeylCrossExponent V (Pi.single i 1) (Pi.single j 1) -
      ((-(V i i) : ℝ) : ℂ) - ((-(V j j) : ℝ) : ℂ)) =
      quantumCovariance V modeSymplecticForm i j := by
  have hs : V j i = V i j := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply] using
      congrFun (congrFun hV.eq i) j
  simp only [gaussianWeylCrossExponent, Matrix.mulVec_sub, sub_dotProduct,
    dotProduct_sub, real_coordinate_basis_bilinear, hs, quantumCovariance,
    Matrix.add_apply, Matrix.smul_apply, complexifyMatrix_apply,
    Complex.real_smul, smul_eq_mul]
  push_cast
  ring

/-- Necessity for the actual raw displacement characteristic. The matrix
V must be symmetric because its quadratic form alone cannot distinguish
an added antisymmetric part. -/
theorem gaussianDisplacement_quantum_posSemidef
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.IsHermitian)
    (hG : HasGaussianDisplacementCharacteristic A V) :
    (quantumCovariance V modeSymplecticForm).PosSemidef := by
  let M : ℝ → Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ := fun s =>
    (1 / 2 : ℝ) • (s⁻¹ • densityExpectationGram (multiModeNumberBasis m) A
      (fun i => gaussianWeylDifference s (Pi.single i 1)))
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), (M s).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((densityExpectationGram_posSemidef (multiModeNumberBasis m) hA
      (fun i => gaussianWeylDifference s (Pi.single i 1))).smul
        (inv_nonneg.mpr (le_of_lt hs))).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hlim : Tendsto M (𝓝[>] (0 : ℝ)) (𝓝 (quantumCovariance V modeSymplecticForm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    let a := gaussianWeylCrossExponent V (Pi.single i 1) (Pi.single j 1)
    let b : ℂ := ((-(V i i) : ℝ) : ℂ)
    let c : ℂ := ((-(V j j) : ℝ) : ℂ)
    have he : (1 / 2 : ℝ) • (a - b - c) = quantumCovariance V modeSymplecticForm i j :=
      gaussianWeylCrossExponent_basis_limit hV i j
    have h := (tendsto_gaussianGramDifference_quotient a b c).const_smul (1 / 2 : ℝ)
    rw [he] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [M, Matrix.smul_apply, densityExpectationGram,
      gaussianWeylDifference_expectation hA hG (le_of_lt hs), real_coordinate_basis_bilinear]
    rfl
  exact isClosed_setOfPred_posSemidef.mem_of_tendsto hlim hpos

/-- Literal physical uncertainty is necessary for an actual positive
Gaussian density, with the canonical displacement rotation retained. -/
theorem gaussianPhysical_quantum_posSemidef
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.IsHermitian)
    (hG : HasGaussianPhysicalCharacteristic A V) :
    (quantumCovariance V modeSymplecticForm).PosSemidef := by
  have hB : (physicalDisplacementCovariance V).IsHermitian := by
    simpa only [physicalDisplacementCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul modeSymplecticForm hV
  have h := gaussianDisplacement_quantum_posSemidef hA hB hG
  have hh := h.mul_mul_conjTranspose_same (complexifyMatrix (modeSymplecticForm (ι := Fin m)))
  rw [← quantumCovariance_congruence] at hh
  have hcov : modeSymplecticForm * physicalDisplacementCovariance V * modeSymplecticFormᵀ = V := by
    unfold physicalDisplacementCovariance
    calc
      _ = (modeSymplecticForm * modeSymplecticFormᵀ) * V *
          (modeSymplecticForm * modeSymplecticFormᵀ) := by noncomm_ring
      _ = V := by rw [modeSymplecticForm_mul_transpose, Matrix.one_mul, Matrix.mul_one]
  have hform : (modeSymplecticForm (ι := Fin m)) * modeSymplecticForm * modeSymplecticFormᵀ =
      modeSymplecticForm := by rw [Matrix.mul_assoc, modeSymplecticForm_mul_transpose,
        Matrix.mul_one]
  rwa [hcov, hform] at hh

end VacuumBellSeparation.Gaussian
