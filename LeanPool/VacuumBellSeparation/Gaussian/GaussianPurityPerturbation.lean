/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuantumPurityCalculus

/-!
# The actual Gaussian log-purity perturbation estimate

The true aggregate derivative is integrated along V+tΔ by the real mean
value bound. Literal strict quantum uncertainty at the two endpoints
supplies the faithful spectral domain throughout the segment. The final
operator statement concerns the true extended traces of actual Gaussian
density powers, using the previously proved spectral trace identity.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

variable {m : ℕ}

/-- Symmetric covariance segment given by `V + t • Δ`. -/
def symmetricCovarianceSegment
    (V Δ : RealSymmetricMatrixSpace (Fin m × Fin 2)) (t : ℝ) :
    RealSymmetricMatrixSpace (Fin m × Fin 2) := V + t • Δ

@[simp] theorem symmetricCovarianceSegment_coe
    (V Δ : RealSymmetricMatrixSpace (Fin m × Fin 2)) (t : ℝ) :
    ((symmetricCovarianceSegment V Δ t : RealSymmetricMatrixSpace (Fin m × Fin 2)) :
      Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) = covarianceSegment (V : Matrix (Fin m × Fin 2)
        (Fin m × Fin 2) ℝ) (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) t := rfl

theorem hasDerivAt_covariancePurityTrace_segment {r : ℝ} (hr : 0 < r)
    (V Δ : RealSymmetricMatrixSpace (Fin m × Fin 2)) (t : ℝ)
    (hW : (covarianceSegment (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (Δ : Matrix
      (Fin m × Fin 2) (Fin m × Fin 2) ℝ) t).PosDef)
    (hQ : (quantumCovariance (covarianceSegment (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
      (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) t)
      modeSymplecticForm).PosDef) :
    HasDerivAt (fun s : ℝ => covariancePurityTrace r (symmetricCovarianceSegment V Δ s : Matrix
      (Fin m × Fin 2) (Fin m × Fin 2) ℝ))
      (covariancePurityDerivative r (symmetricCovarianceSegment V Δ t) hW Δ) t := by
  have hc : HasDerivAt (symmetricCovarianceSegment V Δ) Δ t := by
    change HasDerivAt (fun s : ℝ => V + s • Δ) Δ t
    convert! ((hasDerivAt_id t).smul_const Δ).const_add V using 1;
      simp only [one_smul]
  exact (hasFDerivAt_covariancePurityTrace_of_strict_quantum hr
    (symmetricCovarianceSegment V Δ t) hW hQ).comp_hasDerivAt t hc

theorem covariancePurityTrace_segment_bound {r : ℝ} (hr : 1 < r)
    (V Δ : RealSymmetricMatrixSpace (Fin m × Fin 2))
    (hV : (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef)
    (hQ₀ : (quantumCovariance (V : Matrix (Fin m × Fin 2)
      (Fin m × Fin 2) ℝ) modeSymplecticForm).PosDef)
    (hQ₁ : (quantumCovariance ((V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) + (Δ : Matrix
      (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) modeSymplecticForm).PosDef)
    (hδ : ‖relativeCovariancePerturbation (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
      (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)‖ < 1) :
    |covariancePurityTrace r ((V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) + (Δ : Matrix
      (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) - covariancePurityTrace r (V : Matrix (Fin m × Fin 2)
        (Fin m × Fin 2) ℝ)| ≤
      (r / 2) / (1 - ‖relativeCovariancePerturbation (V : Matrix (Fin m × Fin 2)
        (Fin m × Fin 2) ℝ) (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)‖) *
        matrixTraceNorm (relativeCovariancePerturbation (V : Matrix (Fin m × Fin 2)
          (Fin m × Fin 2) ℝ) (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) := by
  let F : ℝ → ℝ := fun t => covariancePurityTrace r (symmetricCovarianceSegment V Δ t : Matrix
    (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
  let C := (r / 2) * ((1 - ‖relativeCovariancePerturbation (V : Matrix (Fin m × Fin 2)
    (Fin m × Fin 2) ℝ) (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)‖)⁻¹ *
    matrixTraceNorm (relativeCovariancePerturbation (V : Matrix (Fin m × Fin 2)
      (Fin m × Fin 2) ℝ) (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)))
  have hW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (covarianceSegment (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (Δ : Matrix
        (Fin m × Fin 2) (Fin m × Fin 2) ℝ) t).PosDef :=
    covarianceSegment_posDef hV (realSymmetricMatrix_isHermitian Δ) ht.1 ht.2 hδ
  have hQ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (quantumCovariance (covarianceSegment (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
        (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) t)
        modeSymplecticForm).PosDef :=
    quantumCovariance_segment_posDef hQ₀ hQ₁ ht.1 ht.2
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt F (covariancePurityDerivative r (symmetricCovarianceSegment V Δ t)
        (hW t ht) Δ) t :=
    hasDerivAt_covariancePurityTrace_segment (by linarith) V Δ t (hW t ht) (hQ t ht)
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖deriv F t‖ ≤ C := by
    rw [(hd t ht).deriv, Real.norm_eq_abs]
    exact (abs_covariancePurityDerivative_le_of_strict_quantum hr
      (symmetricCovarianceSegment V Δ t) Δ (hW t ht) (hQ t ht)).trans
        (mul_le_mul_of_nonneg_left
          (matrixTraceNorm_relativeCovariancePerturbation_segment_le hV
            (realSymmetricMatrix_isHermitian Δ) ht.1 ht.2 hδ) (by linarith : 0 ≤ r / 2))
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hd t ht).differentiableAt) hb
    (left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
  simpa only [F, C, symmetricCovarianceSegment, one_smul, zero_smul, add_zero,
    Submodule.coe_add, Submodule.coe_zero, Real.norm_eq_abs, sub_zero, abs_one, mul_one,
      div_eq_mul_inv,
    mul_assoc] using h

/-- Actual infinite-dimensional Gaussian density powers satisfy the
source log-purity estimate, with the genuine covariance perturbation.
Both literal strict uncertainty hypotheses are explicit. -/
theorem abs_log_positiveTrace_gaussian_rpow_sub_le
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hB : IsPositiveTraceClass B)
    {V Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.PosDef) (hΔ : Δ.IsHermitian)
    (hQ₀ : (quantumCovariance (V : Matrix (Fin m × Fin 2)
      (Fin m × Fin 2) ℝ) modeSymplecticForm).PosDef)
    (hQ₁ : (quantumCovariance (V + Δ) modeSymplecticForm).PosDef)
    (hGA : HasGaussianPhysicalCharacteristic A V)
    (hGB : HasGaussianPhysicalCharacteristic B (V + Δ))
    {r : ℝ} (hr : 1 < r) (hδ : ‖relativeCovariancePerturbation V Δ‖ < 1) :
    |Real.log (positiveTrace (B ^ r)).toReal - Real.log (positiveTrace (A ^ r)).toReal| ≤
      (r / 2) / (1 - ‖relativeCovariancePerturbation V Δ‖) *
        matrixTraceNorm (relativeCovariancePerturbation V Δ) := by
  have hW : (V + Δ).PosDef := by
    simpa only [covarianceSegment, one_smul] using
      covarianceSegment_posDef hV hΔ (t := 1) zero_le_one le_rfl hδ
  rw [log_positiveTrace_gaussianPhysical_rpow_eq_purity hB hW hQ₁ hGB (by linarith),
    log_positiveTrace_gaussianPhysical_rpow_eq_purity hA hV hQ₀ hGA (by linarith)]
  exact covariancePurityTrace_segment_bound hr ⟨V, hV.isHermitian.isSelfAdjoint⟩
    ⟨Δ, hΔ.isSelfAdjoint⟩ hV hQ₀ hQ₁ hδ

end VacuumBellSeparation.Gaussian
