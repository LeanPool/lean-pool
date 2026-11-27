/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteRenyiInterpolation
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace

/-!
# Finite matrix traces are the actual Hilbert-space positive trace

The pinned star-algebra equivalence sends a matrix to its bounded operator
on genuine Euclidean Hilbert space. Computing in the actual coordinate
Hilbert basis identifies the full positiveTrace with the finite matrix
trace, and genuine functional calculus transports every real power.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix ContinuousLinearMap
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem euclidean_coordinate_inner_matrix (A : Matrix ι ι ℂ) (i j : ι) :
    inner ℂ (EuclideanSpace.basisFun ι ℂ i)
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A (EuclideanSpace.basisFun ι ℂ j)) = A i j := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul]
  change (WithLp.ofLp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A
    (EuclideanSpace.single j 1))) i = A i j
  rw [Matrix.ofLp_toEuclideanCLM, PiLp.ofLp_single, Matrix.mulVec_single_one]
  rfl

theorem positiveTrace_toEuclideanCLM {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    positiveTrace ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A) = ENNReal.ofReal A.trace.re := by
  let b := (EuclideanSpace.basisFun ι ℂ).toHilbertBasis
  rw [positiveTrace_eq_tsum_diagonal b (map_nonneg (Matrix.toEuclideanCLM (n := ι)
    (𝕜 := ℂ)) hA.nonneg)]
  have he (i : ι) : inner ℂ (b i) ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A (b i)) = A i i := by
    simpa only [b, OrthonormalBasis.coe_toHilbertBasis]
      using euclidean_coordinate_inner_matrix A i i
  simp only [he, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1)]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]

theorem toEuclideanCLM_rpow {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (p : ℝ) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A ^ p) = ((Matrix.toEuclideanCLM (n := ι)
      (𝕜 := ℂ)) A) ^ p := by
  have hmap := map_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) hA.nonneg
  rw [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hmap]
  let euclideanLinear :=
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact StarAlgHomClass.map_cfc (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (fun x : ℝ => x ^ p) A
    (A.finite_real_spectrum.continuousOn _)
    euclideanLinear.continuous_of_finiteDimensional
    hA.isHermitian.isSelfAdjoint hmap.isSelfAdjoint

theorem positiveTrace_toEuclideanCLM_rpow {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (p : ℝ) :
    positiveTrace (((Matrix.toEuclideanCLM (n := ι)
      (𝕜 := ℂ)) A) ^ p) = finitePositivePowerTrace A p := by
  rw [← toEuclideanCLM_rpow hA p,
    positiveTrace_toEuclideanCLM (CFC.rpow_nonneg (a := A) (y := p)).posSemidef]
  rfl

theorem toEuclideanCLM_finiteRenyiSandwich {ρ σ : Matrix ι ι ℂ}
    (hσ : σ.PosSemidef) (τ : ℝ) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (finiteRenyiSandwich ρ σ τ) =
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) σ) ^ (-τ / 2) * (Matrix.toEuclideanCLM (n := ι)
        (𝕜 := ℂ)) ρ *
        ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) σ) ^ (-τ / 2) := by
  simp only [finiteRenyiSandwich, map_mul, toEuclideanCLM_rpow hσ]

end VacuumBellSeparation.Gaussian
