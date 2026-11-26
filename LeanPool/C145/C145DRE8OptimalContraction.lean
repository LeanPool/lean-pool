/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8ProjectionResiduals
public import LeanPool.C145.C145DRE8SpectralContraction

/-! True orthogonal projection residuals joined to the DRE8 raw-kernel
contraction. The finite index set is the nonground modal set of the source.
The p=3,4,5 interfaces support all three quadratic-Krylov slices. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2 C145.ThreePlane
variable {n : ℕ}

/-- The three annihilated moments remove any quadratic from every power slice. -/
theorem power_quadratic_residual_slice (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (p : ℕ) (c0 c1 c2 : ℝ) :
    tensorSlice V (fun i => a i * t i ^ p) =
      tensorSlice V (fun i => a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2))) := by
  classical
  funext j k
  have h0 := hm.1 0 (by omega) j k
  have h1 := hm.1 1 (by omega) j k
  have h2 := hm.1 2 (by omega) j k
  calc
    _ = tensorSlice V (fun i => a i * t i ^ p) j k -
      c0 * (∑ i, (a i * t i ^ 0) * V i j k) -
      c1 * (∑ i, (a i * t i ^ 1) * V i j k) -
      c2 * (∑ i, (a i * t i ^ 2) * V i j k) := by rw [h0,h1,h2]; ring
    _ = _ := by
      simp only [tensorSlice, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Literal source moment slice equals the actual optimal projection residual slice. -/
theorem power_projection_residual_slice (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (p : ℕ) :
    tensorSlice V (fun i => a i * t i ^ p) =
      tensorSlice V (fun i => projectionResidual a t p i) := by
  obtain ⟨c0,c1,c2,hc⟩ := exists_projection_residual_coefficients a t p
  rw [power_quadratic_residual_slice a t V hm p c0 c1 c2]
  congr 1
  funext i
  exact (hc i).symm

/-- Cauchy--Schwarz in actual finite-coordinate norms, with true κ_p. -/
theorem projection_residual_slice_cauchy (a t : Fin n → ℝ) (V : Tensor n) (p : ℕ) :
    matrixSq (tensorSlice V (fun i => projectionResidual a t p i)) ≤
      kappa a t p ^ 2 * tensorSq V := by
  rw [kappa_sq_eq_sum]
  exact tensorSlice_cauchy V _

/-- Source power-slice bound, with no residual/minimizer supplied as a premise. -/
theorem power_slice_kappa_bound (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (p : ℕ) :
    matrixSq (tensorSlice V (fun i => a i * t i ^ p)) ≤
      kappa a t p ^ 2 * tensorSq V := by
  rw [power_projection_residual_slice a t V hm p]
  exact projection_residual_slice_cauchy a t V p

/-- True κ₃ is no larger than the standard monic Chebyshev residual. -/
theorem kappa_three_chebyshev_sq (a t : Fin n → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    1024 * kappa a t 3 ^ 2 ≤ ∑ i, a i ^ 2 := by
  have hm := kappa_sq_le_quadratic_residual a t 3 (1 / 32) (-9 / 16) (3 / 2)
  have hc := chebyshev_vector_bound a t ht0 ht1
  have heq : (∑ i, (a i * (t i ^ 3-((1 / 32 : ℝ) + (-9 / 16) * t i + (3 / 2) * t i ^ 2))) ^ 2) =
      ∑ i, (a i * chebyshevResidual (t i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [chebyshevResidual]
    ring
  rw [heq] at hm
  linarith

/-- Source κ₃ ≤ ‖a‖₂/32 in the true Euclidean norm. -/
theorem kappa_three_le_norm_div32 (a t : Fin n → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    kappa a t 3 ≤ ‖momentVector a t 0‖ / 32 := by
  have hc := kappa_three_chebyshev_sq a t ht0 ht1
  have heq : ‖momentVector a t 0‖ ^ 2 = ∑ i, a i ^ 2 := by
    simpa only [momentVector_apply, pow_zero, mul_one] using
      EuclideanSpace.real_norm_sq_eq (momentVector a t 0)
  have hs : (32 * kappa a t 3) ^ 2 ≤ ‖momentVector a t 0‖ ^ 2 := by
    rw [heq]
    nlinarith
  have hn : 0 ≤ 32 * kappa a t 3 := mul_nonneg (by norm_num) (kappa_nonneg a t 3)
  have hle := (sq_le_sq₀ hn (norm_nonneg (momentVector a t 0))).mp hs
  linarith

/-- Optimal DRE8 (6.4), squared, with actual attained κ₃ rather than an
explicit or hypothesized residual. -/
theorem kernel_optimal_contraction (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell u : ℝ) (hw : ell < u)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) :
    (2 * ell-u) ^ 6 * matrixSq (tensorSlice (xiWeighted rates V) a) ≤
      (u-ell) ^ 6 * kappa a (fun i => (rates i-ell) / (u-ell)) 3 ^ 2 *
      tensorSq (xiWeighted rates V) := by
  obtain ⟨c0,c1,c2,hc⟩ := exists_kappa_coefficients a (fun i => (rates i-ell) / (u-ell)) 3
  have h := kernel_residual_contraction a rates V hm ell u hw hband hlo hhi c0 c1 c2
  rw [hc] at h
  exact h

/-- Actual ordinary H₂ data gives the sharp κ₃ contraction. The weighted
moments, polynomial factor and minimizer are all derived, never premises. -/
theorem actual_H2_optimal_contraction (a rates : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates (weightedTensor a E)) (ell u : ℝ) (hw : ell < u)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) :
    (2 * ell-u) ^ 6 * matrixSq (tensorSlice E a) ≤
      (u-ell) ^ 6 * kappa a (fun i => (rates i-ell) / (u-ell)) 3 ^ 2 * tensorSq E := by
  obtain ⟨R,_,_,hE,hm,_⟩ := actual_H2_physical_kernel a rates ha hRates E hSym hData ell (u-ell)
  rw [hE]
  exact kernel_optimal_contraction a rates _ hm ell u hw hband hlo hhi

end C145DRE8

end
