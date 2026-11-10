/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TripleSpectralGap

/-! A quantitative positive-semidefinite perturbation estimate follows by completing the square
along a one-dimensional kernel. -/

@[expose] public noncomputable section

open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- Completing the square for a diagonal perturbation along a one-dimensional
kernel. The coefficient condition is written without division. -/
theorem diagonal_kernel_quadratic_nonneg {d₁ d₂ d₃ σ K M L : ℝ}
    (hK : 0 < K) (hM : 0 ≤ M) (hd₁ : |d₁| ≤ M) (hd₂ : |d₂| ≤ M)
    (hkernel : K ≤ σ ^ 2 * d₁ + σ ^ 2 * d₂ + d₃)
    (hcoeff : K * M + 2 * σ ^ 2 * M ^ 2 ≤ K * L) (a b z : ℝ) :
    0 ≤ d₁ * (a + σ * z) ^ 2 + d₂ * (b + σ * z) ^ 2 + d₃ * z ^ 2 +
      L * (a ^ 2 + b ^ 2) := by
  have hd₁sq : d₁ ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d₁) hM).mpr hd₁
  have hd₂sq : d₂ ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d₂) hM).mpr hd₂
  have ht : (d₁ * a + d₂ * b) ^ 2 ≤ 2 * M ^ 2 * (a ^ 2 + b ^ 2) := by
    have h₁ := mul_le_mul_of_nonneg_right hd₁sq (sq_nonneg a)
    have h₂ := mul_le_mul_of_nonneg_right hd₂sq (sq_nonneg b)
    nlinarith only [h₁, h₂, sq_nonneg (d₁ * a - d₂ * b)]
  have hda : 0 ≤ (d₁ + M) * a ^ 2 :=
    mul_nonneg (by linarith only [(abs_le.mp hd₁).1]) (sq_nonneg a)
  have hdb : 0 ≤ (d₂ + M) * b ^ 2 :=
    mul_nonneg (by linarith only [(abs_le.mp hd₂).1]) (sq_nonneg b)
  have hc := mul_le_mul_of_nonneg_right hcoeff (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hk := mul_le_mul_of_nonneg_right hkernel (sq_nonneg z)
  have hsq := sq_nonneg (K * z + σ * (d₁ * a + d₂ * b))
  have hcross := mul_le_mul_of_nonneg_left ht (sq_nonneg σ)
  have hpositive := mul_nonneg hK.le (add_nonneg hda hdb)
  have hlower : 0 ≤ K * (d₁ * (a + σ * z) ^ 2 + d₂ * (b + σ * z) ^ 2 +
      d₃ * z ^ 2 + L * (a ^ 2 + b ^ 2)) := by
    have hkernel' := mul_le_mul_of_nonneg_left hk hK.le
    nlinarith only [hsq, hcross, hpositive, hc, hkernel']
  exact nonneg_of_mul_nonneg_right hlower hK

/-- A finite-matrix perturbation with explicit bounds on the two transverse
diagonal entries and a positive lower bound in the kernel direction. -/
theorem diagonal_add_smul_posSemidef {B : Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B.IsHermitian) {σ m : ℝ}
    (hgap : ∀ x : Fin 3 → ℝ, m * ((x 0 - σ * x 2) ^ 2 + (x 1 - σ * x 2) ^ 2) ≤
      x ⬝ᵥ (B *ᵥ x)) {d : Fin 3 → ℝ} {S K M : ℝ}
    (hS : 0 ≤ S) (hK : 0 < K) (hM : 0 ≤ M)
    (hd₀ : |d 0| ≤ M) (hd₁ : |d 1| ≤ M)
    (hkernel : K ≤ σ ^ 2 * d 0 + σ ^ 2 * d 1 + d 2)
    (hcoeff : K * M + 2 * σ ^ 2 * M ^ 2 ≤ K * (S * m)) :
    (Matrix.diagonal d + S • B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_diagonal d).add (hB.smul (IsSelfAdjoint.all S)))
  intro x
  simp only [star_trivial, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  have hdiag : x ⬝ᵥ (Matrix.diagonal d *ᵥ x) =
      d 0 * (x 0) ^ 2 + d 1 * (x 1) ^ 2 + d 2 * (x 2) ^ 2 := by
    simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three]
    ring
  rw [hdiag]
  have hquad := diagonal_kernel_quadratic_nonneg hK hM hd₀ hd₁ hkernel hcoeff
    (x 0 - σ * x 2) (x 1 - σ * x 2) (x 2)
  have hgap' := mul_le_mul_of_nonneg_left (hgap x) hS
  nlinarith only [hquad, hgap']

end EhrhardGaussian.Ehrhard

end
