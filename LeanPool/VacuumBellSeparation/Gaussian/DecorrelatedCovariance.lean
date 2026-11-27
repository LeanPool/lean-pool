/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuantumRealCovariance

/-!
# Actual covariance decorrelation by complementary label projections

The reference covariance is Pᵀ V P + Qᵀ V Q. Complementarity P+Q=I
preserves strict positivity of the sum of congruences; orthogonality in
the Euclidean norm is unnecessary. Vanishing symplectic cross blocks
preserves the literal strict quantum uncertainty matrix. Idempotence is
used only for the regional restrictions and zero covariance cross block.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem posDef_sum_complementary_congruences {𝕜 : Type*}
    [CommRing 𝕜] [PartialOrder 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜]
    {M P Q : Matrix ι ι 𝕜} (hM : M.PosDef) (hPQ : P + Q = 1) :
    (Pᴴ * M * P + Qᴴ * M * Q).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(hM.posSemidef.conjTranspose_mul_mul_same P).isHermitian.add
    (hM.posSemidef.conjTranspose_mul_mul_same Q).isHermitian, ?_⟩
  intro x hx
  have hsplit : P *ᵥ x + Q *ᵥ x = x := by
    rw [← Matrix.add_mulVec, hPQ, Matrix.one_mulVec]
  have hform : star x ⬝ᵥ ((Pᴴ * M * P + Qᴴ * M * Q) *ᵥ x) =
      star (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x)) +
        star (Q *ᵥ x) ⬝ᵥ (M *ᵥ (Q *ᵥ x)) := by
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.star_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [hform]
  by_cases hPx : P *ᵥ x = 0
  · have hQx : Q *ᵥ x ≠ 0 := by
      intro hQx
      apply hx
      simpa only [hPx, hQx, add_zero] using hsplit.symm
    simpa only [hPx, star_zero, zero_dotProduct, zero_add] using hM.dotProduct_mulVec_pos hQx
  · exact add_pos_of_pos_of_nonneg (hM.dotProduct_mulVec_pos hPx)
      (hM.posSemidef.dotProduct_mulVec_nonneg _)

/-- Decorrelated covariance given by `Pᵀ * V * P + Qᵀ * V * Q`. -/
def decorrelatedCovariance (V P Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Pᵀ * V * P + Qᵀ * V * Q

theorem decorrelatedCovariance_posDef {V P Q : Matrix ι ι ℝ}
    (hV : V.PosDef) (hPQ : P + Q = 1) : (decorrelatedCovariance V P Q).PosDef := by
  simpa only [decorrelatedCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    posDef_sum_complementary_congruences hV hPQ

theorem complementary_symplectic_diagonal {Ω P Q : Matrix ι ι ℝ}
    (hPQ : P + Q = 1) (hcross : Pᵀ * Ω * Q = 0) (hcross' : Qᵀ * Ω * P = 0) :
    Pᵀ * Ω * P + Qᵀ * Ω * Q = Ω := by
  have h := congrArg (fun T : Matrix ι ι ℝ => Tᵀ * Ω * T) hPQ
  simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, hcross, hcross',
    add_zero, zero_add] at h
  exact h

theorem quantumCovariance_decorrelated {V Ω P Q : Matrix ι ι ℝ}
    (hPQ : P + Q = 1) (hcross : Pᵀ * Ω * Q = 0) (hcross' : Qᵀ * Ω * P = 0) :
    quantumCovariance (decorrelatedCovariance V P Q) Ω =
      (complexifyMatrix P)ᴴ * quantumCovariance V Ω * complexifyMatrix P +
        (complexifyMatrix Q)ᴴ * quantumCovariance V Ω * complexifyMatrix Q := by
  have hΩ := complementary_symplectic_diagonal hPQ hcross hcross'
  calc
    quantumCovariance (decorrelatedCovariance V P Q) Ω =
        quantumCovariance (Pᵀ * V * P) (Pᵀ * Ω * P) +
          quantumCovariance (Qᵀ * V * Q) (Qᵀ * Ω * Q) := by
      nth_rw 1 [← hΩ]
      simp only [quantumCovariance, decorrelatedCovariance, complexifyMatrix,
        Matrix.map_add (algebraMap ℝ ℂ) (map_add (algebraMap ℝ ℂ)), smul_add]
      abel
    _ = _ := by
      have hP := quantumCovariance_congruence V Ω Pᵀ
      have hQ := quantumCovariance_congruence V Ω Qᵀ
      simpa only [Matrix.transpose_transpose, complexifyMatrix_transpose,
        Matrix.conjTranspose_conjTranspose] using congrArg₂ (· + ·) hP hQ

theorem quantumCovariance_decorrelated_posDef {V Ω P Q : Matrix ι ι ℝ}
    (hV : (quantumCovariance V Ω).PosDef) (hPQ : P + Q = 1)
    (hcross : Pᵀ * Ω * Q = 0) (hcross' : Qᵀ * Ω * P = 0) :
    (quantumCovariance (decorrelatedCovariance V P Q) Ω).PosDef := by
  rw [quantumCovariance_decorrelated hPQ hcross hcross']
  apply posDef_sum_complementary_congruences hV
  have h := congrArg complexifyMatrix hPQ
  simpa only [complexifyMatrix,
    Matrix.map_add (algebraMap ℝ ℂ) (map_add (algebraMap ℝ ℂ)),
    Matrix.map_one (algebraMap ℝ ℂ) (map_zero _) (map_one _)] using h

theorem complementary_projection_cross {P Q : Matrix ι ι ℝ}
    (hP : P * P = P) (hPQ : P + Q = 1) : P * Q = 0 ∧ Q * P = 0 := by
  constructor
  · calc
      P * Q = P * (P + Q) - P * P := by noncomm_ring
      _ = 0 := by rw [hPQ, Matrix.mul_one, hP, sub_self]
  · calc
      Q * P = (P + Q) * P - P * P := by noncomm_ring
      _ = 0 := by rw [hPQ, Matrix.one_mul, hP, sub_self]

theorem complementary_projection_right_idempotent {P Q : Matrix ι ι ℝ}
    (hP : P * P = P) (hPQ : P + Q = 1) : Q * Q = Q := by
  have hcross := (complementary_projection_cross hP hPQ).2
  calc
    Q * Q = Q * (P + Q) - Q * P := by noncomm_ring
    _ = Q := by rw [hPQ, Matrix.mul_one, hcross, sub_zero]

theorem decorrelatedCovariance_left_restriction (V : Matrix ι ι ℝ)
    {P Q : Matrix ι ι ℝ} (hP : P * P = P) (hPQ : P + Q = 1) :
    Pᵀ * decorrelatedCovariance V P Q * P = Pᵀ * V * P := by
  have hcross := (complementary_projection_cross hP hPQ).2
  calc
    _ = (P * P)ᵀ * V * (P * P) + (Q * P)ᵀ * V * (Q * P) := by
      unfold decorrelatedCovariance
      simp only [Matrix.transpose_mul]
      noncomm_ring
    _ = _ := by rw [hP, hcross]; simp

theorem decorrelatedCovariance_right_restriction (V : Matrix ι ι ℝ)
    {P Q : Matrix ι ι ℝ} (hP : P * P = P) (hPQ : P + Q = 1) :
    Qᵀ * decorrelatedCovariance V P Q * Q = Qᵀ * V * Q := by
  have hQ := complementary_projection_right_idempotent hP hPQ
  have h := decorrelatedCovariance_left_restriction V (P := Q) (Q := P) hQ
    ((add_comm Q P).trans hPQ)
  simpa only [decorrelatedCovariance, add_comm] using h

theorem decorrelatedCovariance_cross (V : Matrix ι ι ℝ)
    {P Q : Matrix ι ι ℝ} (hP : P * P = P) (hPQ : P + Q = 1) :
    Pᵀ * decorrelatedCovariance V P Q * Q = 0 := by
  have hcross := complementary_projection_cross hP hPQ
  calc
    _ = (P * P)ᵀ * V * (P * Q) + (Q * P)ᵀ * V * (Q * Q) := by
      unfold decorrelatedCovariance
      simp only [Matrix.transpose_mul]
      noncomm_ring
    _ = 0 := by rw [hcross.1, hcross.2]; simp

end VacuumBellSeparation.Gaussian
