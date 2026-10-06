/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzConvolution

/-!
# The regularized tensor of Schwartz velocity fields

The outer product is a continuous complex bilinear map. Pairing it with
Schwartz mollification preserves Schwartz regularity of the tensor.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The componentwise outer product on complex Euclidean three-vectors. -/
@[expose]
def regularisedComplexTensorOuter (v u : ComplexVec3) : ComplexTensor3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    WithLp.toLp 2 (fun j : Fin 3 => v i * u j))

/-- The Frobenius norm of a complex rank-one tensor is the product of
the two vector norms. -/
theorem regularisedComplexTensorOuter_norm (v u : ComplexVec3) :
    ‖regularisedComplexTensorOuter v u‖ = ‖v‖ * ‖u‖ := by
  have hv : ‖v‖ ^ 2 = ∑ i : Fin 3, ‖v i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ v
  have hu : ‖u‖ ^ 2 = ∑ j : Fin 3, ‖u j‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ u
  have hout : ‖regularisedComplexTensorOuter v u‖ ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, ‖v i‖ ^ 2 * ‖u j‖ ^ 2 := by
    rw [regularisedComplexTensorOuter, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i hi
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j hj
    simp [mul_pow]
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, ‖v i‖ ^ 2 * ‖u j‖ ^ 2) =
      (∑ i : Fin 3, ‖v i‖ ^ 2) * (∑ j : Fin 3, ‖u j‖ ^ 2) := by
    rw [Finset.sum_mul_sum]
  have hnormsq : ‖regularisedComplexTensorOuter v u‖ ^ 2 =
      (‖v‖ * ‖u‖) ^ 2 := by
    rw [hout, hsum, ← hv, ← hu, mul_pow]
  have hnonneg : 0 ≤ ‖regularisedComplexTensorOuter v u‖ := norm_nonneg _
  have htarget : 0 ≤ ‖v‖ * ‖u‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith only [hnormsq, hnonneg, htarget]

@[expose]
def regularisedComplexTensorOuterLinear :
    ComplexVec3 →ₗ[ℂ] ComplexVec3 →ₗ[ℂ] ComplexTensor3 :=
  LinearMap.mk₂ ℂ regularisedComplexTensorOuter
    (by intro v w u; apply PiLp.ext; intro i; apply PiLp.ext; intro j;
        simp [regularisedComplexTensorOuter, add_mul])
    (by intro c v u; apply PiLp.ext; intro i; apply PiLp.ext; intro j;
        simp [regularisedComplexTensorOuter, mul_assoc])
    (by intro v u w; apply PiLp.ext; intro i; apply PiLp.ext; intro j;
        simp [regularisedComplexTensorOuter, mul_add])
    (by intro c v u; apply PiLp.ext; intro i; apply PiLp.ext; intro j;
        simp [regularisedComplexTensorOuter, mul_left_comm])

/-- The complex rank-one tensor is a continuous bilinear map on the
Euclidean spatial carriers. -/
@[expose]
def regularisedComplexTensorOuterCLM :
    ComplexVec3 →L[ℂ] ComplexVec3 →L[ℂ] ComplexTensor3 :=
  regularisedComplexTensorOuterLinear.mkContinuous₂ 1 (by
    intro v u
    change ‖regularisedComplexTensorOuter v u‖ ≤ 1 * ‖v‖ * ‖u‖
    rw [regularisedComplexTensorOuter_norm]
    simp)

/-- The regularized quadratic tensor of a complex Schwartz velocity
field is again Schwartz. -/
@[expose]
def regularisedSchwartzTensor
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) :
    𝓢(L2Vec3, ComplexTensor3) :=
  SchwartzMap.pairing regularisedComplexTensorOuterCLM
    (regularisedSchwartzMollify ρ ε hε ψ) ψ

/-- The Schwartz tensor has the expected pointwise outer-product form. -/
theorem regularisedSchwartzTensor_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    regularisedSchwartzTensor ρ ε hε ψ x =
      regularisedComplexTensorOuter
        (regularisedSchwartzMollify ρ ε hε ψ x) (ψ x) := rfl

end CKN.Leray

end
