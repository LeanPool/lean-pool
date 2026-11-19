/-
Copyright (c) 2026 BrownianMotion contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BrownianMotion contributors
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Linear algebra for Gaussian processes -/


@[expose] public section

lemma sum_single_apply {ι : Type*} (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [Fintype ι]
    [DecidableEq ι] (v : (i : ι) → φ i) :
    ∑ i, Pi.single i (v i) = v := by
  ext i
  simp

lemma Matrix.PosSemidef.nonneg_apply_self {n R : Type*} [CommRing R] [PartialOrder R]
    [StarRing R] {M : Matrix n n R} (hM : M.PosSemidef) (i : n) : 0 ≤ M i i := by
  classical
  convert hM.2 (Finsupp.single i 1)
  simp

section mkContinuous₂

namespace LinearMap

variable {E F G 𝕜 : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F →ₗ[𝕜] G)

/-- Given a bilinear map whose codomains are finite dimensional, outputs the continuous
version. -/
def mkContinuous₂OfFiniteDimensional : E →L[𝕜] F →L[𝕜] G :=
  letI g x : F →L[𝕜] G := (f x).toContinuousLinearMap
  letI h : E →ₗ[𝕜] F →L[𝕜] G :=
    { toFun := g
      map_add' x y := by ext z; simp [g]
      map_smul' m x := by ext y; simp [g] }
  h.toContinuousLinearMap

@[simp]
lemma mkContinuous₂OfFiniteDimensional_apply (x : E) (y : F) :
    f.mkContinuous₂OfFiniteDimensional x y = f x y := rfl

end LinearMap

end mkContinuous₂

section InnerProductSpace

open scoped InnerProductSpace

lemma OrthonormalBasis.inner_eq {𝕜 E ι : Type*} [NormedAddCommGroup E] [RCLike 𝕜]
    [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) {i j : ι} :
    ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := by
  by_cases h : i = j
  · simp only [h, ↓reduceIte]
    apply RCLike.ext
    · simp
    · simp
  · simp [h]

lemma OrthonormalBasis.norm_sq_eq_sum_sq_inner_right {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  simp

lemma OrthonormalBasis.norm_sq_eq_sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪x, b i⟫_ℝ ^ 2 := by
  simp_rw [b.norm_sq_eq_sum_sq_inner_right, real_inner_comm]

lemma EuclideanSpace.real_inner_eq {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  nth_rw 1 [← (EuclideanSpace.basisFun ι ℝ).sum_repr' x, sum_inner]
  simp_rw [real_inner_smul_left, basisFun_inner]

@[simp]
lemma inner_toDual_symm_eq_self {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (L : StrongDual 𝕜 E) :
  inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) = L := by ext; simp

@[simp]
lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
    ⇑f.toLinearIsometry.toContinuousLinearMap = ⇑f := rfl

end InnerProductSpace
