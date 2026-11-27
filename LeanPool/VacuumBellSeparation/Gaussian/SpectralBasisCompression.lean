/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteBasisCompression
public import LeanPool.VacuumBellSeparation.Gaussian.CompactPowerIntertwining

/-!
# Actual spectral finite compressions of inverse-reference sandwiches

Finite selections from a genuine reference eigenbasis reduce the reference
operator and every positive CFC power. The finite inverse powers occur only
on the strictly positive finite compressed matrix. Thus the actual bounded
inverse-range sandwich compresses to exactly the finite Renyi sandwich;
no bounded inverse of the infinite reference is introduced.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Matrix
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι κ E F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem compression_apply_eigenvector (i : F →ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) {x : F} {a : ℝ} (ha : A (i x) = a • i x) :
    compression i A x = a • x := by
  change i.toContinuousLinearMap.adjoint (A (i x)) = _
  rw [ha, map_smul_of_tower, adjoint_embedding_apply]

omit [DecidableEq κ] in
theorem finiteBasisEmbedding_intertwine (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {A : E →L[ℂ] E}
    {a : ι → ℝ} (ha : ∀ j, A (b j) = a j • b j) :
    A.comp (finiteBasisEmbedding b f hf).toContinuousLinearMap =
      (finiteBasisEmbedding b f hf).toContinuousLinearMap.comp
        (compression (finiteBasisEmbedding b f hf) A) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun κ ℂ).toBasis.ext
  intro j
  change A (finiteBasisEmbedding b f hf (EuclideanSpace.basisFun κ ℂ j)) =
    finiteBasisEmbedding b f hf
      (compression (finiteBasisEmbedding b f hf) A (EuclideanSpace.basisFun κ ℂ j))
  have he : A (finiteBasisEmbedding b f hf (EuclideanSpace.basisFun κ ℂ j)) =
      a (f j) • finiteBasisEmbedding b f hf (EuclideanSpace.basisFun κ ℂ j) := by
    simpa only [finiteBasisEmbedding_basis] using ha (f j)
  rw [compression_apply_eigenvector _ A he]
  exact he.trans ((finiteBasisEmbedding b f hf).toLinearMap.map_smul_of_tower
    (a (f j)) (EuclideanSpace.basisFun κ ℂ j)).symm

omit [DecidableEq κ] in
theorem finiteBasisEmbedding_rpow_intertwine (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {A : E →L[ℂ] E}
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ j, A (b j) = a j • b j)
    {p : ℝ} (hp : 0 < p) :
    (A ^ p).comp (finiteBasisEmbedding b f hf).toContinuousLinearMap =
      (finiteBasisEmbedding b f hf).toContinuousLinearMap.comp
        ((compression (finiteBasisEmbedding b f hf) A) ^ p) :=
  compact_positive_rpow_intertwine
    (isCompactOperator_of_locallyCompactSpace_dom (compression (finiteBasisEmbedding b f hf) A))
    (compression_nonneg _ hA) hA _ (finiteBasisEmbedding_intertwine b f hf ha) hp

theorem compression_conjugate_of_intertwine (i : F →ₗᵢ[ℂ] E)
    {S : E →L[ℂ] E} {C : F →L[ℂ] F} (hS : IsSelfAdjoint S) (hC : IsSelfAdjoint C)
    (hi : S.comp i.toContinuousLinearMap = i.toContinuousLinearMap.comp C)
    (Θ : E →L[ℂ] E) : compression i (S * Θ * S) = C * compression i Θ * C := by
  have he (x : F) : S (i x) = i (C x) := DFunLike.congr_fun hi x
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [compression_inner, mul_apply_eq_comp, mul_apply_eq_comp,
    ← S.adjoint_inner_left, hS.adjoint_eq, he, he, ← compression_inner]
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← C.adjoint_inner_right, hC.adjoint_eq]

theorem finiteBasisCompression_sandwich_factorization (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {ρ σ Θ : E →L[ℂ] E}
    (hσ : 0 ≤ σ) {a : ι → ℝ} (ha : ∀ j, σ (b j) = a j • b j)
    {τ : ℝ} (hτ : 0 < τ)
    (hfactor : σ ^ (τ / 2) * Θ * σ ^ (τ / 2) = ρ) :
    finiteBasisCompression b f hf ρ =
      (finiteBasisCompression b f hf σ) ^ (τ / 2) * finiteBasisCompression b f hf Θ *
        (finiteBasisCompression b f hf σ) ^ (τ / 2) := by
  apply (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)).injective
  change (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ))
      (finiteBasisCompression b f hf ρ) =
    (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ))
      ((finiteBasisCompression b f hf σ) ^ (τ / 2) *
        finiteBasisCompression b f hf Θ * (finiteBasisCompression b f hf σ) ^ (τ / 2))
  simp only [map_mul, toEuclideanCLM_rpow (finiteBasisCompression_posSemidef b f hf hσ),
    toEuclideanCLM_finiteBasisCompression]
  rw [← hfactor]
  exact compression_conjugate_of_intertwine _ CFC.rpow_nonneg.isSelfAdjoint
    CFC.rpow_nonneg.isSelfAdjoint (finiteBasisEmbedding_rpow_intertwine b f hf hσ ha
      (half_pos hτ)) Θ

theorem finiteBasisCompression_eq_finiteRenyiSandwich (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {ρ σ Θ : E →L[ℂ] E}
    (hσ : 0 ≤ σ) (hinj : Function.Injective σ)
    {a : ι → ℝ} (ha : ∀ j, σ (b j) = a j • b j) {τ : ℝ} (hτ : 0 < τ)
    (hfactor : σ ^ (τ / 2) * Θ * σ ^ (τ / 2) = ρ) :
    finiteRenyiSandwich (finiteBasisCompression b f hf ρ) (finiteBasisCompression b f hf σ) τ =
      finiteBasisCompression b f hf Θ := by
  let S := finiteBasisCompression b f hf σ
  have hS := finiteBasisCompression_posDef b f hf hσ hinj
  have hleft : S ^ (-τ / 2) * S ^ (τ / 2) = 1 := by
    rw [← CFC.rpow_add hS.isUnit, show -τ / 2 + τ / 2 = 0 by ring,
      CFC.rpow_zero S hS.posSemidef.nonneg]
  have hright : S ^ (τ / 2) * S ^ (-τ / 2) = 1 := by
    rw [← CFC.rpow_add hS.isUnit, show τ / 2 + -τ / 2 = 0 by ring,
      CFC.rpow_zero S hS.posSemidef.nonneg]
  rw [finiteRenyiSandwich, finiteBasisCompression_sandwich_factorization b f hf hσ ha hτ hfactor]
  change S ^ (-τ / 2) * (S ^ (τ / 2) * _ * S ^ (τ / 2)) * S ^ (-τ / 2) = _
  calc
    _ = (S ^ (-τ / 2) * S ^ (τ / 2)) * finiteBasisCompression b f hf Θ *
        (S ^ (τ / 2) * S ^ (-τ / 2)) := by noncomm_ring
    _ = _ := by rw [hleft, hright, one_mul, mul_one]

end VacuumBellSeparation.Gaussian
