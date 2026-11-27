/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteMatrixPositiveTrace
public import LeanPool.VacuumBellSeparation.Gaussian.CompressionPowerTrace

/-!
# Genuine finite coordinate compressions of a Hilbert-space operator

A finite injective selection from an actual Hilbert basis gives an
isometric embedding of Euclidean Hilbert space. The associated finite
matrix is exactly the actual adjoint compression, not a replacement
state. Positivity, strict positivity for injective input, and the full
positive trace/power-trace bounds are proved for these matrices.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Matrix
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι κ E F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Linear map for the finite basis embedding linear, of type `EuclideanSpace ℂ κ →ₗ[ℂ] E`. -/
def finiteBasisEmbeddingLinear (b : HilbertBasis ι ℂ E) (f : κ → ι) :
    EuclideanSpace ℂ κ →ₗ[ℂ] E :=
  (EuclideanSpace.basisFun κ ℂ).toBasis.constr ℂ (b ∘ f)

omit [DecidableEq κ] [CompleteSpace E] in
theorem finiteBasisEmbeddingLinear_basis (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (i : κ) :
    finiteBasisEmbeddingLinear b f (EuclideanSpace.basisFun κ ℂ i) = b (f i) :=
  (EuclideanSpace.basisFun κ ℂ).toBasis.constr_basis ℂ (b ∘ f) i

/-- Linear isometry for the finite basis embedding, of type `EuclideanSpace ℂ κ →ₗᵢ[ℂ] E`. -/
def finiteBasisEmbedding (b : HilbertBasis ι ℂ E) (f : κ → ι)
    (hf : Function.Injective f) : EuclideanSpace ℂ κ →ₗᵢ[ℂ] E :=
  (finiteBasisEmbeddingLinear b f).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun κ ℂ).toBasis)
    (EuclideanSpace.basisFun κ ℂ).orthonormal (by
      have he : (finiteBasisEmbeddingLinear b f) ∘
          (EuclideanSpace.basisFun κ ℂ).toBasis = b ∘ f := by
        funext i
        exact finiteBasisEmbeddingLinear_basis b f i
      rw [he]
      exact b.orthonormal.comp f hf)

omit [DecidableEq κ] [CompleteSpace E] in
theorem finiteBasisEmbedding_basis (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) (i : κ) :
    finiteBasisEmbedding b f hf (EuclideanSpace.basisFun κ ℂ i) = b (f i) :=
  finiteBasisEmbeddingLinear_basis b f i

/-- Compress an operator to the span of the chosen orthonormal family. -/
def finiteBasisCompression (b : HilbertBasis ι ℂ E) (f : κ → ι)
    (hf : Function.Injective f) (A : E →L[ℂ] E) : Matrix κ κ ℂ :=
  (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)).symm (compression (finiteBasisEmbedding b f hf) A)

@[simp] theorem toEuclideanCLM_finiteBasisCompression (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) (A : E →L[ℂ] E) :
    (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)) (finiteBasisCompression b f hf A) =
      compression (finiteBasisEmbedding b f hf) A :=
  (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)).apply_symm_apply _

theorem finiteBasisCompression_entry (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) (A : E →L[ℂ] E) (i j : κ) :
    finiteBasisCompression b f hf A i j = inner ℂ (b (f i)) (A (b (f j))) := by
  rw [← euclidean_coordinate_inner_matrix (finiteBasisCompression b f hf A) i j,
    toEuclideanCLM_finiteBasisCompression,
    compression_inner, finiteBasisEmbedding_basis, finiteBasisEmbedding_basis]

theorem finiteBasisCompression_posSemidef (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    (finiteBasisCompression b f hf A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact map_nonneg (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)).symm (compression_nonneg _ hA)

theorem compression_injective_of_positive_injective (i : F →ₗᵢ[ℂ] E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) (hinj : Function.Injective A) :
    Function.Injective (compression i A) := by
  have hz (x : F) (hx : compression i A x = 0) : x = 0 := by
    have hd : (inner ℂ (i x) (A (i x))).re = 0 := by
      rw [← compression_inner i A, hx, inner_zero_right, Complex.zero_re]
    have hs : CFC.sqrt A (i x) = 0 := by
      apply norm_eq_zero.mp
      have he := sqrt_norm_sq_eq_diagonal hA (i x)
      rw [hd] at he
      nlinarith [norm_nonneg (CFC.sqrt A (i x))]
    have ha : A (i x) = 0 := by
      rw [← CFC.sq_sqrt A hA, pow_two, mul_apply_eq_comp, hs, map_zero]
    have hi : i x = 0 := hinj (ha.trans (map_zero A).symm)
    exact i.injective (hi.trans (map_zero i).symm)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hxy, sub_self]

theorem finiteBasisCompression_posDef (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {A : E →L[ℂ] E}
    (hA : 0 ≤ A) (hinj : Function.Injective A) :
    (finiteBasisCompression b f hf A).PosDef := by
  apply (finiteBasisCompression_posSemidef b f hf hA).posDef_iff_isUnit.mpr
  have hc := compression_injective_of_positive_injective (finiteBasisEmbedding b f hf) hA hinj
  have hu : IsUnit (compression (finiteBasisEmbedding b f hf) A) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hc, LinearMap.injective_iff_surjective.mp hc⟩
  exact hu.map (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)).symm

theorem finiteBasisCompression_trace_le (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    ENNReal.ofReal (finiteBasisCompression b f hf A).trace.re ≤ positiveTrace A := by
  rw [← positiveTrace_toEuclideanCLM (finiteBasisCompression_posSemidef b f hf hA),
    toEuclideanCLM_finiteBasisCompression]
  exact positiveTrace_compression_le _ hA

theorem finiteBasisCompression_power_trace_le (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hf : Function.Injective f) {A : E →L[ℂ] E}
    (hc : IsCompactOperator A) (hA : 0 ≤ A) {p : ℝ} (hp : 1 ≤ p) :
    finitePositivePowerTrace (finiteBasisCompression b f hf A) p ≤ positiveTrace (A ^ p) := by
  rw [← positiveTrace_toEuclideanCLM_rpow (finiteBasisCompression_posSemidef b f hf hA),
    toEuclideanCLM_finiteBasisCompression]
  exact positiveTrace_compression_rpow_le _ hc hA hp

end VacuumBellSeparation.Gaussian
