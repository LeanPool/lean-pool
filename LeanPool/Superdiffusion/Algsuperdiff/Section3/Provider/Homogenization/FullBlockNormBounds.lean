/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.BlockMatrix
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# FullBlockNormBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Four-block domination of the full Euclidean block operator norm

The variance carriers of Section 3.5 are stated with the Euclidean operator
norm of a `2d × 2d` matrix over `BlockCoord d = Fin d ⊕ Fin d`
(`‖Matrix.toEuclidean (toFullBlockMat ...)‖`), while the block moment inputs
available for them are stated with the `d × d` norm `Ch02.matrixOperatorNorm`
of one of the four blocks.  This module supplies that direction of the
dictionary.

## What is proved

1. `norm_toEuclideanCLM_le_sum_matrixOperatorNorm_blocks`: for every `X: FullBlockMat d`,
   `‖toEuclidean X‖ ≤ ‖UL‖ + ‖UR‖ + ‖LL‖ + ‖LR‖`, the summands being the
   `Ch02.matrixOperatorNorm` of the four `d × d` blocks `ofFullBlockMat X`.  No symmetry,
   definiteness or nondegeneracy hypothesis is used, and the constant is absolute.
2. `norm_toEuclideanCLM_sq_le_four_mul_sum_sq_matrixOperatorNorm_blocks`: the squared
   corollary with the absolute constant `4`, `‖toEuclidean X‖² ≤ 4 (‖UL‖² + ‖UR‖² + ‖LL‖²
   + ‖LR‖²)`.
3. The two `BlockMat`-carrier restatements (`..._toFullBlockMat_...`), the shape
   in which the block carriers of this directory present their matrices.
4. `norm_toEuclideanCLM_diagonal_mul_mul_diagonal_le`: conjugating by the two-scalar block
   gauge `diag(s 𝟙, t 𝟙)` weights the four block norms by `s²`, `|st|`, `|st|`, `t²`.

The squared form is the one an integrability consumer wants: integrability of
the full squared operator norm follows from a second moment for each of the
four block norms separately.  Applied to `starredFluctuationMatrix B a` it
dominates `starredFluctuationOperatorNormSq B a` with no rewriting at all, that
carrier being literally `‖toEuclidean (starredFluctuationMatrix ...)‖²`.

## What is not proved here

The instance of item 4 at the manuscript's own gauge is *not* taken: it needs
the identification of `CFC.sqrt (Ch02.constantFullBlockMatrix
(Observable.isotropicComparatorMatrix σ))` with `Matrix.diagonal
(Ch05.Section56.scalarFullBlockSqrtDiag σ σ)` -- available as the private
`cfcSqrt_isotropicComparator_eq_diagonal` (`VarianceCarrierSeam.lean`, second
copy at `VarianceClosure.lean`;
a four-line consequence of the public
`Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt`)
-- plus the block readings of the reflected difference, and taking it here
would import the whole `VarianceBridge` closure into a pure matrix module.  A
consumer holding that closure reaches the manuscript weights `σ`, `1`, `1`,
`σ⁻¹` from item 4 at `s = √σ`, `t = (√σ)⁻¹` after `Real.sq_sqrt` and
`mul_inv_cancel₀` at `σ > 0`; the squared gauged form the M7 consumer wants is
a six-line re-derivation from item 5 plus `pow_le_pow_left₀` (the four-square
split as in the squared corollary).

## Method

`X` acts on `EuclideanSpace ℝ (BlockCoord d)`; splitting the argument into its
two halves `u = x ∘ Sum.inl`, `v = x ∘ Sum.inr` and using
`(X *ᵥ x) = Sum.elim (UL *ᵥ u + UR *ᵥ v) (LL *ᵥ u + LR *ᵥ v)` gives the bound
from `ContinuousLinearMap.opNorm_le_bound`, because the Euclidean norm of a
`Sum.elim` is below the sum of the two halves' norms and each half of `x` has
norm at most `‖x‖`.  The gauge statement then needs only the four entrywise
readings of `diag · X · diag` and absolute homogeneity of the `d × d` norm.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open _root_.HCPolySupport _root_.HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## Two Euclidean facts about `BlockCoord`-indexed vectors -/

/-- Pythagoras for a block-coordinate vector assembled from its two halves. -/
private theorem norm_sq_toLp_sum_elim (u v : Vec d) :
    ‖(WithLp.toLp 2 (Sum.elim u v) : EuclideanSpace ℝ (BlockCoord d))‖ ^ (2 : ℕ) =
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ^ (2 : ℕ) +
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ (2 : ℕ) := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_sum_type]
  rfl

/-- The Euclidean norm of a block-coordinate vector is below the sum of the
norms of its two halves. -/
private theorem norm_toLp_sum_elim_le (u v : Vec d) :
    ‖(WithLp.toLp 2 (Sum.elim u v) : EuclideanSpace ℝ (BlockCoord d))‖ ≤
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ +
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  refine (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp ?_
  rw [norm_sq_toLp_sum_elim]
  have hcross :
      0 ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hexpand :
      (‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ +
          ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖) ^ (2 : ℕ) =
        ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ^ (2 : ℕ) +
          ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ (2 : ℕ) +
          2 * (‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ *
            ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖) := by
    ring
  linarith

/-- Each half of a block-coordinate vector has Euclidean norm at most the norm
of the whole vector. -/
private theorem norm_toLp_comp_le (f : BlockCoord d → ℝ) :
    ‖(WithLp.toLp 2 (f ∘ Sum.inl) : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (BlockCoord d))‖ ∧
      ‖(WithLp.toLp 2 (f ∘ Sum.inr) : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (BlockCoord d))‖ := by
  have hsplit :
      ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (BlockCoord d))‖ ^ (2 : ℕ) =
        ‖(WithLp.toLp 2 (f ∘ Sum.inl) : EuclideanSpace ℝ (Fin d))‖ ^ (2 : ℕ) +
          ‖(WithLp.toLp 2 (f ∘ Sum.inr) : EuclideanSpace ℝ (Fin d))‖ ^ (2 : ℕ) := by
    rw [← norm_sq_toLp_sum_elim (f ∘ Sum.inl) (f ∘ Sum.inr), Sum.elim_comp_inl_inr]
  constructor
  · refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    have h := sq_nonneg ‖(WithLp.toLp 2 (f ∘ Sum.inr) : EuclideanSpace ℝ (Fin d))‖
    linarith
  · refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    have h := sq_nonneg ‖(WithLp.toLp 2 (f ∘ Sum.inl) : EuclideanSpace ℝ (Fin d))‖
    linarith

/-- The defining bound of `Ch02.matrixOperatorNorm`, read on plain vectors. -/
private theorem norm_toLp_mulVec_le (A : Mat d) (u : Vec d) :
    ‖(WithLp.toLp 2 (Matrix.mulVec A u) : EuclideanSpace ℝ (Fin d))‖ ≤
      Ch02.matrixOperatorNorm A * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ :=
  Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm A u

/-- One block row of the four-block bound: a row of two `d × d` blocks, applied
to two vectors of Euclidean norm at most `r`. -/
private theorem norm_toLp_row_le (A B : Mat d) (u v : Vec d) (r : ℝ)
    (hu : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ≤ r)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ≤ r) :
    ‖(WithLp.toLp 2 (Matrix.mulVec A u + Matrix.mulVec B v) :
        EuclideanSpace ℝ (Fin d))‖ ≤
      Ch02.matrixOperatorNorm A * r + Ch02.matrixOperatorNorm B * r := by
  have htri :
      ‖(WithLp.toLp 2 (Matrix.mulVec A u + Matrix.mulVec B v) :
          EuclideanSpace ℝ (Fin d))‖ ≤
        ‖(WithLp.toLp 2 (Matrix.mulVec A u) : EuclideanSpace ℝ (Fin d))‖ +
          ‖(WithLp.toLp 2 (Matrix.mulVec B v) : EuclideanSpace ℝ (Fin d))‖ := by
    rw [WithLp.toLp_add]
    exact norm_add_le _ _
  have hA := norm_toLp_mulVec_le A u
  have hB := norm_toLp_mulVec_le B v
  have hA' :
      Ch02.matrixOperatorNorm A * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ≤
        Ch02.matrixOperatorNorm A * r :=
    mul_le_mul_of_nonneg_left hu (Ch02.matrixOperatorNorm_nonneg _)
  have hB' :
      Ch02.matrixOperatorNorm B * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ≤
        Ch02.matrixOperatorNorm B * r :=
    mul_le_mul_of_nonneg_left hv (Ch02.matrixOperatorNorm_nonneg _)
  linarith

/-! ## The four-block bound -/

/-- **The full block operator norm is below the sum of its four block operator
norms.**  For every `2d × 2d` real matrix `X` over `BlockCoord d`, with no
symmetry or positivity hypothesis and with an absolute constant. -/
theorem norm_toEuclideanCLM_le_sum_matrixOperatorNorm_blocks (X : FullBlockMat d) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ ≤
      Ch02.matrixOperatorNorm (ofFullBlockMat X).upperLeft +
        Ch02.matrixOperatorNorm (ofFullBlockMat X).upperRight +
        Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerLeft +
        Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerRight := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (by
      have h1 := Ch02.matrixOperatorNorm_nonneg (ofFullBlockMat X).upperLeft
      have h2 := Ch02.matrixOperatorNorm_nonneg (ofFullBlockMat X).upperRight
      have h3 := Ch02.matrixOperatorNorm_nonneg (ofFullBlockMat X).lowerLeft
      have h4 := Ch02.matrixOperatorNorm_nonneg (ofFullBlockMat X).lowerRight
      linarith) ?_
  intro x
  set f : BlockCoord d → ℝ := x.ofLp
  have hx : x = (WithLp.toLp 2 f : EuclideanSpace ℝ (BlockCoord d)) := rfl
  have hsplit :
      Matrix.mulVec X f =
        Sum.elim
          (Matrix.mulVec (ofFullBlockMat X).upperLeft (f ∘ Sum.inl) +
            Matrix.mulVec (ofFullBlockMat X).upperRight (f ∘ Sum.inr))
          (Matrix.mulVec (ofFullBlockMat X).lowerLeft (f ∘ Sum.inl) +
            Matrix.mulVec (ofFullBlockMat X).lowerRight (f ∘ Sum.inr)) := by
    funext alpha
    cases alpha with
    | inl i =>
        simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
          Pi.add_apply, ofFullBlockMat, Function.comp_apply]
    | inr i =>
        simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inr,
          Pi.add_apply, ofFullBlockMat, Function.comp_apply]
  have hvalue :
      (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X) x =
        (WithLp.toLp 2 (Matrix.mulVec X f) : EuclideanSpace ℝ (BlockCoord d)) := by
    rw [hx]
    exact Matrix.toEuclideanCLM_toLp X f
  have hhalves := norm_toLp_comp_le f
  have hupper :=
    norm_toLp_row_le (ofFullBlockMat X).upperLeft (ofFullBlockMat X).upperRight
      (f ∘ Sum.inl) (f ∘ Sum.inr) ‖x‖ (hx ▸ hhalves.1) (hx ▸ hhalves.2)
  have hlower :=
    norm_toLp_row_le (ofFullBlockMat X).lowerLeft (ofFullBlockMat X).lowerRight
      (f ∘ Sum.inl) (f ∘ Sum.inr) ‖x‖ (hx ▸ hhalves.1) (hx ▸ hhalves.2)
  have hcombine := norm_toLp_sum_elim_le
    (Matrix.mulVec (ofFullBlockMat X).upperLeft (f ∘ Sum.inl) +
      Matrix.mulVec (ofFullBlockMat X).upperRight (f ∘ Sum.inr))
    (Matrix.mulVec (ofFullBlockMat X).lowerLeft (f ∘ Sum.inl) +
      Matrix.mulVec (ofFullBlockMat X).lowerRight (f ∘ Sum.inr))
  rw [hvalue, hsplit]
  have hring :
      (Ch02.matrixOperatorNorm (ofFullBlockMat X).upperLeft +
            Ch02.matrixOperatorNorm (ofFullBlockMat X).upperRight +
            Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerLeft +
            Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerRight) * ‖x‖ =
        Ch02.matrixOperatorNorm (ofFullBlockMat X).upperLeft * ‖x‖ +
          Ch02.matrixOperatorNorm (ofFullBlockMat X).upperRight * ‖x‖ +
          Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerLeft * ‖x‖ +
          Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerRight * ‖x‖ := by
    ring
  linarith

/-! ## The two-scalar block gauge -/

/-- Absolute homogeneity of the `d × d` Euclidean operator norm. -/
private theorem matrixOperatorNorm_smul (c : ℝ) (A : Mat d) :
    Ch02.matrixOperatorNorm (c • A) = |c| * Ch02.matrixOperatorNorm A := by
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • A)‖ =
    |c| * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- **Conjugation by the two-scalar block gauge `diag(s 𝟙, t 𝟙)` weights the four
block norms by `s²`, `|st|`, `|st|`, `t²`.**  This is the gauge weighting of
the manuscript's `𝐁^{1/2} · 𝐁^{1/2}` conjugation at an isotropic comparator `𝐁
= 𝐁(σ)`, whose `CFC.sqrt` is exactly the diagonal matrix with `√σ` on the first
block coordinates and `(√σ)⁻¹` on the second: taking `s = √σ` and `t =
(√σ)⁻¹` turns the four weights into `σ`, `1`, `1`, `σ⁻¹`, the asymmetry
printed in the manuscript's variance display. -/
theorem norm_toEuclideanCLM_diagonal_mul_mul_diagonal_le (s t : ℝ) (X : FullBlockMat d) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (Matrix.diagonal (Sum.elim (fun _ => s) (fun _ => t)) * X *
          Matrix.diagonal (Sum.elim (fun _ => s) (fun _ => t)))‖ ≤
      s ^ (2 : ℕ) * Ch02.matrixOperatorNorm (ofFullBlockMat X).upperLeft +
        |s * t| * Ch02.matrixOperatorNorm (ofFullBlockMat X).upperRight +
        |s * t| * Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerLeft +
        t ^ (2 : ℕ) * Ch02.matrixOperatorNorm (ofFullBlockMat X).lowerRight := by
  set D : FullBlockMat d :=
    Matrix.diagonal (Sum.elim (fun _ => s) (fun _ => t)) with hD
  have hUL : (ofFullBlockMat (D * X * D)).upperLeft =
      (s * s) • (ofFullBlockMat X).upperLeft := by
    ext i j
    change (D * X * D) (Sum.inl i) (Sum.inl j) = s * s * X (Sum.inl i) (Sum.inl j)
    simp only [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, Sum.elim_inl]
    ring
  have hUR : (ofFullBlockMat (D * X * D)).upperRight =
      (s * t) • (ofFullBlockMat X).upperRight := by
    ext i j
    change (D * X * D) (Sum.inl i) (Sum.inr j) = s * t * X (Sum.inl i) (Sum.inr j)
    simp only [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, Sum.elim_inl, Sum.elim_inr]
    ring
  have hLL : (ofFullBlockMat (D * X * D)).lowerLeft =
      (s * t) • (ofFullBlockMat X).lowerLeft := by
    ext i j
    change (D * X * D) (Sum.inr i) (Sum.inl j) = s * t * X (Sum.inr i) (Sum.inl j)
    simp only [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, Sum.elim_inl, Sum.elim_inr]
    ring
  have hLR : (ofFullBlockMat (D * X * D)).lowerRight =
      (t * t) • (ofFullBlockMat X).lowerRight := by
    ext i j
    change (D * X * D) (Sum.inr i) (Sum.inr j) = t * t * X (Sum.inr i) (Sum.inr j)
    simp only [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, Sum.elim_inr]
    ring
  have hbound := norm_toEuclideanCLM_le_sum_matrixOperatorNorm_blocks (D * X * D)
  rw [hUL, hUR, hLL, hLR, matrixOperatorNorm_smul, matrixOperatorNorm_smul,
    matrixOperatorNorm_smul, matrixOperatorNorm_smul] at hbound
  have hs : |s * s| = s ^ (2 : ℕ) := by
    rw [abs_of_nonneg (mul_self_nonneg s), pow_two]
  have ht : |t * t| = t ^ (2 : ℕ) := by
    rw [abs_of_nonneg (mul_self_nonneg t), pow_two]
  rwa [hs, ht] at hbound

end

end Algsuperdiff.Section3.Provider.Homogenization
