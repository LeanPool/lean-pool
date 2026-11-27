/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Aesop.Main
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Tactic.TypeStar

/-!
# Algebraic reserve compression

The direct square comparison in Lemma 4.4, "Compression of thermal weights",
of the manuscript.

For a self-adjoint operator `B = i J / 2` and an isometric embedding `ι`, the
difference between the compressed reserve square and the compression of the
reserve square is

`1 - (ι* B ι)² - ι* (1 - B²) ι = ι* B (1 - ι ι*) B ι ≥ 0`.

This identity holds for arbitrary complex Hilbert spaces. The definitions here
are the explicit operators in this equation, with no Gaussian or compression
theorem assumed as a structure field.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Compression `ι* A ι` along an isometric embedding. -/
noncomputable def compression (ι : E →ₗᵢ[ℂ] F) (A : F →L[ℂ] F) : E →L[ℂ] E :=
  ι.toContinuousLinearMap.adjoint ∘L A ∘L ι.toContinuousLinearMap

/-- The orthogonal projection `ι ι*` onto the image of an isometric embedding. -/
noncomputable def imageProjection (ι : E →ₗᵢ[ℂ] F) : F →L[ℂ] F :=
  ι.toContinuousLinearMap ∘L ι.toContinuousLinearMap.adjoint

/-- The square of the manuscript's reserve, `1 - B²`, before imposing positivity. -/
def reserveSquare (B : F →L[ℂ] F) : F →L[ℂ] F := 1 - B ^ 2

/-- The positive reserve `sqrt (1 - B²)`. Its intended domain is the
self-adjoint contractions, for which the argument is positive. -/
noncomputable def reserve (B : F →L[ℂ] F) : F →L[ℂ] F :=
  CFC.sqrt (reserveSquare B)

@[simp]
theorem adjoint_embedding_apply (ι : E →ₗᵢ[ℂ] F) (x : E) :
    ι.toContinuousLinearMap.adjoint (ι x) = x := by
  simpa only [comp_apply, one_apply_eq_self, LinearIsometry.coe_toContinuousLinearMap] using
    DFunLike.congr_fun ι.adjoint_comp_self x

@[simp]
theorem compression_one (ι : E →ₗᵢ[ℂ] F) :
    compression ι 1 = 1 := by
  ext x
  simp [compression]

@[simp]
theorem compression_sub (ι : E →ₗᵢ[ℂ] F) (A B : F →L[ℂ] F) :
    compression ι (A - B) = compression ι A - compression ι B := by
  ext x
  simp [compression]

/-- Compression preserves positivity. -/
theorem compression_nonneg (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F} (h : 0 ≤ A) :
    0 ≤ compression ι A :=
  nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp h).adjoint_conj
    ι.toContinuousLinearMap)

/-- Compression preserves self-adjointness. -/
theorem compression_isSelfAdjoint (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (compression ι A) :=
  hA.adjoint_conj ι.toContinuousLinearMap

/-- A self-adjoint contraction has positive reserve square. -/
theorem reserveSquare_nonneg {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) : 0 ≤ reserveSquare B := by
  rw [reserveSquare, sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (B ^ 2),
    pow_two, hB.norm_mul_self]
  nlinarith [norm_nonneg B]

/-- Compression preserves the operator order. -/
theorem compression_mono (ι : E →ₗᵢ[ℂ] F) {A B : F →L[ℂ] F} (h : A ≤ B) :
    compression ι A ≤ compression ι B := by
  rw [le_def, ← compression_sub]
  exact (le_def.mp h).adjoint_conj ι.toContinuousLinearMap

/-- The operator `ι ι*` really is a star projection. -/
theorem imageProjection_isStarProjection (ι : E →ₗᵢ[ℂ] F) :
    IsStarProjection (imageProjection ι) := by
  constructor
  · change imageProjection ι * imageProjection ι = imageProjection ι
    ext x
    simp [imageProjection, mul_apply_eq_comp]
  · change star (imageProjection ι) = imageProjection ι
    simp [imageProjection, star_eq_adjoint]

/-- The orthogonal complement of the image projection is positive. -/
theorem one_sub_imageProjection_nonneg (ι : E →ₗᵢ[ℂ] F) :
    0 ≤ 1 - imageProjection ι := by
  exact nonneg_iff_isPositive.mpr
    (.of_isStarProjection (imageProjection_isStarProjection ι).one_sub)

/-- The direct reserve-square identity in the proof of manuscript Lemma 4.4. -/
theorem reserveSquare_compression_sub (ι : E →ₗᵢ[ℂ] F) (B : F →L[ℂ] F) :
    reserveSquare (compression ι B) - compression ι (reserveSquare B) =
      compression ι (B * (1 - imageProjection ι) * B) := by
  ext x
  simp only [reserveSquare, compression, imageProjection, pow_two, comp_apply,
    mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub,
    LinearIsometry.coe_toContinuousLinearMap, adjoint_embedding_apply]
  abel

/-- The square reserve increases under compression, for self-adjoint `B`.
No finite-dimensionality or strict contraction assumption is needed for this
algebraic inequality. -/
theorem compression_reserveSquare_le (ι : E →ₗᵢ[ℂ] F) {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) :
    compression ι (reserveSquare B) ≤ reserveSquare (compression ι B) := by
  rw [← sub_nonneg, reserveSquare_compression_sub, nonneg_iff_isPositive]
  have hP := (nonneg_iff_isPositive.mp (one_sub_imageProjection_nonneg ι)).adjoint_conj
    (B ∘L ι.toContinuousLinearMap)
  have hBadj : B.adjoint = B := by simpa only [star_eq_adjoint] using hB.star_eq
  simpa only [compression, adjoint_comp, hBadj, mul_def, comp_assoc] using hP

/-- If the full reserve square is positive, so is the compressed reserve square. -/
theorem reserveSquare_compression_nonneg (ι : E →ₗᵢ[ℂ] F) {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) (hR : 0 ≤ reserveSquare B) :
    0 ≤ reserveSquare (compression ι B) := by
  have hcomp : 0 ≤ compression ι (reserveSquare B) :=
    nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hR).adjoint_conj
      ι.toContinuousLinearMap)
  exact hcomp.trans (compression_reserveSquare_le ι hB)

/-- The quadratic compression inequality, obtained from the reserve-square
identity by cancelling the identity operators. -/
theorem compression_sq_le (ι : E →ₗᵢ[ℂ] F) {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) :
    (compression ι B) ^ 2 ≤ compression ι (B ^ 2) := by
  have h := compression_reserveSquare_le ι hB
  simpa only [reserveSquare, compression_sub, compression_one, sub_le_sub_iff_left] using h

/-- Square-root Jensen inequality for a Hilbert-space compression. This is
derived from the quadratic compression inequality and Mathlib's operator
monotonicity of the square root. -/
theorem compression_sqrt_le (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F} (hA : 0 ≤ A) :
    compression ι (CFC.sqrt A) ≤ CFC.sqrt (compression ι A) := by
  have h := compression_sq_le ι (CFC.sqrt_nonneg A).isSelfAdjoint
  rw [CFC.sq_sqrt A hA] at h
  have hs := CFC.sqrt_le_sqrt _ _ h
  rwa [CFC.sqrt_sq _ (compression_nonneg ι (CFC.sqrt_nonneg A))] at hs

/-- The low-compression claim of Lemma 4.4 at `a = 1/2`:
`ι* R ι ≤ R_F`. This is valid also for infinite-dimensional source spaces and
noninvertible reserve operators. -/
theorem compression_reserve_le (ι : E →ₗᵢ[ℂ] F) {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) (hR : 0 ≤ reserveSquare B) :
    compression ι (reserve B) ≤ reserve (compression ι B) := by
  exact (compression_sqrt_le ι hR).trans
    (CFC.sqrt_le_sqrt _ _ (compression_reserveSquare_le ι hB))

/-- The `a = 1/2` low-compression bound in the manuscript's natural domain of
self-adjoint contractions. -/
theorem compression_reserve_le_of_norm_le_one (ι : E →ₗᵢ[ℂ] F) {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) :
    compression ι (reserve B) ≤ reserve (compression ι B) :=
  compression_reserve_le ι hB (reserveSquare_nonneg hB hnorm)

end VacuumBellSeparation.Gaussian
