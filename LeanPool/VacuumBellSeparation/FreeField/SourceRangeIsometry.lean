/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ModularWeightInclusion

/-!
# Source isometries induced by physical unitaries

A physical unitary carrying the actual completed real source range into
another such range induces an isometry of the original completions. Its
complexification compresses the actual Gram operator exactly. The source
weight estimate follows from operator concavity, including zero spectrum.
The range inclusion is an explicit hypothesis here, to be proved from
localization in each application.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap Gaussian

variable {m : ℝ} (hm : 0 < m)
  {U W : Set (EuclideanSpace ℝ (Fin 3))}
  (T : Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m))
  (hT : ∀ z : SourceHilbert hm U,
    T (sourceEmbedding hm U z) ∈ sourceRealSpace hm W)

/-- Source range map. -/
noncomputable def sourceRangeMap : SourceHilbert hm U →ₗᵢ[ℝ] sourceRealSpace hm W where
  toFun z := ⟨T (sourceEmbedding hm U z), hT z⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := by
    apply Subtype.ext
    change T (sourceEmbedding hm U (a • x)) = a • T (sourceEmbedding hm U x)
    rw [map_smul]
    exact T.toLinearEquiv.toLinearMap.map_smul_of_tower a (sourceEmbedding hm U x)
  norm_map' z := by
    change ‖T (sourceEmbedding hm U z)‖ = ‖z‖
    rw [T.norm_map, (sourceEmbedding hm U).norm_map]

/-- Source range isometry of type `SourceHilbert hm U →ₗᵢ[ℝ] SourceHilbert hm W`. -/
noncomputable def sourceRangeIsometry : SourceHilbert hm U →ₗᵢ[ℝ] SourceHilbert hm W :=
  (sourceEmbedding hm W).equivRange.symm.toLinearIsometry.comp (sourceRangeMap hm T hT)

theorem sourceEmbedding_rangeIsometry (z : SourceHilbert hm U) :
    sourceEmbedding hm W (sourceRangeIsometry hm T hT z) = T (sourceEmbedding hm U z) := by
  exact congrArg Subtype.val ((sourceEmbedding hm W).equivRange.apply_symm_apply
    (sourceRangeMap hm T hT z))

/-- Complex source range isometry of type `ComplexSourceHilbert hm U →ₗᵢ[ℂ] ComplexSourceHilbert hm
W`. -/
noncomputable def complexSourceRangeIsometry :
    ComplexSourceHilbert hm U →ₗᵢ[ℂ] ComplexSourceHilbert hm W :=
  complexifyIsometry (sourceRangeIsometry hm T hT)

theorem complexSourceMap_rangeIsometry (z : ComplexSourceHilbert hm U) :
    complexSourceMap hm W (complexSourceRangeIsometry hm T hT z) =
      T (complexSourceMap hm U z) := by
  change sourceEmbedding hm W (sourceRangeIsometry hm T hT z.re) +
    Complex.I • sourceEmbedding hm W (sourceRangeIsometry hm T hT z.im) =
      T (sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U z.im)
  rw [sourceEmbedding_rangeIsometry, sourceEmbedding_rangeIsometry, map_add, map_smul]

theorem sourceGram_rangeIsometry_compression :
    compression (complexSourceRangeIsometry hm T hT) (sourceGram hm W) = sourceGram hm U := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_left ℂ
  intro w
  change inner ℂ w ((complexSourceRangeIsometry hm T hT).toContinuousLinearMap.adjoint
    ((complexSourceMap hm W).adjoint
      (complexSourceMap hm W (complexSourceRangeIsometry hm T hT z)))) =
    inner ℂ w ((complexSourceMap hm U).adjoint (complexSourceMap hm U z))
  rw [adjoint_inner_right, adjoint_inner_right, adjoint_inner_right]
  change inner ℂ (complexSourceMap hm W (complexSourceRangeIsometry hm T hT w))
      (complexSourceMap hm W (complexSourceRangeIsometry hm T hT z)) =
    inner ℂ (complexSourceMap hm U w) (complexSourceMap hm U z)
  rw [complexSourceMap_rangeIsometry, complexSourceMap_rangeIsometry, T.inner_map_map]

theorem sourceNormalizedCommutation_rangeIsometry_compression :
    compression (complexSourceRangeIsometry hm T hT)
      (normalizedCommutation (complexSourceCommutation hm W)) =
        normalizedCommutation (complexSourceCommutation hm U) := by
  have heq (V : Set (EuclideanSpace ℝ (Fin 3))) :
      normalizedCommutation (complexSourceCommutation hm V) = sourceGram hm V - 1 := by
    rw [sourceGram_eq_normalized_commutation]
    change (Complex.I / 2) • complexSourceCommutation hm V =
      1 + (Complex.I / 2) • complexSourceCommutation hm V - 1
    abel
  rw [heq W, heq U, compression_sub, compression_one,
    sourceGram_rangeIsometry_compression]

theorem sourceModularWeight_rangeIsometry_square_compression
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    compression (complexSourceRangeIsometry hm T hT)
      ((sourceModularWeight hm W c).adjoint * sourceModularWeight hm W c) ≤
        (sourceModularWeight hm U c).adjoint * sourceModularWeight hm U c := by
  rw [sourceModularWeight_adjoint_mul hm W hc.le hc2,
    sourceModularWeight_adjoint_mul hm U hc.le hc2,
    ← sourceNormalizedCommutation_rangeIsometry_compression hm T hT]
  exact modularWeight_compression (complexSourceRangeIsometry hm T hT)
    (normalizedCommutation_isSelfAdjoint (complexSourceCommutation_mem_skewAdjoint hm W))
    (norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm W))
    (by linarith) (by linarith)

theorem sourceModularWeight_rangeIsometry_norm
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (z : ComplexSourceHilbert hm U) :
    ‖sourceModularWeight hm W c (complexSourceRangeIsometry hm T hT z)‖ ≤
      ‖sourceModularWeight hm U c z‖ := by
  let J := (complexSourceRangeIsometry hm T hT).toContinuousLinearMap
  let A := sourceModularWeight hm W c
  let B := sourceModularWeight hm U c
  have hleft : ‖A (J z)‖ ^ 2 =
      (inner ℂ z (compression (complexSourceRangeIsometry hm T hT) (A.adjoint * A) z)).re := by
    change ‖(A ∘L J) z‖ ^ 2 = _
    rw [(A ∘L J).apply_norm_sq_eq_inner_adjoint_right, adjoint_comp]
    rfl
  have hright : ‖B z‖ ^ 2 = (inner ℂ z ((B.adjoint * B) z)).re :=
    B.apply_norm_sq_eq_inner_adjoint_right z
  have hh := (nonneg_iff_isPositive.mp (sub_nonneg.mpr
    (sourceModularWeight_rangeIsometry_square_compression hm T hT hc hc2))).re_inner_nonneg_right z
  change 0 ≤ (inner ℂ z ((B.adjoint * B -
    compression (complexSourceRangeIsometry hm T hT) (A.adjoint * A)) z)).re at hh
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hh
  rw [← hleft, ← hright] at hh
  change ‖A (J z)‖ ≤ ‖B z‖
  nlinarith [norm_nonneg (A (J z)), norm_nonneg (B z)]

end VacuumBellSeparation
