/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceReserveDefs
public import LeanPool.VacuumBellSeparation.FreeField.SourceGramStrictness
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCommutation

/-!
# The physical source uncertainty reserve

The reserve is the actual positive square root of G times its conjugate,
where G is the Gram operator of the completed physical source map. Bounded
regions give injectivity, not a uniform spectral gap or a bounded inverse.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem conjugateSourceGram_eq :
    conjugateSourceGram hm U = 1 - (Complex.I / 2) • complexSourceCommutation hm U :=
  Gaussian.conjugate_sourceMap_gram (sourceEmbedding hm U)

theorem conjugateSourceGram_eq_two_sub :
    conjugateSourceGram hm U = 2 - sourceGram hm U := by
  rw [conjugateSourceGram_eq, sourceGram_eq_normalized_commutation]
  rw [show (2 : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) = 1 + 1 from
    (one_add_one_eq_two).symm]
  abel

theorem sourceGram_commute_conjugateSourceGram :
    Commute (sourceGram hm U) (conjugateSourceGram hm U) := by
  rw [sourceGram_eq_normalized_commutation, conjugateSourceGram_eq]
  exact Gaussian.gramPlus_commute_gramMinus _

theorem conjugateSourceGram_nonneg : 0 ≤ conjugateSourceGram hm U := by
  rw [conjugateSourceGram_eq]
  exact Gaussian.gramMinus_nonneg
    (Gaussian.normalizedCommutation_isSelfAdjoint
      (complexSourceCommutation_mem_skewAdjoint hm U))
    (Gaussian.norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm U))

theorem sourceGram_mul_conjugateSourceGram_eq :
    sourceGram hm U * conjugateSourceGram hm U =
      Gaussian.reserveSquare (Gaussian.normalizedCommutation (complexSourceCommutation hm U)) := by
  rw [sourceGram_eq_normalized_commutation, conjugateSourceGram_eq]
  exact Gaussian.gramPlus_mul_gramMinus _

theorem sourceGram_mul_conjugateSourceGram_nonneg :
    0 ≤ sourceGram hm U * conjugateSourceGram hm U := by
  rw [sourceGram_mul_conjugateSourceGram_eq]
  exact Gaussian.reserveSquare_nonneg
    (Gaussian.normalizedCommutation_isSelfAdjoint
      (complexSourceCommutation_mem_skewAdjoint hm U))
    (Gaussian.norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm U))

theorem sourceReserve_eq_normalized_reserve :
    sourceReserve hm U =
      Gaussian.reserve (Gaussian.normalizedCommutation (complexSourceCommutation hm U)) := by
  rw [sourceReserve, sourceGram_mul_conjugateSourceGram_eq]
  rfl

theorem sourceReserve_nonneg : 0 ≤ sourceReserve hm U := CFC.sqrt_nonneg _

theorem sourceReserve_isSelfAdjoint : IsSelfAdjoint (sourceReserve hm U) :=
  (sourceReserve_nonneg hm U).isSelfAdjoint

theorem sourceReserve_mul_self :
    sourceReserve hm U * sourceReserve hm U = sourceGram hm U * conjugateSourceGram hm U :=
  CFC.sqrt_mul_sqrt_self _ (sourceGram_mul_conjugateSourceGram_nonneg hm U)

theorem sourceReserve_le_one : sourceReserve hm U ≤ 1 := by
  have hB := Gaussian.normalizedCommutation_isSelfAdjoint
    (complexSourceCommutation_mem_skewAdjoint hm U)
  have hsq : 0 ≤ (Gaussian.normalizedCommutation (complexSourceCommutation hm U)) ^ 2 := by
    simpa only [pow_two, hB.star_eq] using
      star_mul_self_nonneg (Gaussian.normalizedCommutation (complexSourceCommutation hm U))
  have hle : sourceGram hm U * conjugateSourceGram hm U ≤ 1 := by
    rw [sourceGram_mul_conjugateSourceGram_eq, Gaussian.reserveSquare]
    exact sub_le_self _ hsq
  simpa only [sourceReserve, CFC.sqrt_one] using CFC.sqrt_le_sqrt _ _ hle

/-- The physical bounded-region reserve is injective even when zero is in its spectrum. -/
theorem sourceReserve_injective (hU : Bornology.IsBounded U) :
    Function.Injective (sourceReserve hm U) := by
  intro x y hxy
  apply conjugateSourceGram_injective hm U hU
  apply sourceGram_injective hm U hU
  change (sourceGram hm U * conjugateSourceGram hm U) x =
    (sourceGram hm U * conjugateSourceGram hm U) y
  rw [← sourceReserve_mul_self]
  change sourceReserve hm U (sourceReserve hm U x) = sourceReserve hm U (sourceReserve hm U y)
  rw [hxy]

/-- Strict positivity here is positivity on each nonzero vector, with no uniform lower bound. -/
theorem inner_sourceReserve_pos (hU : Bornology.IsBounded U)
    (x : ComplexSourceHilbert hm U) (hx : x ≠ 0) :
    0 < (inner ℂ x (sourceReserve hm U x)).re := by
  let T := CFC.sqrt (sourceReserve hm U)
  have hTT : T.adjoint.comp T = sourceReserve hm U := by
    change star T * T = sourceReserve hm U
    rw [(CFC.sqrt_nonneg (sourceReserve hm U)).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sourceReserve_nonneg hm U)
  have hTx : T x ≠ 0 := by
    intro h
    apply hx
    apply sourceReserve_injective hm U hU
    rw [map_zero, ← hTT]
    change T.adjoint (T x) = 0
    rw [h, map_zero]
  change 0 < RCLike.re (inner ℂ x (sourceReserve hm U x))
  rw [← hTT, ← T.apply_norm_sq_eq_inner_adjoint_right]
  exact sq_pos_of_pos (norm_pos_iff.mpr hTx)

end VacuumBellSeparation
