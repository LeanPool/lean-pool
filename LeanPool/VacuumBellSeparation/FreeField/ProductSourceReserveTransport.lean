/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePairSourceCompression
public import LeanPool.VacuumBellSeparation.FreeField.SourceReserve
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertProductFunctionalCalculus

/-!
# Separate regional reserves in the actual product-source coordinates

The full source compression uses the complexification of a real Hilbert
product. The explicit coordinate unitary identifies its commutation
operator and reserve powers with the blocks of the original regional
source operators. This is valid at a zero spectral endpoint and assumes
no bounded inverse of a reserve.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m) (U W : Set (EuclideanSpace ℝ (Fin 3)))

/-- Product source complex equivalence defined as `complexificationProductEquiv`. -/
def productSourceComplexEquiv :
    HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) ≃ₗᵢ[ℂ]
      WithLp 2 (ComplexSourceHilbert hm U × ComplexSourceHilbert hm W) :=
  complexificationProductEquiv

theorem productSourceComplexEquiv_commutation :
    (productSourceComplexEquiv hm U W).conjStarAlgEquiv
      (complexify (productSourceCommutation hm (UA := U) (UB := W))) =
        complexHilbertProductOperator (complexSourceCommutation hm U)
          (complexSourceCommutation hm W) :=
  complexificationProductEquiv_conjugate (sourceCommutation hm U) (sourceCommutation hm W)

theorem productSourceComplexEquiv_normalized_commutation :
    (productSourceComplexEquiv hm U W).conjStarAlgEquiv
      (normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W)))) =
        complexHilbertProductOperator (normalizedCommutation (complexSourceCommutation hm U))
          (normalizedCommutation (complexSourceCommutation hm W)) := by
  have hs := (productSourceComplexEquiv hm U W).conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.map_smul
    (Complex.I / 2) (complexify (productSourceCommutation hm (UA := U) (UB := W)))
  change (productSourceComplexEquiv hm U W).conjStarAlgEquiv
      ((Complex.I / 2) • complexify (productSourceCommutation hm (UA := U) (UB := W))) =
    (Complex.I / 2) • (productSourceComplexEquiv hm U W).conjStarAlgEquiv
      (complexify (productSourceCommutation hm (UA := U) (UB := W))) at hs
  rw [normalizedCommutation, hs, productSourceComplexEquiv_commutation]
  ext z
  rfl

theorem productSourceComplexEquiv_reserve :
    (productSourceComplexEquiv hm U W).conjStarAlgEquiv
      (reserve (normalizedCommutation (complexify (productSourceCommutation hm (UA := U)
        (UB := W))))) =
        complexHilbertProductOperator (sourceReserve hm U) (sourceReserve hm W) := by
  let B := normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W)))
  have hB : IsSelfAdjoint B := productSource_normalizedCommutation_isSelfAdjoint hm
  have hn : ‖B‖ ≤ 1 := productSource_normalizedCommutation_norm_le_one hm
  have hmap : (productSourceComplexEquiv hm U W).conjStarAlgEquiv (reserve B) =
      reserve ((productSourceComplexEquiv hm U W).conjStarAlgEquiv B) := by
    rw [reserve, CFC.sqrt_eq_rpow,
      conjStarAlgEquiv_rpow _ (reserveSquare_nonneg hB hn) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      reserveSquare, map_sub, map_one, map_pow]
    rw [reserve, CFC.sqrt_eq_rpow]
    rfl
  change (productSourceComplexEquiv hm U W).conjStarAlgEquiv (reserve B) = _
  rw [hmap]
  dsimp only [B]
  rw [productSourceComplexEquiv_normalized_commutation,
    complexHilbertProductOperator_reserve
      (normalizedCommutation_isSelfAdjoint (complexSourceCommutation_mem_skewAdjoint hm U))
      (norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm U))
      (normalizedCommutation_isSelfAdjoint (complexSourceCommutation_mem_skewAdjoint hm W))
      (norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm W)),
    ← sourceReserve_eq_normalized_reserve, ← sourceReserve_eq_normalized_reserve]

theorem productSourceComplexEquiv_reserve_rpow {b : ℝ} (hb : 0 ≤ b) :
    (productSourceComplexEquiv hm U W).conjStarAlgEquiv
      (reserve (normalizedCommutation (complexify (productSourceCommutation hm (UA := U)
        (UB := W)))) ^ b) =
        complexHilbertProductOperator (sourceReserve hm U ^ b) (sourceReserve hm W ^ b) := by
  let B : HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) →L[ℂ]
      HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) :=
    normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W)))
  have hR : 0 ≤ reserve B := CFC.sqrt_nonneg (reserveSquare B)
  have hp := conjStarAlgEquiv_rpow (productSourceComplexEquiv hm U W)
    (A := reserve B) (τ := b) hR hb
  change (productSourceComplexEquiv hm U W).conjStarAlgEquiv (reserve B ^ b) = _
  rw [hp]
  dsimp only [B]
  rw [productSourceComplexEquiv_reserve]
  exact complexHilbertProductOperator_rpow
    (A := sourceReserve hm U) (B := sourceReserve hm W) (p := b)
    (sourceReserve_nonneg hm U) (sourceReserve_nonneg hm W) hb

end VacuumBellSeparation
