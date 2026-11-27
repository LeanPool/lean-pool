/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ProductSourceReserveTransport
public import LeanPool.VacuumBellSeparation.FreeField.ProductSourceCovariancePerturbation
public import LeanPool.VacuumBellSeparation.Gaussian.CrossRankOneSeries
public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryNuclearTrace

/-!
# Actual full-source reserve factors from regional cross-kernel series

An actual expansion of the original cross covariance, together with
summable weighted regional vectors, constructs the bounded compact factor
on the source space used by finite compression. Both operator and nuclear
bounds refer to that same factor. The weighted moment and Fourier-kernel
estimates supplying these vectors are proved in other modules for regions in two
separated balls (`exists_spatial_source_reserve_estimate` in
`FreeField/SpatialSourceReserveEstimate.lean`).
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal

variable {m : ℝ} (hm : 0 < m) (U W : Set (EuclideanSpace ℝ (Fin 3)))
  {ι : Type*}

theorem exists_productSource_reserve_factor_of_cross_series
    {b : ℝ} (hb : 0 ≤ b)
    (u : ι → ComplexSourceHilbert hm U) (v : ι → ComplexSourceHilbert hm W)
    (hs : Summable fun i => ‖u i‖ * ‖v i‖)
    (hseries : HasSum
      (fun i => crossRankOne ((sourceReserve hm U ^ b) (u i)) ((sourceReserve hm W ^ b) (v i)))
      ((productSourceComplexEquiv hm U W).conjStarAlgEquiv
        (complexify (productSourceCovariancePerturbation hm U W)))) :
    ∃ Y : HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) →L[ℂ]
        HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)),
      complexify (productSourceCovariancePerturbation hm U W) =
        reserve (normalizedCommutation (complexify (productSourceCommutation hm (UA := U)
          (UB := W)))) ^ b *
          Y * reserve (normalizedCommutation (complexify (productSourceCommutation hm (UA := U)
            (UB := W)))) ^ b ∧
      IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
      ‖Y‖ ≤ ∑' i, ‖u i‖ * ‖v i‖ ∧
      operatorTraceNorm Y ≤ ENNReal.ofReal (2 * ∑' i, ‖u i‖ * ‖v i‖) ∧
      operatorTraceNorm Y < ∞ := by
  let e := productSourceComplexEquiv hm U W
  let X := ∑' i, crossRankOne (u i) (v i)
  let R := complexHilbertProductOperator (sourceReserve hm U ^ b) (sourceReserve hm W ^ b)
  let Y := e.symm.conjStarAlgEquiv X
  have hn := summable_norm_crossRankOne hs
  have hXc : IsCompactOperator X :=
    isCompactOperator_tsum_of_summable (fun i => crossRankOne_isCompactOperator _ _) hn.of_norm
  have hXa : IsSelfAdjoint X := isSelfAdjoint_tsum fun i => crossRankOne_isSelfAdjoint _ _
  have hterm (i : ι) : R * crossRankOne (u i) (v i) * R =
      crossRankOne ((sourceReserve hm U ^ b) (u i)) ((sourceReserve hm W ^ b) (v i)) :=
    crossRankOne_block_factorization CFC.rpow_nonneg.isSelfAdjoint CFC.rpow_nonneg.isSelfAdjoint _ _
  have hsum : HasSum
      (fun i => crossRankOne ((sourceReserve hm U ^ b) (u i)) ((sourceReserve hm W ^ b) (v i)))
      (R * X * R) := by
    simpa only [hterm] using (hn.of_norm.hasSum.mul_left R).mul_right R
  have hD := hseries.unique hsum
  have hYn : ‖Y‖ ≤ ∑' i, ‖u i‖ * ‖v i‖ := by
    dsimp only [Y]
    rw [norm_conjStarAlgEquiv]
    exact norm_crossRankOne_tsum_le hs
  have hYt : operatorTraceNorm Y ≤ ENNReal.ofReal (2 * ∑' i, ‖u i‖ * ‖v i‖) := by
    dsimp only [Y]
    rw [operatorTraceNorm_conjStarAlgEquiv]
    exact operatorTraceNorm_crossRankOne_tsum_le hs
  refine ⟨Y, ?_, isCompactOperator_conjStarAlgEquiv e.symm hXc,
    isSelfAdjoint_conjStarAlgEquiv e.symm hXa, hYn, hYt, hYt.trans_lt ENNReal.ofReal_lt_top⟩
  apply e.conjStarAlgEquiv.injective
  rw [map_mul, map_mul]
  change e.conjStarAlgEquiv (complexify (productSourceCovariancePerturbation hm U W)) =
    e.conjStarAlgEquiv
      (reserve (normalizedCommutation (complexify (productSourceCommutation hm (UA := U)
        (UB := W)))) ^ b) *
        e.conjStarAlgEquiv (e.symm.conjStarAlgEquiv X) *
          e.conjStarAlgEquiv
            (reserve (normalizedCommutation (complexify (productSourceCommutation hm (UA := U)
              (UB := W)))) ^ b)
  rw [← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.apply_symm_apply]
  dsimp only [e]
  simp only [productSourceComplexEquiv_reserve_rpow hm U W hb]
  exact hD

end VacuumBellSeparation
