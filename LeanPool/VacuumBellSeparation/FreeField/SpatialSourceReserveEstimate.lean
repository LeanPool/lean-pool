/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CenteredWeightedSourceMoments
public import LeanPool.VacuumBellSeparation.FreeField.SpatialSourceReserveFactor

/-!
# Actual separated-source reserve factor and its quantitative norms

The original polynomial moment vectors are now constructed from the
completed weighted evaluation theorem. Combined with the actual kernel
series they give the factorization without any analytic moment or
kernel-series hypotheses.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification
open scoped BigOperators ENNReal

/-- Source field moment envelope given by `C * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m
* T)`. -/
def sourceFieldMomentEnvelope (C b m T : ℝ) : ℝ :=
  C * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m * T)

/-- Source momentum moment envelope given by `C * T ^ 2 / (1 + m * T) ^ 2 * Real.exp
(sourceMomentLambda b * m * T)`. -/
def sourceMomentumMomentEnvelope (C b m T : ℝ) : ℝ :=
  C * T ^ 2 / (1 + m * T) ^ 2 * Real.exp (sourceMomentLambda b * m * T)

/-- Spatial source factor bound. -/
def spatialSourceFactorBound (C b m s T : ℝ) : ℝ :=
  64 * spatialFieldPolydiscBound m s (2 * (sourceMomentBase b * T)) *
      sourceFieldMomentEnvelope C b m T ^ 2 +
    64 * spatialMomentumPolydiscBound m s (2 * (sourceMomentBase b * T)) *
      sourceMomentumMomentEnvelope C b m T ^ 2

theorem centeredSpatialTestMoment_zero (f : SpatialTestFunction) (α : Fin 3 → ℕ) :
    centeredSpatialTestMoment 0 f α = spatialRealTestMoment f α := by
  have hf : spatialTestTranslate (-(0 : EuclideanSpace ℝ (Fin 3))) f = f := by
    apply Subtype.ext
    funext x
    simp only [spatialTestTranslate, neg_zero, sub_zero]
  rw [centeredSpatialTestMoment, hf]

theorem exists_spatial_source_reserve_estimate {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T) (s : ℝ),
        16 * Real.sqrt 3 * (sourceMomentBase b * T) ≤ s →
        ∀ (U W : Set (EuclideanSpace ℝ (Fin 3))),
          U ⊆ Metric.ball 0 T → W ⊆ Metric.ball (spatialAxisDisplacement s 0) T →
          ∃ Y : HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) →L[ℂ]
              HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)),
            complexify (productSourceCovariancePerturbation hm U W) =
              reserve (normalizedCommutation
                (complexify (productSourceCommutation hm (UA := U) (UB := W)))) ^ b *
                Y * reserve (normalizedCommutation
                  (complexify (productSourceCommutation hm (UA := U) (UB := W)))) ^ b ∧
            IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
            ‖Y‖ ≤ spatialSourceFactorBound C b m s T ∧
            operatorTraceNorm Y ≤ ENNReal.ofReal (2 * spatialSourceFactorBound C b m s T) ∧
            operatorTraceNorm Y < ∞ := by
  obtain ⟨C, hC, hvec⟩ := exists_centered_weightedSource_moment_vectors hb hb1
  refine ⟨C, hC, ?_⟩
  intro m hm T hT s hsep U W hU hW
  let B := sourceMomentBase b * T
  have hB : 0 < B := by
    dsimp [B, sourceMomentBase]
    exact mul_pos (mul_pos (by norm_num) (sourceMomentLambda_pos hb hb1)) hT
  have hTB : T ≤ B := by
    have hΛ := one_le_sourceMomentLambda hb hb1
    dsimp [B, sourceMomentBase]
    nlinarith
  have hs : 0 < s := (show 0 < 16 * Real.sqrt 3 * B by positivity).trans_le hsep
  have hAf : 0 ≤ sourceFieldMomentEnvelope C b m T := by
    unfold sourceFieldMomentEnvelope
    positivity
  have hAp : 0 ≤ sourceMomentumMomentEnvelope C b m T := by
    unfold sourceMomentumMomentEnvelope
    positivity
  choose uf ug huf hug heuf heug using hvec m hm T hT 0 U hU
  choose vf vg hvf hvg hevf hevg using hvec m hm T hT (spatialAxisDisplacement s 0) W hW
  let u : SpatialCrossIndex → ComplexSourceHilbert hm U :=
    Sum.elim (fun k => uf k.1) (fun k => ug k.1)
  let v : SpatialCrossIndex → ComplexSourceHilbert hm W :=
    Sum.elim (fun k => vf k.2) (fun k => vg k.2)
  have hun (i : SpatialCrossIndex) (x : SourceTestSpace hm U) :
      inner ℂ (ofReal (x : SourceHilbert hm U)) ((sourceReserve hm U ^ b) (u i)) =
        (spatialCrossLeftMoment i x.1 : ℂ) := by
    cases i with
    | inl k => simpa only [u, Sum.elim_inl, spatialCrossLeftMoment,
        centeredSpatialTestMoment_zero] using heuf k.1 x
    | inr k => simpa only [u, Sum.elim_inr, spatialCrossLeftMoment,
        centeredSpatialTestMoment_zero] using heug k.1 x
  have hvn (i : SpatialCrossIndex) (x : SourceTestSpace hm W) :
      inner ℂ (ofReal (x : SourceHilbert hm W)) ((sourceReserve hm W ^ b) (v i)) =
        (spatialCrossRightMoment s i x.1 : ℂ) := by
    cases i with
    | inl k => exact hevf k.2 x
    | inr k => exact hevg k.2 x
  obtain ⟨hsum, hnorm⟩ := spatialCross_weighted_vector_series hm hs hB hAf hAp
    hsep u v (fun k => huf k.1) (fun k => hug k.1)
      (fun k => hvf k.2) (fun k => hvg k.2)
  have hnorm' : (∑' i, ‖(spatialCrossCoefficient m s (2 * B) i : ℂ) • u i‖ * ‖v i‖) ≤
      spatialSourceFactorBound C b m s T := by
    simpa only [spatialSourceFactorBound, B, sourceFieldMomentEnvelope,
      sourceMomentumMomentEnvelope, pow_two, mul_assoc] using hnorm
  have hUc : ∀ x ∈ U, ∀ j, ‖x j‖ ≤ (2 * B) / 2 := by
    intro x hx j
    have hn : ‖x‖ < T := by simpa only [Metric.mem_ball, dist_zero_right] using hU hx
    exact (PiLp.norm_apply_le x j).trans (hn.le.trans (by linarith))
  have hWc : ∀ x ∈ W, ∀ j, ‖(x - spatialAxisDisplacement s 0) j‖ ≤ (2 * B) / 2 := by
    intro x hx j
    have hn : ‖x - spatialAxisDisplacement s 0‖ < T := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hW hx
    exact (PiLp.norm_apply_le _ j).trans (hn.le.trans (by linarith))
  obtain ⟨Y, hfac, hc, hsa, hY, hY₁, hfin⟩ := exists_spatial_source_reserve_factor hm hs
    (show 0 < 2 * B by positivity) (show 8 * Real.sqrt 3 * (2 * B) ≤ s by nlinarith)
    (show 0 ≤ b by linarith) hUc hWc u v hsum hun hvn
  refine ⟨Y, hfac, hc, hsa, hY.trans hnorm', hY₁.trans ?_, hfin⟩
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnorm' (by norm_num))

end VacuumBellSeparation
