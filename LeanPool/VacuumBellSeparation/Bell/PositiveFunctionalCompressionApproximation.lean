/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.PositiveStateCompression

/-!
Projection compression converges in the full dual norm when lost mass
vanishes. No normalization, nonzero functional or positive total mass is
assumed. The quantitative factor uses the actual continuous functional norm.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder

variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

private theorem functional_sqrt_star_mul_le (φ : C →ₚ[ℂ] ℂ) (x : C) :
    Real.sqrt ‖φ (star x * x)‖ ≤
      Real.sqrt ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖ * ‖x‖ := by
  let K := ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_⟩
  calc
    ‖φ (star x * x)‖ ≤ K * ‖star x * x‖ :=
      (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap.le_opNorm _
    _ = K * ‖x‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]
    _ = (Real.sqrt K * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]

private theorem functional_sqrt_mul_star_le (φ : C →ₚ[ℂ] ℂ) (x : C) :
    Real.sqrt ‖φ (x * star x)‖ ≤
      Real.sqrt ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖ * ‖x‖ := by
  simpa only [star_star, norm_star] using functional_sqrt_star_mul_le φ (star x)

/-- Uniform error on every observable for an arbitrary positive functional. -/
theorem positiveFunctional_compression_apply_error_le (φ : C →ₚ[ℂ] ℂ)
    (q : C) (hq : IsStarProjection q) (x : C) :
    ‖φ x - compressionFunctional φ q x‖ ≤
      2 * Real.sqrt ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖ *
        Real.sqrt ‖φ (1 - q)‖ * ‖x‖ := by
  let K := Real.sqrt ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖
  let e := 1 - q
  have he : IsStarProjection e := hq.one_sub
  have hleft : ‖φ (e * x)‖ ≤ Real.sqrt ‖φ e‖ * (K * ‖x‖) := by
    have h := PositiveLinearMap.cauchy_schwarz_star_mul φ e x
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (functional_sqrt_star_mul_le φ x) (Real.sqrt_nonneg _))
  have hright : ‖φ (q * x * e)‖ ≤ (K * ‖x‖) * Real.sqrt ‖φ e‖ := by
    have h := PositiveLinearMap.cauchy_schwarz_mul_star φ (q * x) e
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq] at h
    have hn : ‖q * x‖ ≤ ‖x‖ := calc
      ‖q * x‖ ≤ ‖q‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (IsStarProjection.norm_le q hq) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
    exact h.trans (mul_le_mul_of_nonneg_right
      ((functional_sqrt_mul_star_le φ (q * x)).trans
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _))
  have hx : x - star q * x * q = e * x + q * x * e := by
    rw [hq.isSelfAdjoint.star_eq]
    dsimp [e]
    noncomm_ring
  calc
    ‖φ x - compressionFunctional φ q x‖ = ‖φ (e * x) + φ (q * x * e)‖ := by
      rw [compressionFunctional_apply, ← map_sub, hx, map_add]
    _ ≤ ‖φ (e * x)‖ + ‖φ (q * x * e)‖ := norm_add_le _ _
    _ ≤ Real.sqrt ‖φ e‖ * (K * ‖x‖) + (K * ‖x‖) * Real.sqrt ‖φ e‖ :=
      add_le_add hleft hright
    _ = _ := by dsimp [K, e]; ring

/-- The estimate is the norm of the entire dual, with no unit-mass premise. -/
theorem positiveFunctional_compression_dual_error_le (φ : C →ₚ[ℂ] ℂ)
    (q : C) (hq : IsStarProjection q) :
    ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap - compressionDual φ q‖ ≤
      2 * Real.sqrt ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖ *
        Real.sqrt ‖φ (1 - q)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact positiveFunctional_compression_apply_error_le φ q hq

/-- Arbitrary filter version, including zero functionals and zero spaces. -/
theorem positiveFunctional_compression_tendsto_of_lost_mass_zero
    (φ : C →ₚ[ℂ] ℂ) {ι : Type*} {l : Filter ι}
    (q : ι → C) (hq : ∀ i, IsStarProjection (q i))
    (hm : Tendsto (fun i => ‖φ (1 - q i)‖) l (𝓝 0)) :
    Tendsto (fun i => compressionDual φ (q i)) l
      (𝓝 (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun i =>
      2 * Real.sqrt ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖ *
        Real.sqrt ‖φ (1 - q i)‖) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using hm.sqrt.const_mul
      (2 * Real.sqrt ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap‖)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  exact Eventually.of_forall fun i => by
    rw [norm_sub_rev]
    exact positiveFunctional_compression_dual_error_le φ (q i) (hq i)

end VacuumBellSeparation.Bipartite
