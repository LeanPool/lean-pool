/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.ProperIsometryMatrixUnits

/-!
# Strong decay of orthogonal projections

Finite sums of mutually orthogonal star projections are themselves star
projections. Their norm bound yields Bessel's estimate for every original
Hilbert-space vector. Summability of squared norms then gives strong decay.
No completeness of the projection family or sum-to-identity assumption is used.
-/

@[expose] public section

universe u v
namespace VacuumBellSeparation

open Filter
open scoped Topology InnerProductSpace BigOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every finite partial sum is an actual orthogonal projection. -/
theorem isStarProjection_sum_of_pairwise {ι : Type v} (P : ι → H →L[ℂ] H)
    (hp : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) (s : Finset ι) :
    IsStarProjection (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IsStarProjection.zero (H →L[ℂ] H)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply (hp i).add ih
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact horth (by intro he; subst j; exact hi hj)

/-- Idempotence and self-adjointness identify the actual projected square norm. -/
theorem re_inner_projection_apply (P : H →L[ℂ] H) (hp : IsStarProjection P) (x : H) :
    RCLike.re ⟪P x, x⟫_ℂ = ‖P x‖ ^ 2 := by
  have hid : P (P x) = P x := by
    change (P * P) x = P x
    rw [(isStarProjection_iff'.mp hp).1]
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hp.isSelfAdjoint) (P x) x
  change ⟪P (P x), x⟫_ℂ = ⟪P x, P x⟫_ℂ at hs
  rw [hid] at hs
  calc
    RCLike.re ⟪P x, x⟫_ℂ = RCLike.re ⟪P x, P x⟫_ℂ := congrArg RCLike.re hs
    _ = ‖P x‖ ^ 2 := (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (P x)).symm

/-- Bessel's finite inequality for arbitrary mutually orthogonal projections. -/
theorem sum_norm_projection_sq_le {ι : Type v} (P : ι → H →L[ℂ] H)
    (hp : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) (s : Finset ι) (x : H) :
    ∑ i ∈ s, ‖P i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let Q : H →L[ℂ] H := ∑ i ∈ s, P i
  have hQ : IsStarProjection Q := isStarProjection_sum_of_pairwise P hp horth s
  have hQx : ‖Q x‖ ≤ ‖x‖ := (Q.le_opNorm x).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (IsStarProjection.norm_le Q hQ) (norm_nonneg x))
  calc
    ∑ i ∈ s, ‖P i x‖ ^ 2 = ∑ i ∈ s, RCLike.re ⟪P i x, x⟫_ℂ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (re_inner_projection_apply (P i) (hp i) x).symm
    _ = RCLike.re ⟪Q x, x⟫_ℂ := by
      simp only [Q, sum_apply, sum_inner, map_sum]
    _ ≤ ‖⟪Q x, x⟫_ℂ‖ := RCLike.re_le_norm _
    _ ≤ ‖Q x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ ^ 2 := (mul_le_mul_of_nonneg_right hQx (norm_nonneg x)).trans_eq (by ring)

/-- No separability of H and no completeness of the family are required. -/
theorem summable_norm_projection_sq (P : ℕ → H →L[ℂ] H)
    (hp : ∀ n, IsStarProjection (P n))
    (horth : Pairwise (fun i j => P i * P j = 0)) (x : H) :
    Summable (fun n => ‖P n x‖ ^ 2) := by
  exact summable_of_sum_le (fun n => sq_nonneg ‖P n x‖)
    (fun s => sum_norm_projection_sq_le P hp horth s x)

/-- Strong convergence means convergence at every vector of the full H. -/
theorem orthogonal_projections_strong_tendsto_zero (P : ℕ → H →L[ℂ] H)
    (hp : ∀ n, IsStarProjection (P n))
    (horth : Pairwise (fun i j => P i * P j = 0)) (x : H) :
    Tendsto (fun n => P n x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (summable_norm_projection_sq P hp horth x).tendsto_atTop_zero.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- The two adjacent corners used in the Bell construction also vanish strongly. -/
theorem adjacent_orthogonal_corners_strong_tendsto_zero (P : ℕ → H →L[ℂ] H)
    (hp : ∀ n, IsStarProjection (P n))
    (horth : Pairwise (fun i j => P i * P j = 0)) (x : H) :
    Tendsto (fun n => (P n + P (n + 1)) x) atTop (𝓝 0) := by
  have h := orthogonal_projections_strong_tendsto_zero P hp horth x
  have hs := h.comp (tendsto_add_atTop_nat 1)
  simpa only [add_apply, Function.comp_def, zero_add] using h.add hs

namespace ProperIsometry

/-- The actual matrix-unit diagonal family of one isometry tends strongly to
zero, even when its sum is a proper subprojection of the identity. -/
theorem diagonal_strong_tendsto_zero {v : H →L[ℂ] H}
    (hv : star v * v = 1) (x : H) :
    Tendsto (fun n => matrixUnit v n n x) atTop (𝓝 0) := by
  exact orthogonal_projections_strong_tendsto_zero (fun n => matrixUnit v n n)
    (diagonal_projection hv) (fun i j hij => diagonal_orthogonal hv hij) x

theorem adjacent_corner_strong_tendsto_zero {v : H →L[ℂ] H}
    (hv : star v * v = 1) (x : H) :
    Tendsto (fun n => (matrixUnit v n n + matrixUnit v (n + 1) (n + 1)) x)
      atTop (𝓝 0) := by
  exact adjacent_orthogonal_corners_strong_tendsto_zero (fun n => matrixUnit v n n)
    (diagonal_projection hv) (fun i j hij => diagonal_orthogonal hv hij) x

end ProperIsometry
end VacuumBellSeparation
