/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SymmetricRankOneTrace
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertProductFunctionalCalculus

/-!
# Cross-kernel series on the actual regional Hilbert product

Each term is a rank-one cross map and its adjoint. Orthogonality of the
two factors gives the operator-norm bound without a factor two; the
genuine nuclear bound has the factor two required by the manuscript.
Actual block reserves reconstruct the unweighted vectors term by term.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap InnerProductSpace
open scoped ENNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {ι : Type*}

/-- Continuous linear map for the cross rank one, of type `WithLp 2 (E × F) →L[ℂ] WithLp 2 (E ×
F)`. -/
def crossRankOne (u : E) (v : F) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  symmetricRankOne (WithLp.toLp 2 (u, (0 : F))) (WithLp.toLp 2 ((0 : E), v))

omit [InnerProductSpace ℂ E] [CompleteSpace E] [InnerProductSpace ℂ F] [CompleteSpace F] in
theorem norm_hilbertProduct_left (u : E) : ‖WithLp.toLp 2 (u, (0 : F))‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

omit [InnerProductSpace ℂ E] [CompleteSpace E] [InnerProductSpace ℂ F] [CompleteSpace F] in
theorem norm_hilbertProduct_right (v : F) : ‖WithLp.toLp 2 ((0 : E), v)‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem crossRankOne_apply (u : E) (v : F) (z : WithLp 2 (E × F)) :
    crossRankOne u v z = WithLp.toLp 2 (inner ℂ v z.snd • u, inner ℂ u z.fst • v) := by
  apply WithLp.ofLp_injective 2
  simp [crossRankOne, symmetricRankOne, rankOne_apply, WithLp.prod_inner_apply]

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_crossRankOne_le (u : E) (v : F) : ‖crossRankOne u v‖ ≤ ‖u‖ * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_nonneg _))).mp
  rw [crossRankOne_apply, WithLp.prod_norm_sq_eq_of_L2, mul_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖inner ℂ v z.snd • u‖ ^ 2 + ‖inner ℂ u z.fst • v‖ ^ 2 ≤
    (‖u‖ * ‖v‖) ^ 2 * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)
  have hu := norm_inner_le_norm (𝕜 := ℂ) u z.fst
  have hv := norm_inner_le_norm (𝕜 := ℂ) v z.snd
  rw [norm_smul, norm_smul]
  calc
    _ ≤ (‖v‖ * ‖z.snd‖ * ‖u‖) ^ 2 + (‖u‖ * ‖z.fst‖ * ‖v‖) ^ 2 := by gcongr
    _ = _ := by ring

omit [CompleteSpace E] [CompleteSpace F] in
theorem crossRankOne_isCompactOperator (u : E) (v : F) : IsCompactOperator (crossRankOne u v) :=
  symmetricRankOne_isCompactOperator _ _

theorem crossRankOne_isSelfAdjoint (u : E) (v : F) : IsSelfAdjoint (crossRankOne u v) :=
  symmetricRankOne_isSelfAdjoint _ _

theorem operatorTraceNorm_crossRankOne_le (u : E) (v : F) :
    operatorTraceNorm (crossRankOne u v) ≤ ENNReal.ofReal (2 * (‖u‖ * ‖v‖)) := by
  simpa only [crossRankOne, norm_hilbertProduct_left, norm_hilbertProduct_right] using
    operatorTraceNorm_symmetricRankOne_le
      (WithLp.toLp 2 (u, (0 : F))) (WithLp.toLp 2 ((0 : E), v))

omit [CompleteSpace E] [CompleteSpace F] in
theorem summable_norm_crossRankOne {u : ι → E} {v : ι → F}
    (hs : Summable fun i => ‖u i‖ * ‖v i‖) : Summable fun i => ‖crossRankOne (u i) (v i)‖ :=
  Summable.of_nonneg_of_le (fun _i => norm_nonneg _) (fun _i => norm_crossRankOne_le _ _) hs

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_crossRankOne_tsum_le {u : ι → E} {v : ι → F}
    (hs : Summable fun i => ‖u i‖ * ‖v i‖) :
    ‖∑' i, crossRankOne (u i) (v i)‖ ≤ ∑' i, ‖u i‖ * ‖v i‖ := by
  have hn := summable_norm_crossRankOne hs
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun i => norm_crossRankOne_le _ _) hs)

theorem operatorTraceNorm_crossRankOne_tsum_le {u : ι → E} {v : ι → F}
    (hs : Summable fun i => ‖u i‖ * ‖v i‖) :
    operatorTraceNorm (∑' i, crossRankOne (u i) (v i)) ≤
      ENNReal.ofReal (2 * ∑' i, ‖u i‖ * ‖v i‖) := by
  have hs' : Summable fun i =>
      ‖WithLp.toLp 2 (u i, (0 : F))‖ * ‖WithLp.toLp 2 ((0 : E), v i)‖ := by
    simpa only [norm_hilbertProduct_left, norm_hilbertProduct_right] using hs
  simpa only [crossRankOne, norm_hilbertProduct_left, norm_hilbertProduct_right] using
    operatorTraceNorm_symmetricRankOne_tsum_le hs'

theorem crossRankOne_block_factorization {R : E →L[ℂ] E} {S : F →L[ℂ] F}
    (hR : IsSelfAdjoint R) (hS : IsSelfAdjoint S) (u : E) (v : F) :
    complexHilbertProductOperator R S * crossRankOne u v * complexHilbertProductOperator R S =
      crossRankOne (R u) (S v) := by
  ext z
  simp only [mul_apply_eq_comp, crossRankOne_apply, complexHilbertProductOperator_apply]
  apply WithLp.ofLp_injective 2
  change (R (inner ℂ v (S z.snd) • u), S (inner ℂ u (R z.fst) • v)) =
    (inner ℂ (S v) z.snd • R u, inner ℂ (R u) z.fst • S v)
  rw [map_smul, map_smul, ← S.adjoint_inner_left, ← R.adjoint_inner_left,
    hS.adjoint_eq, hR.adjoint_eq]

end VacuumBellSeparation.Gaussian
