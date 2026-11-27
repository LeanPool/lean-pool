/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DecorrelatedCovariance

/-!
# Decorrelation from actual complementary real label subspaces

The matrices are constructed from the genuine projections along the other
subspace. Their sum, idempotence, symplectic cross blocks and covariance
restrictions are proved. No orthogonal coordinate decomposition is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complementary label projection defined as `LinearMap.toMatrix' (L.projection R h)`. -/
def complementaryLabelProjection (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) :
    Matrix ι ι ℝ := LinearMap.toMatrix' (L.projection R h)

@[simp] theorem complementaryLabelProjection_mulVec
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) (x : ι → ℝ) :
    complementaryLabelProjection L R h *ᵥ x = L.projection R h x :=
  LinearMap.toMatrix'_mulVec _ _

theorem complementaryLabelProjection_add
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) :
    complementaryLabelProjection L R h + complementaryLabelProjection R L h.symm = 1 := by
  have he := congrArg LinearMap.toMatrix' (Submodule.projection_add_projection_eq_id h)
  simpa only [complementaryLabelProjection, map_add, LinearMap.toMatrix'_id] using he

theorem complementaryLabelProjection_idempotent
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) :
    complementaryLabelProjection L R h * complementaryLabelProjection L R h =
      complementaryLabelProjection L R h := by
  have he : L.projection R h * L.projection R h = L.projection R h :=
    Submodule.isIdempotentElem_projection h
  have hm := congrArg LinearMap.toMatrix' he
  simpa only [complementaryLabelProjection, LinearMap.toMatrix'_mul] using hm

omit [DecidableEq ι] in
theorem bilinear_mixed_congruence (P M Q : Matrix ι ι ℝ) (x y : ι → ℝ) :
    (P *ᵥ x) ⬝ᵥ (M *ᵥ (Q *ᵥ y)) = x ⬝ᵥ ((Pᵀ * M * Q) *ᵥ y) := by
  calc
    (P *ᵥ x) ⬝ᵥ (M *ᵥ (Q *ᵥ y)) =
        (M *ᵥ (Q *ᵥ y)) ⬝ᵥ ((Pᵀ)ᵀ *ᵥ x) := by
      rw [Matrix.transpose_transpose, dotProduct_comm]
    _ = x ⬝ᵥ (Pᵀ *ᵥ (M *ᵥ (Q *ᵥ y))) :=
      Matrix.dotProduct_transpose_mulVec Pᵀ _ x
    _ = x ⬝ᵥ ((Pᵀ * M * Q) *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem complementaryLabelProjection_cross_zero
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) (M : Matrix ι ι ℝ)
    (hcross : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (M *ᵥ y) = 0) :
    (complementaryLabelProjection L R h)ᵀ * M * complementaryLabelProjection R L h.symm = 0 := by
  ext i j
  have hc := hcross (L.projection R h (Pi.single i 1)) (Submodule.projection_apply_mem h _)
    (R.projection L h.symm (Pi.single j 1)) (Submodule.projection_apply_mem h.symm _)
  rw [← complementaryLabelProjection_mulVec L R h,
    ← complementaryLabelProjection_mulVec R L h.symm,
    bilinear_mixed_congruence] at hc
  simpa only [single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.zero_apply] using hc

omit [DecidableEq ι] in
theorem transpose_cross_zero_of_skew {Ω P Q : Matrix ι ι ℝ}
    (hΩ : Ωᵀ = -Ω) (hcross : Pᵀ * Ω * Q = 0) : Qᵀ * Ω * P = 0 := by
  have ht := congrArg Matrix.transpose hcross
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hΩ, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.transpose_zero, neg_eq_zero, Matrix.mul_assoc] using ht

/-- Label decorrelated covariance defined as `decorrelatedCovariance V
(complementaryLabelProjection L R h) (complementaryLabelProjection R L h.symm)`. -/
def labelDecorrelatedCovariance (V : Matrix ι ι ℝ)
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) : Matrix ι ι ℝ :=
  decorrelatedCovariance V (complementaryLabelProjection L R h)
    (complementaryLabelProjection R L h.symm)

theorem labelDecorrelatedCovariance_posDef {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R) :
    (labelDecorrelatedCovariance V L R h).PosDef :=
  decorrelatedCovariance_posDef hV (complementaryLabelProjection_add L R h)

theorem labelDecorrelatedCovariance_quantum_posDef {V Ω : Matrix ι ι ℝ}
    (hV : (quantumCovariance V Ω).PosDef) (hΩ : Ωᵀ = -Ω)
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R)
    (hcross : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (Ω *ᵥ y) = 0) :
    (quantumCovariance (labelDecorrelatedCovariance V L R h) Ω).PosDef := by
  have hc := complementaryLabelProjection_cross_zero L R h Ω hcross
  exact quantumCovariance_decorrelated_posDef hV (complementaryLabelProjection_add L R h)
    hc (transpose_cross_zero_of_skew hΩ hc)

theorem labelDecorrelatedCovariance_left_restriction (V : Matrix ι ι ℝ)
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R)
    {x y : ι → ℝ} (hx : x ∈ L) (hy : y ∈ L) :
    x ⬝ᵥ (labelDecorrelatedCovariance V L R h *ᵥ y) = x ⬝ᵥ (V *ᵥ y) := by
  let P := complementaryLabelProjection L R h
  let Q := complementaryLabelProjection R L h.symm
  have hPx : P *ᵥ x = x := by
    simpa only [P, complementaryLabelProjection_mulVec] using
      Submodule.projection_apply_of_mem_left h hx
  have hPy : P *ᵥ y = y := by
    simpa only [P, complementaryLabelProjection_mulVec] using
      Submodule.projection_apply_of_mem_left h hy
  have hr := decorrelatedCovariance_left_restriction V
    (complementaryLabelProjection_idempotent L R h) (complementaryLabelProjection_add L R h)
  calc
    _ = (P *ᵥ x) ⬝ᵥ (decorrelatedCovariance V P Q *ᵥ (P *ᵥ y)) := by rw [hPx, hPy]; rfl
    _ = x ⬝ᵥ ((Pᵀ * decorrelatedCovariance V P Q * P) *ᵥ y) :=
      bilinear_mixed_congruence P _ P x y
    _ = x ⬝ᵥ ((Pᵀ * V * P) *ᵥ y) := by rw [hr]
    _ = _ := by rw [← bilinear_mixed_congruence, hPx, hPy]

theorem labelDecorrelatedCovariance_right_restriction (V : Matrix ι ι ℝ)
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R)
    {x y : ι → ℝ} (hx : x ∈ R) (hy : y ∈ R) :
    x ⬝ᵥ (labelDecorrelatedCovariance V L R h *ᵥ y) = x ⬝ᵥ (V *ᵥ y) := by
  have hr := labelDecorrelatedCovariance_left_restriction V R L h.symm hx hy
  change x ⬝ᵥ (((complementaryLabelProjection R L h.symm)ᵀ * V *
      complementaryLabelProjection R L h.symm +
      (complementaryLabelProjection L R h)ᵀ * V * complementaryLabelProjection L R h) *ᵥ y) =
    x ⬝ᵥ (V *ᵥ y) at hr
  rw [add_comm] at hr
  exact hr

theorem labelDecorrelatedCovariance_cross (V : Matrix ι ι ℝ)
    (L R : Submodule ℝ (ι → ℝ)) (h : IsCompl L R)
    {x y : ι → ℝ} (hx : x ∈ L) (hy : y ∈ R) :
    x ⬝ᵥ (labelDecorrelatedCovariance V L R h *ᵥ y) = 0 := by
  let P := complementaryLabelProjection L R h
  let Q := complementaryLabelProjection R L h.symm
  have hPx : P *ᵥ x = x := by
    simpa only [P, complementaryLabelProjection_mulVec] using
      Submodule.projection_apply_of_mem_left h hx
  have hQy : Q *ᵥ y = y := by
    simpa only [Q, complementaryLabelProjection_mulVec] using
      Submodule.projection_apply_of_mem_left h.symm hy
  have hc := decorrelatedCovariance_cross V
    (complementaryLabelProjection_idempotent L R h) (complementaryLabelProjection_add L R h)
  calc
    _ = (P *ᵥ x) ⬝ᵥ (decorrelatedCovariance V P Q *ᵥ (Q *ᵥ y)) := by rw [hPx, hQy]; rfl
    _ = x ⬝ᵥ ((Pᵀ * decorrelatedCovariance V P Q * Q) *ᵥ y) :=
      bilinear_mixed_congruence P _ Q x y
    _ = 0 := by rw [hc]; simp

end VacuumBellSeparation.Gaussian
