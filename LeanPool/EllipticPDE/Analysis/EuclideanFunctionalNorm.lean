/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2


/-!
# Norm of a functional on Euclidean space in standard coordinates

A continuous linear functional `L` on `EuclideanSpace ℝ (Fin n)` has squared norm equal to the
sum of the squares of its values on the standard basis vectors: `‖L‖² = ∑ i, (L (single i 1))²`.
Through the Fréchet-Riesz representation, `L (single i 1)` is the `i`-th coordinate of the Riesz
vector, and the identity is Parseval for that vector.

Applied to `L = fderiv ℝ φ x`, this expresses the squared gradient norm `‖fderiv ℝ φ x‖²` as the
sum of squared partial derivatives `∑ i, (∂ᵢ φ x)²`, the form in which the gradient `L²` norm of
`MeasureTheory.integral_sq_sub_translation_le` meets a Sobolev `H¹` gradient bound.
-/

@[expose] public section

open scoped RealInnerProductSpace
open InnerProductSpace

/-- The squared operator norm of a functional on Euclidean space is the sum of the squares of its
values on the standard basis vectors. -/
theorem norm_sq_clm_eq_sum_apply_single {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ i, (L (EuclideanSpace.single i 1)) ^ 2 := by
  set E := EuclideanSpace ℝ (Fin n)
  set v : E := (InnerProductSpace.toDual ℝ E).symm L with hv
  have hLv : (InnerProductSpace.toDual ℝ E) v = L := by
    rw [hv]; exact (InnerProductSpace.toDual ℝ E).apply_symm_apply L
  have hnorm : ‖L‖ = ‖v‖ := by
    rw [hv]; exact ((InnerProductSpace.toDual ℝ E).symm.norm_map L).symm
  have happ : ∀ i, L (EuclideanSpace.single i 1) = v i := by
    intro i
    rw [← hLv, InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_right]
    simp
  rw [hnorm, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [happ i, Real.norm_eq_abs, sq_abs]
