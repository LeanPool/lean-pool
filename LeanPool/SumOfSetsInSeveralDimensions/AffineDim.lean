/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine dimension of a finite set

The affine dimension of a finite set `S ⊆ ℝ^D` is the dimension of the direction of its affine
span. The direction of the affine span of `S` is the vector span of `S`, the subspace spanned by
the differences of the points of `S`.

## Main definitions

* `Finset.affineDim S`: the affine dimension of `S`.

## Main statements

* `Finset.affineDim_eq_finrank_vectorSpan`: `S.affineDim` is the dimension of `vectorSpan ℝ S`.
* `Finset.affineDim_eq_finrank_span_sub`: `S.affineDim` is the dimension of the span of `S - S`.
* `Finset.affineDim_mono`: the affine dimension is monotone.
* `Finset.affineDim_vadd_finset`, `Finset.affineDim_image_add_left`,
  `Finset.affineDim_image_add_right`, `Finset.affineDim_image_sub`: it is invariant under
  translation.
* `Finset.affineDim_add_one_le_card`: a nonempty set of affine dimension `d` has at least `d + 1`
  points.
-/

@[expose] public section

namespace Finset

open scoped Pointwise

variable {D : ℕ}

/-- The affine dimension of a finite set `S ⊆ ℝ^D`: the dimension of the direction of the affine
span of `S`. -/
noncomputable def affineDim (S : Finset (Fin D → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (S : Set (Fin D → ℝ))).direction

/-- The affine dimension of `S` is the dimension of the vector span of `S`. -/
lemma affineDim_eq_finrank_vectorSpan (S : Finset (Fin D → ℝ)) :
    S.affineDim = Module.finrank ℝ (vectorSpan ℝ (S : Set (Fin D → ℝ))) := by
  rw [affineDim, direction_affineSpan]

/-- The affine dimension of `S` is the dimension of the span of `S - S`. -/
lemma affineDim_eq_finrank_span_sub (S : Finset (Fin D → ℝ)) :
    S.affineDim = Module.finrank ℝ (Submodule.span ℝ (↑S - ↑S : Set (Fin D → ℝ))) := by
  rw [affineDim_eq_finrank_vectorSpan, vectorSpan_def]
  rfl

/-- Affine dimension is monotone under inclusion of finite sets. -/
lemma affineDim_mono {S T : Finset (Fin D → ℝ)}
    (hST : S ⊆ T) : S.affineDim ≤ T.affineDim := by
  unfold affineDim
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono
  simpa using hST

/-- The affine dimension of a subset of `ℝ^D` is at most `D`. -/
lemma affineDim_le (S : Finset (Fin D → ℝ)) : S.affineDim ≤ D :=
  (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun ℝ)

@[simp]
lemma affineDim_empty : (∅ : Finset (Fin D → ℝ)).affineDim = 0 := by
  simp [affineDim_eq_finrank_vectorSpan]

@[simp]
lemma affineDim_singleton (x : Fin D → ℝ) : ({x} : Finset (Fin D → ℝ)).affineDim = 0 := by
  simp [affineDim_eq_finrank_vectorSpan]

/-- The affine dimension is invariant under translation. -/
@[simp]
lemma affineDim_vadd_finset (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (c +ᵥ S).affineDim = S.affineDim := by
  rw [affineDim_eq_finrank_vectorSpan, coe_vadd_finset, vectorSpan_vadd,
    affineDim_eq_finrank_vectorSpan]

/-- The affine dimension of `c + S` is that of `S`. -/
lemma affineDim_image_add_left (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (S.image (c + ·)).affineDim = S.affineDim :=
  affineDim_vadd_finset c S

/-- The affine dimension of `S + c` is that of `S`. -/
lemma affineDim_image_add_right (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (S.image (· + c)).affineDim = S.affineDim := by
  simp only [add_comm _ c, affineDim_image_add_left]

/-- The affine dimension of `S - c` is that of `S`. -/
lemma affineDim_image_sub (S : Finset (Fin D → ℝ)) (c : Fin D → ℝ) :
    (S.image fun x ↦ x - c).affineDim = S.affineDim := by
  simp only [sub_eq_add_neg, affineDim_image_add_right]

/-- A nonempty finite set of affine dimension `d` contains at least `d + 1` points. -/
lemma affineDim_add_one_le_card {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) :
    S.affineDim + 1 ≤ #S := by
  have : Nonempty (S : Set (Fin D → ℝ)) := hS.to_set.to_subtype
  have h := finrank_vectorSpan_range_add_one_le ℝ ((↑) : ↥(S : Set (Fin D → ℝ)) → Fin D → ℝ)
  rw [Subtype.range_coe, ← affineDim_eq_finrank_vectorSpan] at h
  simpa using h

/-- The affine dimension of a finite set is at most its number of points. -/
lemma affineDim_le_card (S : Finset (Fin D → ℝ)) : S.affineDim ≤ #S := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · simp
  · grind [affineDim_add_one_le_card hS]

end Finset
