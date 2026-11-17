/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Ranges of `rTensor` against a free module

Let `𝒞` be a basis of `N`. An element of `P ⊗[R] N` lies in the range of `f.rTensor N` if and only
if each of its coordinates with respect to `𝒞` lies in the range of `f`.

## Main statements

* `TensorProduct.equivFinsuppOfBasisRight_rTensor`: the coordinates of `f.rTensor N x` are the
  images under `f` of the coordinates of `x`.
* `TensorProduct.mem_range_rTensor_iff_equivFinsuppOfBasisRight`.
-/

public section

noncomputable section

open LinearMap Module

open scoped TensorProduct

variable {R M N : Type*} {κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

variable [DecidableEq κ] (𝒞 : Basis κ R N)

/-- The coordinates of `f.rTensor N x` are the images under `f` of the coordinates of `x`. -/
lemma TensorProduct.equivFinsuppOfBasisRight_rTensor {P : Type*} [AddCommMonoid P] [Module R P]
    (f : M →ₗ[R] P) (x : M ⊗[R] N) :
    equivFinsuppOfBasisRight 𝒞 (f.rTensor N x) =
      (equivFinsuppOfBasisRight 𝒞 x).mapRange f f.map_zero := by
  induction x with
  | tmul m n => ext; simp
  | add x y hx hy => simp [hx, hy, Finsupp.mapRange_add (map_add f)]

/-- Let `𝒞` be a basis of `N`. An element of `P ⊗[R] N` lies in the range of `f.rTensor N` if and
only if each of its coordinates with respect to `𝒞` lies in the range of `f`. -/
lemma TensorProduct.mem_range_rTensor_iff_equivFinsuppOfBasisRight {P : Type*} [AddCommMonoid P]
    [Module R P] (f : M →ₗ[R] P) (x : P ⊗[R] N) :
    x ∈ range (f.rTensor N) ↔ ∀ i, equivFinsuppOfBasisRight 𝒞 x i ∈ range f := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨y, rfl⟩ i
    simp [equivFinsuppOfBasisRight_rTensor]
  choose g hg using h
  rw [← (equivFinsuppOfBasisRight 𝒞).symm_apply_apply x, equivFinsuppOfBasisRight_symm_apply]
  exact Submodule.sum_mem _ fun i _ ↦ ⟨g i ⊗ₜ 𝒞 i, by simp [hg]⟩

end
