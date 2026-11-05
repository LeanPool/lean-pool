/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.HyperbolicPair
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Cancelling a hyperbolic plane

The step of Witt cancellation that turns a statement about *isometries of a hyperbolic pair* into
a statement about *cancellation*: if every hyperbolic pair of `H ⊥ q₂` is the image of the standard
one under a self-isometry, then `H ⊥ q₁ ≅ H ⊥ q₂` implies `q₁ ≅ q₂`.

This is the second half of `Dias II.6.4` (`Baeza III (4.3)`), specialized to a hyperbolic plane and
written with mathlib's `QuadraticMap.prod` in place of an internal orthogonal decomposition. The
transitivity hypothesis it consumes is `Dias II.6.2`, whose general case is what needs the LG axiom;
its unit case is `QuadraticMap.IsHyperbolicPair.exists_isometryEquiv_of_isUnit`.

## Main results

* `QuadraticForm.isHyperbolicPair_plane_prod` : `((1,0), 0)` and `((0,1), 0)` form the standard
  hyperbolic pair of `plane ⊥ q`.
* `QuadraticForm.isometryEquivOfFixesPlane` : an isometry `plane ⊥ q₁ ≅ plane ⊥ q₂` fixing both
  members of the standard hyperbolic pair restricts to an isometry `q₁ ≅ q₂`. The mechanism is
  that a vector is in the second summand *exactly* when it is orthogonal to the pair, which is a
  two-line computation for the plane and needs no regularity of `q₁` or `q₂`.
* `QuadraticForm.isometryEquiv_of_isometryEquiv_plane_prod` : cancellation of a plane, given
  transitivity on hyperbolic pairs.

## References

* I. Dias, *Formas Quadráticas Sobre LG-Anéis*, Ph.D. thesis, Universidade Estadual de Campinas,
  1988, II.6.2 and II.6.4.
* R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Math. **655**, Springer 1978,
  III, (4.2) and (4.3).
-/

@[expose] public section

universe u v w

namespace QuadraticForm

open _root_.QuadraticMap (polar polar_prod polar_zero_left polar_zero_right
  IsHyperbolicPair)

variable {R : Type u} [CommRing R] {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
variable {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]

/-- The standard hyperbolic pair of `plane ⊥ q`. -/
theorem isHyperbolicPair_plane_prod (Q : QuadraticForm R M₁) :
    IsHyperbolicPair ((plane R).prod Q) ((1, 0), 0) ((0, 1), 0) where
  apply_left := by simp
  apply_right := by simp
  polar_eq_one := by
    rw [polar_prod, polar_plane]
    simp

/-- A vector of `plane ⊥ q` orthogonal to both members of the standard hyperbolic pair lies in the
second summand. This is the whole content of "the orthogonal complement of the plane is `q`", and
it needs nothing of `q`. -/
theorem fst_eq_zero_of_polar_eq_zero {Q : QuadraticForm R M₁} {x : (R × R) × M₁}
    (h₁ : polar ((plane R).prod Q) x ((1, 0), 0) = 0)
    (h₂ : polar ((plane R).prod Q) x ((0, 1), 0) = 0) : x.1 = 0 := by
  rw [polar_prod, polar_plane, polar_zero_right] at h₁ h₂
  simp only [mul_zero, mul_one, zero_add, add_zero] at h₁ h₂
  exact Prod.ext h₂ h₁

section FixesPlane

variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
variable (τ : ((plane R).prod Q₁).IsometryEquiv ((plane R).prod Q₂))
variable (hu : τ ((1, 0), 0) = ((1, 0), 0)) (hv : τ ((0, 1), 0) = ((0, 1), 0))

include hu hv in
/-- An isometry fixing the standard hyperbolic pair maps the second summand into the second
summand. -/
theorem fst_map_inr_eq_zero (m : M₁) : (τ (0, m)).1 = 0 := by
  refine fst_eq_zero_of_polar_eq_zero (Q := Q₂) ?_ ?_
  · rw [← hu, τ.polar_apply, polar_prod, polar_zero_left, polar_zero_right, add_zero]
  · rw [← hv, τ.polar_apply, polar_prod, polar_zero_left, polar_zero_right, add_zero]

/-- The restriction of `τ` to the second summand, as a linear map. -/
def restrictPlane : M₁ →ₗ[R] M₂ :=
  (LinearMap.snd R (R × R) M₂).comp ((τ : _ ≃ₗ[R] _).toLinearMap.comp (LinearMap.inr R (R × R) M₁))

@[simp] theorem restrictPlane_apply (m : M₁) : restrictPlane τ m = (τ (0, m)).2 := rfl

include hu hv in
theorem map_inr (m : M₁) : τ (0, m) = (0, restrictPlane τ m) :=
  Prod.ext (fst_map_inr_eq_zero τ hu hv m) rfl

include hu hv in
theorem apply_restrictPlane (m : M₁) : Q₂ (restrictPlane τ m) = Q₁ m := by
  have h := τ.map_app ((0, m) : (R × R) × M₁)
  rw [map_inr τ hu hv] at h
  simpa using h

include hu in
theorem symm_fixes_left : τ.symm ((1, 0), 0) = ((1, 0), 0) := by rw [← hu, τ.symm_apply_apply]

include hv in
theorem symm_fixes_right : τ.symm ((0, 1), 0) = ((0, 1), 0) := by rw [← hv, τ.symm_apply_apply]

include hu hv in
theorem restrictPlane_symm_restrictPlane (m : M₁) :
    restrictPlane τ.symm (restrictPlane τ m) = m := by
  have h2 := congrArg τ.symm (map_inr τ hu hv m)
  rw [τ.symm_apply_apply,
    map_inr τ.symm (symm_fixes_left τ hu) (symm_fixes_right τ hv)] at h2
  exact congrArg Prod.snd h2.symm

include hu hv in
theorem restrictPlane_restrictPlane_symm (n : M₂) :
    restrictPlane τ (restrictPlane τ.symm n) = n := by
  have h2 := congrArg τ
    (map_inr τ.symm (symm_fixes_left τ hu) (symm_fixes_right τ hv) n)
  rw [τ.apply_symm_apply, map_inr τ hu hv] at h2
  exact congrArg Prod.snd h2.symm

include hu hv in
/-- **An isometry `plane ⊥ q₁ ≅ plane ⊥ q₂` fixing the standard hyperbolic pair cancels the
plane.** -/
noncomputable def isometryEquivOfFixesPlane : Q₁.IsometryEquiv Q₂ where
  __ := LinearEquiv.ofBijective (restrictPlane τ)
    (Function.bijective_iff_has_inverse.2
      ⟨restrictPlane τ.symm, restrictPlane_symm_restrictPlane τ hu hv,
        restrictPlane_restrictPlane_symm τ hu hv⟩)
  map_app' := apply_restrictPlane τ hu hv

end FixesPlane

/-- **Cancellation of a hyperbolic plane**, given transitivity on hyperbolic pairs.

The hypothesis is `Dias II.6.2` for `plane ⊥ q₂`: every hyperbolic pair is the image of the
standard one under a self-isometry. Given it, `plane ⊥ q₁ ≅ plane ⊥ q₂` implies `q₁ ≅ q₂`, by
correcting the given isometry so that it fixes the standard pair and then restricting
(`QuadraticForm.isometryEquivOfFixesPlane`). -/
theorem isometryEquiv_of_isometryEquiv_plane_prod {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂}
    (htrans : ∀ i j : (R × R) × M₂, IsHyperbolicPair ((plane R).prod Q₂) i j →
      ∃ σ : ((plane R).prod Q₂).IsometryEquiv ((plane R).prod Q₂),
        σ ((1, 0), 0) = i ∧ σ ((0, 1), 0) = j)
    (h : Nonempty (((plane R).prod Q₁).IsometryEquiv ((plane R).prod Q₂))) :
    Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨e⟩ := h
  obtain ⟨σ, hσu, hσv⟩ :=
    htrans (e ((1, 0), 0)) (e ((0, 1), 0)) ((isHyperbolicPair_plane_prod Q₁).map e)
  refine ⟨isometryEquivOfFixesPlane (e.trans σ.symm) ?_ ?_⟩
  · change σ.symm (e ((1, 0), 0)) = _
    rw [← hσu, σ.symm_apply_apply]
  · change σ.symm (e ((0, 1), 0)) = _
    rw [← hσv, σ.symm_apply_apply]

end QuadraticForm
