/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SkewRotationPlane

/-!
# The invariant plane and the smaller real skew operator

The rotation pair gives an actual two-dimensional invariant subspace.
Restriction to its orthogonal complement retains both skew-adjointness
and injectivity, and reduces the dimension by two. These statements make
the induction step for a full skew normal form explicit.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The real subspace spanned by the two vectors used for a plane rotation. -/
def rotationPlane (x y : E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (![x, y] : Fin 2 → E))

omit [FiniteDimensional ℝ E] in
theorem orthonormal_rotationPair {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0) :
    Orthonormal ℝ (![x, y] : Fin 2 → E) := by
  have hyx : inner ℝ y x = 0 := (real_inner_comm x y).trans hxy
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hx, hy, hxy, hyx]

omit [FiniteDimensional ℝ E] in
theorem finrank_rotationPlane {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0) :
    Module.finrank ℝ (rotationPlane x y) = 2 := by
  convert! finrank_span_eq_card (orthonormal_rotationPair hx hy hxy).linearIndependent using 1

omit [FiniteDimensional ℝ E] in
theorem maps_rotationPlane (A : E →ₗ[ℝ] E) {ν : ℝ} {x y : E}
    (hAx : A x = ν • y) (hAy : A y = (-ν) • x) :
    ∀ z ∈ rotationPlane x y, A z ∈ rotationPlane x y := by
  have hx : x ∈ rotationPlane x y := Submodule.subset_span ⟨0, by simp⟩
  have hy : y ∈ rotationPlane x y := Submodule.subset_span ⟨1, by simp⟩
  have hle : rotationPlane x y ≤ (rotationPlane x y).comap A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change A (![x, y] i) ∈ rotationPlane x y
    fin_cases i
    · convert! (rotationPlane x y).smul_mem ν hy using 1
    · convert! (rotationPlane x y).smul_mem (-ν) hx using 1
  exact fun z hz => hle hz

theorem real_skew_restrict (A : E →ₗ[ℝ] E) (hA : A.adjoint = -A)
    (P : Submodule ℝ E) (hP : ∀ x ∈ P, A x ∈ P) :
    (A.restrict hP).adjoint = -(A.restrict hP) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [LinearMap.adjoint_inner_right]
  change inner ℝ (A (y : E)) (x : E) = inner ℝ (y : E) (-(A (x : E)))
  have h := A.adjoint_inner_right (y : E) (x : E)
  rw [hA, LinearMap.neg_apply] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
theorem injective_restrict (A : E →ₗ[ℝ] E) (hinj : Function.Injective A)
    (P : Submodule ℝ E) (hP : ∀ x ∈ P, A x ∈ P) :
    Function.Injective (A.restrict hP) := by
  intro x y hxy
  apply Subtype.ext
  apply hinj
  exact congrArg Subtype.val hxy

/-- A genuine two-dimensional invariant plane with an injective skew
restriction on its orthogonal complement and the exact dimension drop. -/
theorem exists_skew_invariant_plane [Nontrivial E]
    (A : E →ₗ[ℝ] E) (hA : A.adjoint = -A) (hinj : Function.Injective A) :
    ∃ P : Submodule ℝ E,
      Module.finrank ℝ P = 2 ∧
      (∀ x ∈ P, A x ∈ P) ∧
      ∃ hP : ∀ x ∈ Pᗮ, A x ∈ Pᗮ,
        (A.restrict hP).adjoint = -(A.restrict hP) ∧
        Function.Injective (A.restrict hP) ∧
        Module.finrank ℝ Pᗮ + 2 = Module.finrank ℝ E := by
  obtain ⟨ν, x, y, _, hx, hy, hxy, hAx, hAy⟩ := exists_skew_rotation_plane A hA hinj
  let P := rotationPlane x y
  have hdim : Module.finrank ℝ P = 2 := finrank_rotationPlane hx hy hxy
  have hP : ∀ z ∈ P, A z ∈ P := maps_rotationPlane A hAx hAy
  have hPo : ∀ z ∈ Pᗮ, A z ∈ Pᗮ := real_skew_maps_orthogonal A hA P hP
  refine ⟨P, hdim, hP, hPo, real_skew_restrict A hA Pᗮ hPo,
    injective_restrict A hinj Pᗮ hPo, ?_⟩
  have hsum := P.finrank_add_finrank_orthogonal
  omega

end VacuumBellSeparation.Gaussian
