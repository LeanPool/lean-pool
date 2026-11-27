/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.TypeStar

/-!
# An actual invariant rotation plane for an injective real skew operator

The spectral theorem is applied to the positive Gram operator `A†A`.
An eigenvector `x` and the normalized vector `Ax` give an orthonormal
rotation plane. The orthogonal complement of any invariant subspace is
invariant as well. These are induction foundations for the finite-mode
real skew normal form required by Williamson's theorem.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem real_skew_inner_self (A : E →ₗ[ℝ] E) (hA : A.adjoint = -A) (x : E) :
    inner ℝ x (A x) = 0 := by
  have h := A.adjoint_inner_right x x
  rw [hA, LinearMap.neg_apply, inner_neg_right] at h
  linarith [real_inner_comm x (A x)]

/-- Every injective skew-adjoint real operator on a nonzero finite-dimensional
Hilbert space has a genuine orthonormal invariant rotation pair. -/
theorem exists_skew_rotation_plane [Nontrivial E]
    (A : E →ₗ[ℝ] E) (hA : A.adjoint = -A) (hinj : Function.Injective A) :
    ∃ (ν : ℝ) (x y : E), 0 < ν ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      inner ℝ x y = 0 ∧ A x = ν • y ∧ A y = (-ν) • x := by
  let hP := A.isSymmetric_adjoint_comp_self
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := hP.eigenvectorBasis rfl
  let x := b i
  let μ := hP.eigenvalues rfl i
  have hx : ‖x‖ = 1 := b.orthonormal.norm_eq_one i
  have hx₀ : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    norm_num at hx
  have hAx₀ : A x ≠ 0 := by
    intro h
    exact hx₀ (hinj (h.trans A.map_zero.symm))
  have heig : A.adjoint (A x) = μ • x := hP.apply_eigenvectorBasis rfl i
  have hnorm : ‖A x‖ ^ 2 = μ := by
    calc
      ‖A x‖ ^ 2 = inner ℝ (A x) (A x) := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ x (A.adjoint (A x)) := (A.adjoint_inner_right x (A x)).symm
      _ = μ := by rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq, hx]; ring
  have hμ : 0 < μ := by
    rw [← hnorm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hAx₀)
  let ν := Real.sqrt μ
  let y := ν⁻¹ • A x
  have hν : 0 < ν := Real.sqrt_pos.mpr hμ
  have hνsq : ν * ν = μ := Real.mul_self_sqrt hμ.le
  have hνnorm : ν = ‖A x‖ := by
    dsimp [ν]
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hy : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hν),
      ← hνnorm, inv_mul_cancel₀ hν.ne']
  have hxy : inner ℝ x y = 0 := by
    dsimp [y]
    rw [real_inner_smul_right, real_skew_inner_self A hA, mul_zero]
  have hrot₁ : A x = ν • y := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hν.ne', one_smul]
  have hAA : A (A x) = (-μ) • x := by
    have h := congrArg Neg.neg heig
    simpa only [hA, LinearMap.neg_apply, neg_neg, neg_smul] using h
  have hrot₂ : A y = (-ν) • x := by
    dsimp [y]
    rw [map_smul, hAA, smul_smul]
    congr 1
    rw [← hνsq]
    field_simp [hν.ne']
  exact ⟨ν, x, y, hν, hx, hy, hxy, hrot₁, hrot₂⟩

/-- The orthogonal complement of an invariant subspace remains invariant
under a real skew-adjoint operator. -/
theorem real_skew_maps_orthogonal (A : E →ₗ[ℝ] E) (hA : A.adjoint = -A)
    (P : Submodule ℝ E) (hP : ∀ x ∈ P, A x ∈ P) :
    ∀ x ∈ Pᗮ, A x ∈ Pᗮ := by
  intro x hx
  apply (P.mem_orthogonal _).mpr
  intro y hy
  calc
    inner ℝ y (A x) = inner ℝ (A.adjoint y) x := (A.adjoint_inner_left x y).symm
    _ = -inner ℝ (A y) x := by rw [hA, LinearMap.neg_apply, inner_neg_left]
    _ = 0 := by rw [P.inner_right_of_mem_orthogonal (hP y hy) hx, neg_zero]

end VacuumBellSeparation.Gaussian
