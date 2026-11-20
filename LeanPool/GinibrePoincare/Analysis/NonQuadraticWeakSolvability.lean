/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticWeakSolvability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticDbarAdjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Weak solvability from adjoint coercivity
The duality construction does not assume an analytic solution or a closed
operator domain. It extends the bounded functional on the actual adjoint
range and applies the Hilbert space Riesz representation theorem. -/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped InnerProductSpace

/-- Hahn–Banach/Riesz weak solvability from a coercive test operator.
`V` is the embedding of tests and `A` their adjoint image; no norm on the
algebraic test space is required. -/
theorem exists_weak_solution_of_adjoint_bound
    {D H : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A V : D →ₗ[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ, ‖V φ‖ ≤ C * ‖A φ‖) (h : H) :
    ∃ u : H, ‖u‖ ≤ C * ‖h‖ ∧ ∀ φ, ⟪u, A φ⟫_ℝ = ⟪h, V φ⟫_ℝ := by
  -- The coercive estimate makes the test functional vanish on ker A.
  let F : D →ₗ[ℝ] ℝ := (innerSL ℝ h).toLinearMap.comp V
  have hfunctional_descends : A.ker ≤ F.ker := by
    intro φ hφ
    have hzero : V φ = 0 := by
      have hh := hbound φ
      have hA : A φ = 0 := hφ
      rw [hA, norm_zero, mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    change ⟪h, V φ⟫_ℝ = 0
    rw [hzero, inner_zero_right]
  -- Descend to the actual range through the quotient by ker A.
  let L : A.range →ₗ[ℝ] ℝ :=
    (A.ker.liftQ F hfunctional_descends).comp A.quotKerEquivRange.symm.toLinearMap
  have hrangeFunctional_apply (φ : D) : L ⟨A φ, ⟨φ, rfl⟩⟩ = ⟪h, V φ⟫_ℝ := by
    have he : A.quotKerEquivRange.symm ⟨A φ, ⟨φ, rfl⟩⟩ = Submodule.Quotient.mk φ := by
      apply A.quotKerEquivRange.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (LinearMap.quotKerEquivRange_apply_mk A φ).symm
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, he, Submodule.liftQ_apply]
    rfl
  have hrangeFunctional_bound (x : A.range) : ‖L x‖ ≤ (‖h‖ * C) * ‖x‖ := by
    obtain ⟨φ, hφ⟩ := x.property
    have hx : x = ⟨A φ, ⟨φ, rfl⟩⟩ := Subtype.ext hφ.symm
    rw [hx, hrangeFunctional_apply]
    calc
      ‖⟪h, V φ⟫_ℝ‖ ≤ ‖h‖ * ‖V φ‖ := norm_inner_le_norm _ _
      _ ≤ ‖h‖ * (C * ‖A φ‖) := mul_le_mul_of_nonneg_left (hbound φ) (norm_nonneg h)
      _ = (‖h‖ * C) * ‖(⟨A φ, ⟨φ, rfl⟩⟩ : A.range)‖ := by rw [mul_assoc]; rfl
  let T : A.range →L[ℝ] ℝ := L.mkContinuous (‖h‖ * C) hrangeFunctional_bound
  have hrangeFunctional_norm : ‖T‖ ≤ ‖h‖ * C :=
    T.opNorm_le_bound (mul_nonneg (norm_nonneg h) hC) hrangeFunctional_bound
  -- Extend with the same norm, then use Riesz to represent the functional.
  obtain ⟨G, hextension_agrees, hextension_norm⟩ := exists_extension_norm_eq A.range T
  let u := (InnerProductSpace.toDual ℝ H).symm G
  refine ⟨u, ?_, ?_⟩
  · calc
      ‖u‖ = ‖G‖ := (InnerProductSpace.toDual ℝ H).symm.norm_map G
      _ = ‖T‖ := hextension_norm
      _ ≤ ‖h‖ * C := hrangeFunctional_norm
      _ = C * ‖h‖ := mul_comm _ _
  · intro φ
    rw [show u = (InnerProductSpace.toDual ℝ H).symm G from rfl,
      InnerProductSpace.toDual_symm_apply]
    have hh := hextension_agrees (⟨A φ, ⟨φ, rfl⟩⟩ : A.range)
    change G (A φ) = L ⟨A φ, ⟨φ, rfl⟩⟩ at hh
    rw [hh, hrangeFunctional_apply]

/-- The same adjoint estimate gives the primal spectral gap on the closure
of the actual adjoint range, directly from the weak derivative pairing. -/
theorem norm_le_of_weak_pairing_and_range_closure
    {D H : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A V : D →ₗ[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ, ‖V φ‖ ≤ C * ‖A φ‖) (f h : H)
    (hmem : f ∈ A.range.topologicalClosure)
    (hpair : ∀ φ, ⟪f, A φ⟫_ℝ = ⟪h, V φ⟫_ℝ) :
    ‖f‖ ≤ C * ‖h‖ := by
  let S := {x : H | ‖⟪f, x⟫_ℝ‖ ≤ (C * ‖h‖) * ‖x‖}
  have hclosed : IsClosed S :=
    isClosed_le ((innerSL ℝ f).continuous.norm) (continuous_const.mul continuous_norm)
  have hrange : (A.range : Set H) ⊆ S := by
    rintro x ⟨φ, rfl⟩
    change ‖⟪f, A φ⟫_ℝ‖ ≤ (C * ‖h‖) * ‖A φ‖
    rw [hpair]
    calc
      ‖⟪h, V φ⟫_ℝ‖ ≤ ‖h‖ * ‖V φ‖ := norm_inner_le_norm _ _
      _ ≤ ‖h‖ * (C * ‖A φ‖) := mul_le_mul_of_nonneg_left (hbound φ) (norm_nonneg h)
      _ = (C * ‖h‖) * ‖A φ‖ := by ring
  have hs : f ∈ S := closure_minimal hrange hclosed hmem
  change ‖⟪f, f⟫_ℝ‖ ≤ (C * ‖h‖) * ‖f‖ at hs
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hs
  by_cases hfzero : f = 0
  · subst f
    simpa using mul_nonneg hC (norm_nonneg h)
  · have hp : 0 < ‖f‖ := norm_pos_iff.mpr hfzero
    nlinarith

/-- Orthogonality to the weak kernel is exactly the condition needed for
the primal spectral gap; no smooth holomorphic identification is assumed. -/
theorem norm_le_of_weak_pairing_and_kernel_orthogonal
    {D H : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A V : D →ₗ[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ, ‖V φ‖ ≤ C * ‖A φ‖) (f h : H)
    (hmem : f ∈ A.rangeᗮᗮ)
    (hpair : ∀ φ, ⟪f, A φ⟫_ℝ = ⟪h, V φ⟫_ℝ) :
    ‖f‖ ≤ C * ‖h‖ := by
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hmem
  exact norm_le_of_weak_pairing_and_range_closure A V C hC hbound f h hmem hpair

end
end GinibrePoincare
