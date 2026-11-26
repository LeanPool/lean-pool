/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Linear coordinates for two crossing directions

The small crossing discs in XII (4.5), page 253, use coordinates
where the two edge directions are the real and imaginary axes.
For two directions with nonzero real determinant, the map whose
columns are these directions is invertible. The explicit inverse
also proves continuity of both coordinate changes.
-/

public section

namespace GraphMinor.GM12

/-- Two directions with nonzero real determinant are the images
of the two coordinate axes under a continuous real-linear
equivalence. This supplies the local crossing coordinates in
XII (4.5), page 253. -/
theorem exists_linear_cross_coordinates {u v : ℂ}
    (hdet : u.re * v.im - u.im * v.re ≠ 0) :
    ∃ A : ℂ ≃L[ℝ] ℂ, A 1 = u ∧ A Complex.I = v := by
  let D := u.re * v.im - u.im * v.re
  have hD : D ≠ 0 := hdet
  let L : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight u + Complex.imCLM.smulRight v
  have hL : ∀ z, L z = z.re • u + z.im • v := fun _ => rfl
  let r₁ : ℂ → ℝ := fun z => (v.im * z.re - v.re * z.im) / D
  let r₂ : ℂ → ℝ := fun z => (u.re * z.im - u.im * z.re) / D
  let R : ℂ → ℂ := fun z => ⟨r₁ z, r₂ z⟩
  have hleft : Function.LeftInverse R L := by
    intro z
    apply Complex.ext <;>
      simp only [R, r₁, r₂, hL, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul] <;>
      field_simp [hD] <;> dsimp [D] <;> ring
  have hright : Function.RightInverse R L := by
    intro z
    apply Complex.ext <;>
      simp only [R, r₁, r₂, hL, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul] <;>
      field_simp [hD] <;> dsimp [D] <;> ring
  let e : ℂ ≃ₗ[ℝ] ℂ := {
    toLinearMap := L.toLinearMap
    invFun := R
    left_inv := hleft
    right_inv := hright }
  let A : ℂ ≃L[ℝ] ℂ := {
    toLinearEquiv := e
    continuous_toFun := L.continuous
    continuous_invFun := by
      change Continuous R
      have hrepr : R = fun z => (r₁ z : ℂ) + (r₂ z : ℂ) * Complex.I :=
        funext fun z => Complex.mk_eq_add_mul_I _ _
      rw [hrepr]
      dsimp [r₁, r₂]
      fun_prop }
  refine ⟨A, ?_, ?_⟩
  · change L 1 = u
    rw [hL]
    simp
  · change L Complex.I = v
    rw [hL]
    simp

end GraphMinor.GM12
