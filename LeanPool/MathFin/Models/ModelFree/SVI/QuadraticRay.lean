/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real

/-! # Nonnegativity of a quadratic on a ray

Part of the SVI polynomial-sign certificate (#174).

A real quadratic is nonnegative on a closed ray exactly when a finite list of polynomial sign
conditions on its coefficients holds (`quadratic_nonneg_ray_iff`).

## Main results

* `quadratic_nonneg_ray_zero_iff`: `u x² + v x + z ≥ 0` for all `x ≥ 0` iff `u ≥ 0`, `z ≥ 0` and
  either `u = 0 ∧ v ≥ 0` or `u > 0` with `v ≥ 0` or `4uz - v² ≥ 0`.
* `quadratic_nonneg_ray_iff`: `u w² + v w + z ≥ 0` for all `w ≥ a` iff `u ≥ 0`,
  `u a² + v a + z ≥ 0` and either `u = 0 ∧ v ≥ 0` or `u > 0` with `v + 2ua ≥ 0` or
  `4uz - v² ≥ 0`.

## Tags

quadratic nonnegativity, closed ray, sign conditions, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- A quadratic nonnegative on `[0, ∞)` has nonnegative leading coefficient. -/
theorem quadratic_leading_nonneg (u v z : ℝ)
    (h : ∀ x : ℝ, 0 ≤ x → 0 ≤ u*x^2+v*x+z) : 0 ≤ u := by
  by_contra hu
  have hu : u < 0 := lt_of_not_ge hu
  let x : ℝ := (|v|+|z|+1)/(-u)+1
  have hx : 1 ≤ x := by
    have hp : 0 ≤ (|v|+|z|+1)/(-u) := div_nonneg (by positivity) (by linarith)
    dsimp [x]; linarith
  have he : (-u)*(x-1) = |v|+|z|+1 := by
    dsimp [x]
    field_simp [ne_of_lt hu]
    ring
  have hh := h x (by linarith)
  have hv := le_abs_self v
  have hz := le_abs_self z
  have hvx : v*x ≤ |v| * x := mul_le_mul_of_nonneg_right hv (by linarith)
  have hzx : |z| ≤ |z| * x := by nlinarith [abs_nonneg z]
  have hux : 0 ≤ (-u)*x := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- An affine function nonnegative on `[0, ∞)` has nonnegative slope. -/
theorem affine_nonneg_slope (v z : ℝ)
    (h : ∀ x : ℝ, 0 ≤ x → 0 ≤ v*x+z) : 0 ≤ v := by
  by_contra hv
  have hv : v < 0 := lt_of_not_ge hv
  have hx : 0 ≤ (|z|+1)/(-v) := div_nonneg (by positivity) (by linarith)
  have hh := h _ hx
  have he : v*((|z|+1)/(-v)) = -(|z|+1) := by field_simp [ne_of_lt hv]
  rw [he] at hh
  have := le_abs_self z
  linarith

/-- Exact nonnegativity certificate for a real quadratic on the nonnegative ray. -/
theorem quadratic_nonneg_ray_zero_iff (u v z : ℝ) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ u*x^2+v*x+z) ↔
      0 ≤ u ∧ 0 ≤ z ∧
        ((u=0 ∧ 0≤v) ∨ (0<u ∧ (0≤v ∨ 0≤4*u*z-v^2))) := by
  constructor
  · intro h
    have hu := quadratic_leading_nonneg u v z h
    have hz : 0 ≤ z := by simpa using h 0 le_rfl
    refine ⟨hu,hz,?_⟩
    by_cases he : u=0
    · left
      refine ⟨he,affine_nonneg_slope v z ?_⟩
      simpa [he] using h
    · right
      refine ⟨lt_of_le_of_ne hu (Ne.symm he),?_⟩
      by_cases hv : 0≤v
      · exact Or.inl hv
      · right
        have hup : 0<u := lt_of_le_of_ne hu (Ne.symm he)
        have hx : 0 ≤ -v/(2*u) := div_nonneg (by linarith) (by positivity)
        have hh := h _ hx
        have hid : 4*u*(u*(-v/(2*u))^2+v*(-v/(2*u))+z) = 4*u*z-v^2 := by
          field_simp
          ring
        rw [← hid]
        positivity
  · rintro ⟨hu,hz,(⟨he,hv⟩ | ⟨hup,hv | hd⟩)⟩ x hx
    · subst u; positivity
    · positivity
    · have hsq := sq_nonneg (2*u*x+v)
      nlinarith

/-- A finite polynomial-sign certificate for nonnegativity on any closed real ray. -/
theorem quadratic_nonneg_ray_iff (a u v z : ℝ) :
    (∀ w : ℝ, a ≤ w → 0 ≤ u*w^2+v*w+z) ↔
      0 ≤ u ∧ 0 ≤ u*a^2+v*a+z ∧
        ((u=0 ∧ 0≤v) ∨ (0<u ∧ (0≤v+2*u*a ∨ 0≤4*u*z-v^2))) := by
  have he : (∀ w : ℝ, a ≤ w → 0 ≤ u*w^2+v*w+z) ↔
      (∀ x : ℝ, 0 ≤ x → 0 ≤ u*x^2+(v+2*u*a)*x+(u*a^2+v*a+z)) := by
    constructor
    · intro h x hx
      have hh := h (x+a) (by linarith)
      nlinarith
    · intro h w hw
      have hh := h (w-a) (by linarith)
      nlinarith
  rw [he,quadratic_nonneg_ray_zero_iff]
  have hd : 4*u*(u*a^2+v*a+z)-(v+2*u*a)^2 = 4*u*z-v^2 := by ring
  rw [hd]
  constructor <;> rintro ⟨hu,hz,h⟩ <;> refine ⟨hu,hz,?_⟩
  · rcases h with ⟨he,hv⟩ | h
    · exact Or.inl ⟨he,by simpa [he] using hv⟩
    · exact Or.inr h
  · rcases h with ⟨he,hv⟩ | h
    · exact Or.inl ⟨he,by simpa [he] using hv⟩
    · exact Or.inr h

end SVI
end MathFin
