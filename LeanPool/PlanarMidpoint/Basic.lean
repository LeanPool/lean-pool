/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Planar symmetric cubic tensors

The four entries are the coefficients `C₁₁₁, C₁₁₂, C₁₂₂, C₂₂₂` of a totally
symmetric cubic tensor. The Euclidean pairing identifies it with the bilinear
Christoffel tensor `K`. The derivative index in `obstruction` is unrestricted.
-/

@[expose] public section

namespace PlanarMidpoint

/-- The Euclidean plane with its standard inner product and norm. -/
abbrev E := EuclideanSpace ℝ (Fin 2)
/-- The four independent coefficients of a totally symmetric planar cubic tensor. -/
abbrev Coeff := Fin 4 → ℝ

/-- The affine midpoint parameter, explicitly named to keep independent statements identical. -/
noncomputable abbrev midpointTime : ℝ := 1 / 2

/-- A planar vector specified by its two standard coordinates. -/
def vec (x y : ℝ) : E := !₂[x, y]

@[simp] theorem vec_zero (x y : ℝ) : vec x y 0 = x := rfl
@[simp] theorem vec_one (x y : ℝ) : vec x y 1 = y := rfl

theorem vec_ext {u v : E} (h₀ : u 0 = v 0) (h₁ : u 1 = v 1) : u = v := by
  ext i
  fin_cases i <;> assumption

/-- The symmetric bilinear Christoffel tensor obtained by raising a cubic index. -/
def K (c : Coeff) (u v : E) : E :=
  vec (c 0 * u 0 * v 0 + c 1 * (u 0 * v 1 + u 1 * v 0) + c 2 * u 1 * v 1)
      (c 1 * u 0 * v 0 + c 2 * (u 0 * v 1 + u 1 * v 0) + c 3 * u 1 * v 1)

/-- The symmetric trilinear form represented by the four cubic coefficients. -/
def cubic (c : Coeff) (u v w : E) : ℝ :=
  c 0 * u 0 * v 0 * w 0 + c 1 * (u 0 * v 0 * w 1 + u 0 * v 1 * w 0 + u 1 * v 0 * w 0) + c 2 * (u 0
      * v 1 * w 1 + u 1 * v 0 * w 1 + u 1 * v 1 * w 0) + c 3 * u 1 * v 1 * w 1

/-- The contraction of a planar cubic tensor against the Euclidean metric. -/
def trace (c : Coeff) : E := vec (c 0 + c 2) (c 1 + c 3)

/-- The quartic midpoint obstruction with an unrestricted derivative slot. -/
def obstruction (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) : E :=
  2 • K c h (K (J h) h h) + 5 • K (J (K c h h)) h h - 4 • K (J h) h (K c h h)

theorem K_symm (c : Coeff) (u v : E) : K c u v = K c v u := by
  apply vec_ext <;> simp [K] <;> ring

theorem cubic_swap_left (c : Coeff) (u v w : E) : cubic c u v w = cubic c v u w := by
  simp only [cubic]
  ring

theorem cubic_swap_right (c : Coeff) (u v w : E) : cubic c u v w = cubic c u w v := by
  simp only [cubic]
  ring

theorem cubic_diagonal (c : Coeff) (u : E) :
    cubic c u u u = c 0 * u 0 ^ 3 + 3 * c 1 * u 0 ^ 2 * u 1 + 3 * c 2 * u 0 * u 1 ^ 2 + c 3 * u 1
        ^ 3 := by
  simp only [cubic]
  ring

theorem K_pairing (c : Coeff) (u v w : E) :
    inner ℝ (K c u v) w = cubic c u v w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, K, cubic]
  ring

end PlanarMidpoint
