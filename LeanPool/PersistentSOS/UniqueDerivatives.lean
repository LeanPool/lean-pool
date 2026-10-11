/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

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

public import LeanPool.PersistentSOS.Derivatives
public import LeanPool.PersistentSOS.Sphere
public import LeanPool.PersistentSOS.Radial
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Derivatives of the quartic with a unique global minimizer

The Hessian is computed from the literal polynomial using `MvPolynomial.pderiv`.
At its minimizing axis point it is a strictly positive diagonal matrix.
-/


@[expose] public section
namespace PersistentSOS
open MvPolynomial


private theorem constantCoeff_two : constantCoeff (2 : Poly) = 2 := by
  rw [← map_ofNat MvPolynomial.C 2]
  simp

@[simp] private theorem pderiv_thousand (i : Fin 14) :
    pderiv i (1000 : Poly) = 0 := by
  rw [← map_ofNat MvPolynomial.C 1000]
  exact pderiv_C

@[simp] private theorem pderiv_two (i : Fin 14) :
    pderiv i (2 : Poly) = 0 := by
  rw [← map_ofNat MvPolynomial.C 2]
  exact pderiv_C

@[simp] private theorem pderiv_three (i : Fin 14) :
    pderiv i (3 : Poly) = 0 := by
  rw [← map_ofNat MvPolynomial.C 3]
  exact pderiv_C

@[simp] private theorem eval_ite_poly (z : Fin 14 → ℝ) (c : Prop) [Decidable c]
    (u v : Poly) : eval z (if c then u else v) = if c then eval z u else eval z v := by
  split_ifs <;> rfl

@[simp] private theorem pderiv_ite_poly (i : Fin 14) (c : Prop) [Decidable c]
    (u v : Poly) : pderiv i (if c then u else v) = if c then pderiv i u else pderiv i v := by
  split_ifs <;> rfl

@[simp] private theorem eval_qPoly_axis (r : ℝ) :
    eval (axis r) qPoly = r ^ 2 := Q_axis r

/-- The new cubic has no first - order contribution at the origin. -/
theorem unique_cubic_first_at_zero (i : Fin 14) :
    eval (0 : Fin 14 → ℝ) (pderiv i uniqueCubicPoly) = 0 := by
  have hc : constantCoeff (pderiv i cubicPoly) = 0 := by
    simpa using cubic_first_at_zero i
  simp [uniqueCubicPoly, qPoly, hc]

/-- The new cubic has no second - order contribution at the origin. -/
theorem unique_cubic_second_at_zero (i j : Fin 14) :
    eval (0 : Fin 14 → ℝ) (pderiv j (pderiv i uniqueCubicPoly)) = 0 := by
  have hc : constantCoeff (pderiv j (pderiv i cubicPoly)) = 0 := by
    simpa using cubic_second_at_zero i j
  simp [uniqueCubicPoly, qPoly, hc]

/-- The origin remains stationary for every choice of the parameters. -/
theorem unique_stationary_origin (σ a b : ℝ) (i : Fin 14) :
    eval (0 : Fin 14 → ℝ) (pderiv i (uniqueQuarticPoly σ a b)) = 0 := by
  have hc : constantCoeff (pderiv i uniqueCubicPoly) = 0 := by
    simpa using unique_cubic_first_at_zero i
  have hq : constantCoeff qPoly = 0 := by simp [qPoly]
  simp [uniqueQuarticPoly, q_first, hc, hq]

/-- The Hessian at the stationary origin remains the negative scalar matrix. -/
theorem unique_hessian_origin (σ a b : ℝ) (i j : Fin 14) :
    eval (0 : Fin 14 → ℝ) (pderiv j (pderiv i (uniqueQuarticPoly σ a b))) =
      if i = j then -a else 0 := by
  have hc : constantCoeff (pderiv j (pderiv i uniqueCubicPoly)) = 0 := by
    simpa using unique_cubic_second_at_zero i j
  have hq : constantCoeff qPoly = 0 := by simp [qPoly]
  simp [uniqueQuarticPoly, q_first, hc, Pi.single_apply, constantCoeff_two]
  split_ifs <;> simp_all [constantCoeff_two]

/-- The second derivatives of the original cubic at an arbitrary axis point. -/
theorem cubic_second_axis (r : ℝ) (i j : Fin 14) :
    eval (axis r) (pderiv j (pderiv i cubicPoly)) =
      if i = j then (if i = 0 then 6 * r else if i.val ≤ 4 then 3 * r else -6 * r)
      else 0 := by
  fin_cases i <;>
    norm_num [cubicPoly, axis, Pi.single_apply] <;> split_ifs <;> try simp_all
  all_goals ring

/-- The selected cubic's Hessian on the distinguished axis. -/
theorem unique_cubic_second_axis (r : ℝ) (i j : Fin 14) :
    eval (axis r) (pderiv j (pderiv i uniqueCubicPoly)) =
      if i = j then
        (if i = 0 then 6 * r else if i.val ≤ 4 then 3002 * r / 1001 else -5998 * r / 1001)
      else 0 := by
  simp [uniqueCubicPoly, q_first, cubic_second_axis, axis, Pi.single_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0
    · subst i
      norm_num
      ring
    · by_cases hix : i.val ≤ 4
      · simp [hi, Ne.symm hi, hix]
        ring
      · simp [hi, Ne.symm hi, hix]
        ring
  · by_cases hi : i = 0
    · subst i
      simp [hij, Ne.symm hij]
    · simp [hij, hi, Ne.symm hi]

/-- The actual Hessian entries at the explicit minimizing radius. -/
theorem unique_hessian_minimizer {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (i j : Fin 14) :
    eval (axis (minimizingRadius σ a b))
      (pderiv j (pderiv i (uniqueQuarticPoly σ a b))) =
      if i = j then
        (if i = 0 then 2 * a + 3 * b * minimizingRadius σ a b
         else if i.val ≤ 4 then b * minimizingRadius σ a b / 1001
         else 9001 * b * minimizingRadius σ a b / 1001)
      else 0 := by
  have he := minimizingRadius_equation (b := b) hσ ha
  simp [uniqueQuarticPoly, q_first, unique_cubic_second_axis,
    axis, Pi.single_apply]
  split_ifs <;> simp_all <;> nlinarith

/-- The Hessian at the unique global minimizer is positive definite for
all positive real regularization, quadratic, and cubic strengths. -/
theorem unique_hessian_posDef {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b) :
    Matrix.PosDef (fun i j : Fin 14 =>
      eval (axis (minimizingRadius σ a b))
        (pderiv j (pderiv i (uniqueQuarticPoly σ a b)))) := by
  have hr := minimizingRadius_pos hσ ha hb
  have hdiag :
      (fun i j : Fin 14 => eval (axis (minimizingRadius σ a b))
        (pderiv j (pderiv i (uniqueQuarticPoly σ a b)))) =
      Matrix.diagonal (fun i : Fin 14 =>
        if i = 0 then 2 * a + 3 * b * minimizingRadius σ a b
        else if i.val ≤ 4 then b * minimizingRadius σ a b / 1001
        else 9001 * b * minimizingRadius σ a b / 1001) := by
    funext i j
    rw [unique_hessian_minimizer hσ ha]
    rfl
  rw [hdiag]
  apply Matrix.PosDef.diagonal
  intro i
  split_ifs <;> positivity

/-- First derivatives of the original cubic on its distinguished axis. -/
theorem cubic_first_axis (r : ℝ) (i : Fin 14) :
    eval (axis r) (pderiv i cubicPoly) = if i = 0 then 3 * r ^ 2 else 0 := by
  fin_cases i <;> norm_num [cubicPoly, axis, Pi.single_apply]

/-- The selected cubic has the same axial gradient as the original cubic. -/
theorem unique_cubic_first_axis (r : ℝ) (i : Fin 14) :
    eval (axis r) (pderiv i uniqueCubicPoly) = if i = 0 then 3 * r ^ 2 else 0 := by
  simp [uniqueCubicPoly, q_first, cubic_first_axis, axis, Pi.single_apply]
  by_cases hi : i = 0
  · subst i
    norm_num
    ring
  · simp [hi, Ne.symm hi]

/-- The explicitly specified unique minimizer is stationary. -/
theorem unique_stationary_minimizer {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (i : Fin 14) :
    eval (axis (minimizingRadius σ a b))
      (pderiv i (uniqueQuarticPoly σ a b)) = 0 := by
  have he := minimizingRadius_equation (b := b) hσ ha
  simp [uniqueQuarticPoly, q_first, unique_cubic_first_axis, axis]
  by_cases hi : i = 0
  · simp [hi]
    linear_combination minimizingRadius σ a b * he
  · simp [hi]

end PersistentSOS
