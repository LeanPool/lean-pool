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

public import LeanPool.PersistentSOS.Localizers
public import LeanPool.PersistentSOS.Geometry
public import LeanPool.PersistentSOS.Derivatives
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Main

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section
namespace PersistentSOS

/-- Every ordinary polynomial SOS lower bound satisfies the displayed quantitative bound. -/
theorem quantitative_sos_gap {σ a b γ : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hsos : IsSOS (quarticPoly σ a b - MvPolynomial.C γ)) :
    γ ≤ minimumValue σ a b - b * separation * minimizingRadius σ a b ^ 3 := by
  apply moment_quantitative_transfer sphereFunctional moment_one moment_q moment_q_sq
    ?_ moment_square_nonneg hσ ha hsos
  rw [moment_cubic]
  norm_num [separation]

/-- A strict gap holds for every positive regularization parameter and every
positive fixed quadratic and cubic strength. -/
theorem quantitative_sos_strict {σ a b γ : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hb : 0 < b) (hsos : IsSOS (quarticPoly σ a b - MvPolynomial.C γ)) :
    γ < minimumValue σ a b := by
  have h := quantitative_sos_gap hσ ha hsos
  have hr := minimizingRadius_pos hσ ha hb
  have hd := separation_pos
  have hp : 0 < b * separation * minimizingRadius σ a b ^ 3 := by positivity
  linarith

/-- The exact minimum shift is not a finite sum of squares of real polynomials. -/
theorem minimum_shift_not_sos {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSOS (quarticPoly σ a b - MvPolynomial.C (minimumValue σ a b)) := by
  intro h
  exact (lt_irrefl _) (quantitative_sos_strict hσ ha hb h)

/-- The exact minimum shift is globally nonnegative. -/
theorem minimum_shift_nonnegative {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hb : 0 < b) (z : Fin 14 → ℝ) :
    0 ≤ MvPolynomial.eval z
      (quarticPoly σ a b - MvPolynomial.C (minimumValue σ a b)) := by
  simpa only [map_sub, MvPolynomial.eval_C, sub_nonneg, objective]
    using objective_global_lower_bound hσ ha hb z

/-- Explicit persistent failure, including actual global optimality and attainment. -/
theorem persistent_failure {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b) :
    (∀ z : Fin 14 → ℝ, minimumValue σ a b ≤ objective σ a b z) ∧
    objective σ a b (axis (minimizingRadius σ a b)) = minimumValue σ a b ∧
    ¬ IsSOS (quarticPoly σ a b - MvPolynomial.C (minimumValue σ a b)) :=
  ⟨objective_global_lower_bound hσ ha hb, objective_axis_attainment hσ ha,
    minimum_shift_not_sos hσ ha hb⟩

/-- The finite certificate is a functional on ordinary real polynomials, positive
on every quadratic square, with normalized radial moments and a strict cubic gap. -/
theorem sphere_moment_gap : ∃ L : Poly →ₗ[ℝ] ℝ,
    L 1 = 1 ∧ L qPoly = 1 ∧ L (qPoly ^ 2) = 1 ∧
    (∀ h : Poly, h.totalDegree ≤ 2 → 0 ≤ L (h ^ 2)) ∧
    (∀ h : Poly, h.totalDegree ≤ 2 → L ((qPoly - 1) * h) = 0) ∧
    L cubicPoly = 500753357629 / 500000000000 :=
  ⟨sphereFunctional, moment_one, moment_q, moment_q_sq, moment_square_nonneg,
    moment_sphere_localizer, moment_cubic⟩

end PersistentSOS
