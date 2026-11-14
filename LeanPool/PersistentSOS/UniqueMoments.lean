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
public import LeanPool.PersistentSOS.Transfer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # The same moment certificate separates a cubic with a unique maximizer

No new moment data are required. The existing sphere localizer identifies
`L(tQ)` with `L(t)`, giving a positive exact gap for the selected cubic.
The ordinary SOS degree bridge then transfers that gap at every positive
regularization parameter.
-/


@[expose] public section

namespace PersistentSOS
open MvPolynomial

/-- The exact first - coordinate moment from the retained rational certificate. -/
theorem moment_first_coordinate : sphereFunctional (X 0) = 423308963 / 1000000000 := by
  simp only [X, sphereFunctional_monomial, exponentKey_single]
  norm_num [momentNumerator]

/-- Multiplication by the sphere equation preserves the first - coordinate moment. -/
theorem moment_first_coordinate_q :
    sphereFunctional (X 0 * qPoly) = 423308963 / 1000000000 := by
  have h := moment_sphere_localizer (X 0) (by simp)
  rw [sub_mul, one_mul, map_sub] at h
  rw [mul_comm, ← moment_first_coordinate]
  exact sub_eq_zero.mp h

/-- Constants act by ordinary scalar multiplication under the moment functional. -/
lemma unique_moment_C_mul (c : ℝ) (p : Poly) :
    sphereFunctional (MvPolynomial.C c * p) = c * sphereFunctional p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-- The separation for the selected cubic is strictly positive. -/
theorem uniqueSeparation_pos : 0 < uniqueSeparation := by
  norm_num [uniqueSeparation]

/-- The exact gap for the selected cubic, using the unchanged functional. -/
theorem moment_unique_cubic : sphereFunctional uniqueCubicPoly = 1 + uniqueSeparation := by
  have h1000 : (1000 : Poly) = MvPolynomial.C (1000 : ℝ) :=
    (map_natCast MvPolynomial.C 1000).symm
  unfold uniqueCubicPoly
  rw [unique_moment_C_mul, map_add, h1000, unique_moment_C_mul,
    moment_cubic, moment_first_coordinate_q]
  norm_num [uniqueSeparation]

/-- The selected cubic's exact rational moment value. -/
theorem moment_unique_cubic_exact :
    sphereFunctional uniqueCubicPoly = 143132860603 / 143000000000 := by
  rw [moment_unique_cubic]
  norm_num [uniqueSeparation]

/-- The selected cubic still exceeds its unit - sphere bound under the functional. -/
theorem moment_unique_cubic_gt_one : 1 < sphereFunctional uniqueCubicPoly := by
  rw [moment_unique_cubic]
  linarith [uniqueSeparation_pos]

/-- Common scaling respects the degree - three homogeneity of the selected cubic. -/
@[simp] theorem scalePoly_uniqueCubicPoly (r : ℝ) :
    scalePoly r uniqueCubicPoly = MvPolynomial.C (r ^ 3) * uniqueCubicPoly := by
  simp only [uniqueCubicPoly, map_mul, map_add, map_pow, map_ofNat,
    scalePoly_C, scalePoly_X, scalePoly_qPoly, scalePoly_cubicPoly]
  ring

/-- Exact scaling identity for the selected quartic. -/
theorem scalePoly_uniqueQuarticPoly (r σ a b : ℝ) :
    scalePoly r (uniqueQuarticPoly σ a b) =
      MvPolynomial.C (σ / 4 * r ^ 4) * qPoly ^ 2 -
      MvPolynomial.C (a / 2 * r ^ 2) * qPoly -
      MvPolynomial.C (b * r ^ 3) * uniqueCubicPoly := by
  simp only [uniqueQuarticPoly, map_sub, map_mul, map_pow, scalePoly_C,
    scalePoly_qPoly, scalePoly_uniqueCubicPoly]
  ring

/-- The selected polynomial remains a cubic. -/
theorem totalDegree_uniqueCubicPoly_le : uniqueCubicPoly.totalDegree ≤ 3 := by
  have hnum : (1000 : Poly).totalDegree = 0 := by
    rw [← map_ofNat MvPolynomial.C 1000, totalDegree_C]
  unfold uniqueCubicPoly
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    simpa only [hnum, zero_add] using totalDegree_cubicPoly_le
  · have h := totalDegree_mul (X 0 : Poly) qPoly
    have hq := totalDegree_qPoly_le
    simp only [totalDegree_X] at h
    omega

/-- The selected objective has degree at most four. -/
theorem totalDegree_uniqueQuarticPoly_le (σ a b : ℝ) :
    (uniqueQuarticPoly σ a b).totalDegree ≤ 4 := by
  unfold uniqueQuarticPoly
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact (totalDegree_pow _ _).trans (by have := totalDegree_qPoly_le; omega)
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact totalDegree_qPoly_le.trans (by decide)
  · apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact totalDegree_uniqueCubicPoly_le.trans (by decide)

/-- Subtracting a real lower bound preserves the selected quartic degree bound. -/
theorem totalDegree_shiftedUniqueQuartic_le (σ a b γ : ℝ) :
    (uniqueQuarticPoly σ a b - MvPolynomial.C γ).totalDegree ≤ 4 := by
  exact (totalDegree_sub _ _).trans
    (max_le (totalDegree_uniqueQuarticPoly_le σ a b) (by simp))

/-- The scaled functional evaluates the selected quartic shift exactly. -/
theorem unique_functional_separation (σ a b r γ : ℝ) :
    sphereFunctional (MvPolynomial.C (σ / 4 * r ^ 4) * qPoly ^ 2 -
      MvPolynomial.C (a / 2 * r ^ 2) * qPoly -
      MvPolynomial.C (b * r ^ 3) * uniqueCubicPoly - MvPolynomial.C γ) =
      radialValue σ a b r - b * uniqueSeparation * r ^ 3 - γ := by
  have hconst (c : ℝ) : sphereFunctional (MvPolynomial.C c) = c := by
    simpa only [mul_one, moment_one] using unique_moment_C_mul c 1
  simp only [map_sub, unique_moment_C_mul, hconst, moment_q, moment_q_sq,
    moment_unique_cubic]
  unfold radialValue
  ring

/-- Every ordinary SOS lower bound for the selected quartic has the exact gap. -/
theorem unique_quantitative_sos_gap {σ a b γ : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hsos : IsSOS (uniqueQuarticPoly σ a b - MvPolynomial.C γ)) :
    γ ≤ minimumValue σ a b - b * uniqueSeparation * minimizingRadius σ a b ^ 3 := by
  have hn := scaled_sos_nonneg sphereFunctional moment_square_nonneg
    (totalDegree_shiftedUniqueQuartic_le σ a b γ) hsos (minimizingRadius σ a b)
  rw [map_sub, scalePoly_C, scalePoly_uniqueQuarticPoly, unique_functional_separation,
    radial_at_minimizingRadius hσ ha] at hn
  linarith

/-- The selected cubic gives a strict SOS gap for every positive parameter. -/
theorem unique_quantitative_sos_strict {σ a b γ : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hb : 0 < b) (hsos : IsSOS (uniqueQuarticPoly σ a b - MvPolynomial.C γ)) :
    γ < minimumValue σ a b := by
  have h := unique_quantitative_sos_gap hσ ha hsos
  have hr := minimizingRadius_pos hσ ha hb
  have hd := uniqueSeparation_pos
  have hp : 0 < b * uniqueSeparation * minimizingRadius σ a b ^ 3 := by positivity
  linarith

/-- The selected quartic's exact minimum shift is not an ordinary polynomial SOS. -/
theorem unique_minimum_shift_not_sos {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSOS (uniqueQuarticPoly σ a b - MvPolynomial.C (minimumValue σ a b)) := by
  intro h
  exact (lt_irrefl _) (unique_quantitative_sos_strict hσ ha hb h)

/-- A common ordinary - polynomial functional certifies both exact cubic values,
all truncated sphere relations, and positivity on every quadratic square. -/
theorem unique_sphere_moment_gap : ∃ L : Poly →ₗ[ℝ] ℝ,
    L 1 = 1 ∧ L qPoly = 1 ∧ L (qPoly ^ 2) = 1 ∧
    (∀ h : Poly, h.totalDegree ≤ 2 → 0 ≤ L (h ^ 2)) ∧
    (∀ h : Poly, h.totalDegree ≤ 2 → L ((qPoly - 1) * h) = 0) ∧
    L cubicPoly = 500753357629 / 500000000000 ∧
    L (X 0) = 423308963 / 1000000000 ∧
    L uniqueCubicPoly = 143132860603 / 143000000000 :=
  ⟨sphereFunctional, moment_one, moment_q, moment_q_sq, moment_square_nonneg,
    moment_sphere_localizer, moment_cubic, moment_first_coordinate, moment_unique_cubic_exact⟩

end PersistentSOS
