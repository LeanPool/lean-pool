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

public import LeanPool.PersistentSOS.Definitions
public import LeanPool.PersistentSOS.SOSDegree
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic.Ring

/-!
# Polynomial

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section

namespace PersistentSOS
open MvPolynomial
open scoped BigOperators

/-- Substitution of a common real scale in every polynomial variable. -/
noncomputable def scalePoly (r : ℝ) : Poly →ₐ[ℝ] Poly :=
  MvPolynomial.aeval (fun i => MvPolynomial.C r * MvPolynomial.X i)

theorem scalePoly_C (r c : ℝ) : scalePoly r (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [scalePoly]

@[simp] theorem scalePoly_X (r : ℝ) (i : Fin 14) :
    scalePoly r (MvPolynomial.X i) = MvPolynomial.C r * MvPolynomial.X i := by
  simp [scalePoly]

/-- Common scaling cannot increase total degree. -/
theorem totalDegree_scalePoly_le (r : ℝ) (p : Poly) :
    (scalePoly r p).totalDegree ≤ p.totalDegree := by
  classical
  nth_rw 1 [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  apply le_trans ?_ (le_totalDegree hd)
  rw [scalePoly, aeval_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [algebraMap_eq, totalDegree_C, zero_add, Finsupp.prod, Finsupp.sum]
  apply (totalDegree_finsetProd _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (totalDegree_pow _ _).trans
  have h := totalDegree_mul (MvPolynomial.C r : Poly) (MvPolynomial.X i)
  simp only [totalDegree_C, totalDegree_X, zero_add] at h
  simpa using Nat.mul_le_mul_left (d i) h

@[simp] theorem scalePoly_qPoly (r : ℝ) :
    scalePoly r qPoly = MvPolynomial.C (r ^ 2) * qPoly := by
  simp [qPoly, map_sum, mul_pow, Finset.mul_sum]

@[simp] theorem scalePoly_cubicPoly (r : ℝ) :
    scalePoly r cubicPoly = MvPolynomial.C (r ^ 3) * cubicPoly := by
  simp only [cubicPoly, map_add, map_sub, map_mul, map_pow, map_ofNat, scalePoly_X,
    scalePoly_C]
  ring

/-- The quartic, quadratic, and cubic terms scale with their literal degrees. -/
theorem scalePoly_quarticPoly (r σ a b : ℝ) :
    scalePoly r (quarticPoly σ a b) =
      MvPolynomial.C (σ / 4 * r ^ 4) * qPoly ^ 2 -
      MvPolynomial.C (a / 2 * r ^ 2) * qPoly -
      MvPolynomial.C (b * r ^ 3) * cubicPoly := by
  simp only [quarticPoly, map_sub, map_mul, map_pow, scalePoly_C,
    scalePoly_qPoly, scalePoly_cubicPoly]
  ring

/-- Degree of the squared Euclidean norm polynomial. -/
theorem totalDegree_qPoly_le : qPoly.totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i hi
  simp

/-- The displayed 25 - term cubic has total degree at most three. -/
private theorem degree_add_le_three {p q : Poly} (hp : p.totalDegree ≤ 3)
    (hq : q.totalDegree ≤ 3) : (p + q).totalDegree ≤ 3 :=
  (totalDegree_add p q).trans (max_le hp hq)

private theorem degree_sub_le_three {p q : Poly} (hp : p.totalDegree ≤ 3)
    (hq : q.totalDegree ≤ 3) : (p - q).totalDegree ≤ 3 :=
  (totalDegree_sub p q).trans (max_le hp hq)

private theorem degree_mul_le {p q : Poly} {m n : ℕ} (hp : p.totalDegree ≤ m)
    (hq : q.totalDegree ≤ n) : (p * q).totalDegree ≤ m + n :=
  (totalDegree_mul p q).trans (Nat.add_le_add hp hq)

private theorem degree_three_square (i j : Fin 14) :
    (3 * MvPolynomial.X i * MvPolynomial.X j ^ 2 : Poly).totalDegree ≤ 3 := by
  have hnum : (3 : Poly).totalDegree ≤ 0 := by
    rw [← map_ofNat MvPolynomial.C 3, totalDegree_C]
  exact degree_mul_le (degree_mul_le hnum (totalDegree_X i).le)
    (totalDegree_X_pow j 2).le

private theorem degree_coefficient_square (c : ℝ) (i j : Fin 14) :
    (MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.X j ^ 2).totalDegree ≤ 3 :=
  degree_mul_le (degree_mul_le (totalDegree_C c).le (totalDegree_X i).le)
    (totalDegree_X_pow j 2).le

private theorem degree_coefficient_product (c : ℝ) (i j k : Fin 14) :
    (MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.X j *
      MvPolynomial.X k).totalDegree ≤ 3 :=
  degree_mul_le (degree_mul_le (degree_mul_le (totalDegree_C c).le
    (totalDegree_X i).le) (totalDegree_X j).le) (totalDegree_X k).le

private noncomputable def cubicPart0 : Poly :=
  MvPolynomial.X 0 ^ 3
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 5 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 6 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 7 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 8 ^ 2

private theorem cubicPart0_degree : cubicPart0.totalDegree ≤ 3 := by
  unfold cubicPart0
  exact degree_sub_le_three (degree_sub_le_three (degree_sub_le_three (degree_sub_le_three
    ((totalDegree_X_pow (0 : Fin 14) 3).le) (degree_three_square 0 5)) (degree_three_square 0 6))
    (degree_three_square 0 7)) (degree_three_square 0 8)

private noncomputable def cubicPart1 : Poly :=
  -(3 * MvPolynomial.X 0 * MvPolynomial.X 9 ^ 2)
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 10 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 11 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 12 ^ 2
  - 3 * MvPolynomial.X 0 * MvPolynomial.X 13 ^ 2

private theorem cubicPart1_degree : cubicPart1.totalDegree ≤ 3 := by
  unfold cubicPart1
  exact degree_sub_le_three (degree_sub_le_three (degree_sub_le_three (degree_sub_le_three ((by
    simpa only [totalDegree_neg] using degree_three_square 0 9)) (degree_three_square 0 10))
    (degree_three_square 0 11)) (degree_three_square 0 12)) (degree_three_square 0 13)

private noncomputable def cubicPart2 : Poly :=
  MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
  + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2
  + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 3 ^ 2
  + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 * MvPolynomial.X 4 ^ 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 5 * MvPolynomial.X 1 ^ 2

private theorem cubicPart2_degree : cubicPart2.totalDegree ≤ 3 := by
  unfold cubicPart2
  exact degree_add_le_three (degree_add_le_three (degree_add_le_three (degree_add_le_three
    (degree_coefficient_square (3 / 2) 0 1) (degree_coefficient_square (3 / 2) 0 2))
    (degree_coefficient_square (3 / 2) 0 3)) (degree_coefficient_square (3 / 2) 0 4))
    (degree_coefficient_square (259 / 100) 5 1)

private noncomputable def cubicPart3 : Poly :=
  MvPolynomial.C (259 / 100) * MvPolynomial.X 6 * MvPolynomial.X 2 ^ 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 7 * MvPolynomial.X 3 ^ 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 8 * MvPolynomial.X 1 * MvPolynomial.X 2
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 8 * MvPolynomial.X 3 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 9 * MvPolynomial.X 1 * MvPolynomial.X 3

private theorem cubicPart3_degree : cubicPart3.totalDegree ≤ 3 := by
  unfold cubicPart3
  exact degree_add_le_three (degree_add_le_three (degree_add_le_three (degree_add_le_three
    (degree_coefficient_square (259 / 100) 6 2) (degree_coefficient_square (259 / 100) 7 3))
    (degree_coefficient_product (259 / 100) 8 1 2)) (degree_coefficient_product (259 / 100) 8 3
    4)) (degree_coefficient_product (259 / 100) 9 1 3)

private noncomputable def cubicPart4 : Poly :=
  MvPolynomial.C (259 / 100) * MvPolynomial.X 9 * MvPolynomial.X 2 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 10 * MvPolynomial.X 2 * MvPolynomial.X 3
  + MvPolynomial.C (1813 / 500) * MvPolynomial.X 11 * MvPolynomial.X 1 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 12 * MvPolynomial.X 2 * MvPolynomial.X 4
  + MvPolynomial.C (259 / 100) * MvPolynomial.X 13 * MvPolynomial.X 3 * MvPolynomial.X 4

private theorem cubicPart4_degree : cubicPart4.totalDegree ≤ 3 := by
  unfold cubicPart4
  exact degree_add_le_three (degree_add_le_three (degree_add_le_three (degree_add_le_three
    (degree_coefficient_product (259 / 100) 9 2 4) (degree_coefficient_product (259 / 100) 10 2
    3)) (degree_coefficient_product (1813 / 500) 11 1 4)) (degree_coefficient_product (259 / 100)
    12 2 4)) (degree_coefficient_product (259 / 100) 13 3 4)

private theorem cubicPoly_parts :
    cubicPoly = cubicPart0 + cubicPart1 + cubicPart2 + cubicPart3 + cubicPart4 := by
  unfold cubicPoly cubicPart0 cubicPart1 cubicPart2 cubicPart3 cubicPart4
  ring

/-- The cubic has degree at most three, using separately checked sparse components. -/
theorem totalDegree_cubicPoly_le : cubicPoly.totalDegree ≤ 3 := by
  rw [cubicPoly_parts]
  exact degree_add_le_three
    (degree_add_le_three
      (degree_add_le_three (degree_add_le_three cubicPart0_degree cubicPart1_degree)
        cubicPart2_degree) cubicPart3_degree) cubicPart4_degree

/-- The objective is a quartic polynomial for all parameter values. -/
theorem totalDegree_quarticPoly_le (σ a b : ℝ) : (quarticPoly σ a b).totalDegree ≤ 4 := by
  unfold quarticPoly
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
    exact totalDegree_cubicPoly_le.trans (by decide)


/-- Subtracting a real lower bound preserves the quartic degree bound. -/
theorem totalDegree_shiftedQuartic_le (σ a b γ : ℝ) :
    (quarticPoly σ a b - MvPolynomial.C γ).totalDegree ≤ 4 := by
  exact (totalDegree_sub _ _).trans (max_le (totalDegree_quarticPoly_le σ a b) (by simp))

end PersistentSOS
