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
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Sphere

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section

namespace PersistentSOS

theorem Q_nonneg (z : Fin 14 → ℝ) : 0 ≤ Q z := by
  rw [Q_eq_sum]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (z i)

theorem radius_nonneg (z : Fin 14 → ℝ) : 0 ≤ radius z := Real.sqrt_nonneg _

theorem radius_sq (z : Fin 14 → ℝ) : radius z ^ 2 = Q z :=
  Real.sq_sqrt (Q_nonneg z)

theorem Q_eq_norm_sq (z : Fin 14 → ℝ) :
    Q z = ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 14))‖ ^ 2 := by
  simp [Q_eq_sum, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

theorem radius_eq_norm (z : Fin 14 → ℝ) :
    radius z = ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 14))‖ := by
  rw [radius, Q_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Squared norm of the four coordinates used by the quadratic map. -/
noncomputable def xSq (z : Fin 14 → ℝ) : ℝ :=
  z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2

/-- Squared norm of the nine coordinates paired with the quadratic map. -/
noncomputable def ySq (z : Fin 14 → ℝ) : ℝ :=
  z 5 ^ 2 + z 6 ^ 2 + z 7 ^ 2 + z 8 ^ 2 + z 9 ^ 2 + z 10 ^ 2
    + z 11 ^ 2 + z 12 ^ 2 + z 13 ^ 2

/-- The nine-component rational quadratic map appearing in the cubic. -/
noncomputable def quadMap (z : Fin 14 → ℝ) : Fin 9 → ℝ :=
  ![z 1 ^ 2, z 2 ^ 2, z 3 ^ 2, z 1 * z 2 + z 3 * z 4,
    z 1 * z 3 + z 2 * z 4, z 2 * z 3, 7 / 5 * z 1 * z 4,
    z 2 * z 4, z 3 * z 4]

/-- The nine coordinates paired with the quadratic map. -/
noncomputable def yVec (z : Fin 14 → ℝ) : Fin 9 → ℝ :=
  ![z 5, z 6, z 7, z 8, z 9, z 10, z 11, z 12, z 13]

/-- Pairing of the nine-coordinate vector with the quadratic map. -/
noncomputable def dotTerm (z : Fin 14 → ℝ) : ℝ := ∑ i, yVec z i * quadMap z i

theorem xSq_nonneg (z : Fin 14 → ℝ) : 0 ≤ xSq z := by unfold xSq; positivity
theorem ySq_nonneg (z : Fin 14 → ℝ) : 0 ≤ ySq z := by unfold ySq; positivity

theorem Q_decomp (z : Fin 14 → ℝ) : Q z = z 0 ^ 2 + xSq z + ySq z := by
  simp [Q_eq_sum, Fin.sum_univ_succ, xSq, ySq]
  ring

theorem C_decomp (z : Fin 14 → ℝ) :
    C z = z 0 ^ 3 - 3 * z 0 * ySq z + 3 / 2 * z 0 * xSq z
      + 259 / 100 * dotTerm z := by
  simp [C, cubicPoly, dotTerm, quadMap, yVec, Fin.sum_univ_succ, xSq, ySq]
  ring

theorem choiLam_nonneg (a b c d : ℝ) :
    0 ≤ a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 + d ^ 4 - 4 * a * b * c * d := by
  by_cases h : 0 ≤ b * c
  · nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (b * c - d ^ 2),
      mul_nonneg h (sq_nonneg (a - d))]
  · have hn : 0 ≤ -(b * c) := le_of_lt (neg_pos.mpr (lt_of_not_ge h))
    nlinarith [sq_nonneg (a * b + a * c), sq_nonneg (b * c + d ^ 2),
      mul_nonneg hn (sq_nonneg (a + d))]

theorem quadMap_contraction (z : Fin 14 → ℝ) :
    (∑ i, quadMap z i ^ 2) ≤ xSq z ^ 2 := by
  have h := choiLam_nonneg (z 1) (z 2) (z 3) (z 4)
  simp [quadMap, xSq, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (z 1 * z 4)]

theorem dotTerm_bound (z : Fin 14 → ℝ) : dotTerm z ≤ Real.sqrt (ySq z) * xSq z := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (yVec z) (quadMap z)
  have hy : (∑ i, yVec z i ^ 2) = ySq z := by
    simp [yVec, ySq, Fin.sum_univ_succ]; ring
  have hm := mul_le_mul_of_nonneg_left (quadMap_contraction z) (ySq_nonneg z)
  rw [hy] at hcs
  have hs := Real.sq_sqrt (ySq_nonneg z)
  have hx := xSq_nonneg z
  have hy' := Real.sqrt_nonneg (ySq z)
  change dotTerm z ^ 2 ≤ _ at hcs
  have hprod : 0 ≤ Real.sqrt (ySq z) * xSq z := mul_nonneg hy' hx
  nlinarith [sq_nonneg (dotTerm z - Real.sqrt (ySq z) * xSq z)]

theorem cubic_unit_refined_upper (z : Fin 14 → ℝ) (hQ : Q z = 1) :
    C z + (3 / 2 * Real.sqrt 3 - 259 / 100) * (Real.sqrt (ySq z) * xSq z) ≤ 1 := by
  let Y := Real.sqrt (ySq z)
  let s := Real.sqrt 3
  let t := z 0
  let v := (t + s * Y) / 2
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y ^ 2 = ySq z := Real.sq_sqrt (ySq_nonneg z)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : s ^ 3 = 3 * s := by calc
    s ^ 3 = s ^ 2 * s := by ring
    _ = 3 * s := by rw [hs2]
  have hx := xSq_nonneg z
  have hsplit : t ^ 2 + xSq z + Y ^ 2 = 1 := by
    simpa only [t, hY2, ← Q_decomp] using hQ
  have hk : (259 / 100 : ℝ) ≤ 3 / 2 * s := by nlinarith
  have hupper : C z + (3 / 2 * s - 259 / 100) * (Y * xSq z) ≤
      t ^ 3 - 3 * t * Y ^ 2 + 3 / 2 * (t + s * Y) * xSq z := by
    have hd := dotTerm_bound z
    have hm := mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg hY hx)
    rw [C_decomp, ← hY2]
    change dotTerm z ≤ Y * xSq z at hd
    dsimp [t]
    nlinarith [hd]
  have hcs : (t + s * Y) ^ 2 + (s * t - Y) ^ 2 = 4 * (t ^ 2 + Y ^ 2) := by
    calc
      _ = (1 + s ^ 2) * (t ^ 2 + Y ^ 2) := by ring
      _ = _ := by rw [hs2]; ring
  have hv : -1 ≤ v := by
    dsimp [v]
    nlinarith [sq_nonneg (s * t - Y)]
  have hid : t ^ 3 - 3 * t * Y ^ 2 + 3 / 2 * (t + s * Y) * xSq z
      = 3 * v - 4 * v ^ 3 := by
    have heq : xSq z = 1 - t ^ 2 - Y ^ 2 := by linarith
    rw [heq]
    dsimp [v]
    ring_nf
    rw [hs2, hs3]
    ring
  have hf : 0 ≤ (v + 1) * (2 * v - 1) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  rw [hid] at hupper
  change C z + (3 / 2 * s - 259 / 100) * (Y * xSq z) ≤ 1
  nlinarith

theorem coefficient_strict : (259 / 100 : ℝ) < 3 / 2 * Real.sqrt 3 := by
  have hs := Real.sqrt_nonneg (3 : ℝ)
  have hs2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem cubic_unit_upper (z : Fin 14 → ℝ) (hQ : Q z = 1) : C z ≤ 1 := by
  have h := cubic_unit_refined_upper z hQ
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_lt coefficient_strict))
    (mul_nonneg (Real.sqrt_nonneg (ySq z)) (xSq_nonneg z))
  linarith

theorem C_scale (z : Fin 14 → ℝ) (r : ℝ) :
    C (fun i => r * z i) = r ^ 3 * C z := by
  simp [C, cubicPoly]
  ring

theorem Q_scale (z : Fin 14 → ℝ) (r : ℝ) :
    Q (fun i => r * z i) = r ^ 2 * Q z := by
  simp only [Q_eq_sum, mul_pow, ← Finset.mul_sum]

theorem C_neg (z : Fin 14 → ℝ) : C (fun i => -z i) = -C z := by
  convert C_scale z (-1) using 1 <;> norm_num

theorem cubic_unit_abs (z : Fin 14 → ℝ) (hQ : Q z = 1) : |C z| ≤ 1 := by
  have hu := cubic_unit_upper z hQ
  have hQn : Q (fun i => -z i) = 1 := by
    simpa using (Q_scale z (-1)).trans (by simpa using hQ)
  have hl := cubic_unit_upper (fun i => -z i) hQn
  rw [C_neg] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem Q_eq_zero_iff (z : Fin 14 → ℝ) : Q z = 0 ↔ z = 0 := by
  rw [Q_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]
  exact WithLp.toLp_eq_zero 2

theorem cubic_abs_le (z : Fin 14 → ℝ) : |C z| ≤ radius z ^ 3 := by
  by_cases hz : Q z = 0
  · have heq := (Q_eq_zero_iff z).mp hz
    subst z
    simp [C, cubicPoly, radius, Q_eq_sum]
  · have hr : 0 < radius z := Real.sqrt_pos.mpr (lt_of_le_of_ne (Q_nonneg z) (Ne.symm hz))
    have hr0 : radius z ≠ 0 := ne_of_gt hr
    have hn : Q (fun i => (radius z)⁻¹ * z i) = 1 := by
      rw [Q_scale, ← radius_sq]
      field_simp
    have hu := cubic_unit_abs (fun i => (radius z)⁻¹ * z i) hn
    rw [C_scale, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((radius z)⁻¹) ^ 3)] at hu
    have hh := mul_le_mul_of_nonneg_left hu (le_of_lt (pow_pos hr 3))
    have hi : radius z ^ 3 * ((radius z)⁻¹ ^ 3 * |C z|) = |C z| := by
      field_simp
    rw [hi] at hh
    simpa using hh

theorem Q_axis (r : ℝ) : Q (axis r) = r ^ 2 := by
  simp [Q_eq_sum, axis]

@[simp] theorem C_axis (r : ℝ) : C (axis r) = r ^ 3 := by
  norm_num [C, cubicPoly, axis]

theorem unit_sphere_attainment : Q (axis 1) = 1 ∧ C (axis 1) = 1 := by
  rw [Q_axis, C_axis]
  norm_num

theorem dotTerm_sq_le (z : Fin 14 → ℝ) : dotTerm z ^ 2 ≤ ySq z * xSq z ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (yVec z) (quadMap z)
  have hy : (∑ i, yVec z i ^ 2) = ySq z := by
    simp [yVec, ySq, Fin.sum_univ_succ]; ring
  rw [hy] at hcs
  exact le_trans hcs (mul_le_mul_of_nonneg_left (quadMap_contraction z) (ySq_nonneg z))

theorem dotTerm_zero_of_xSq_zero (z : Fin 14 → ℝ) (h : xSq z = 0) : dotTerm z = 0 := by
  have hd := dotTerm_sq_le z
  rw [h] at hd
  nlinarith [sq_nonneg (dotTerm z)]

theorem dotTerm_zero_of_ySq_zero (z : Fin 14 → ℝ) (h : ySq z = 0) : dotTerm z = 0 := by
  have hd := dotTerm_sq_le z
  rw [h] at hd
  nlinarith [sq_nonneg (dotTerm z)]

/-- Exact equality classification on the unit sphere. The four `x` coordinates vanish;
    the first coordinate is either `1` or `-1 / 2`. The sphere equation then determines
    the squared length of the nine `y` coordinates as `0` or `3 / 4`, respectively. -/
theorem cubic_unit_maximizers (z : Fin 14 → ℝ) (hQ : Q z = 1) :
    C z = 1 ↔ xSq z = 0 ∧ (z 0 = 1 ∨ z 0 = -1 / 2) := by
  constructor
  · intro hC
    have hu := cubic_unit_refined_upper z hQ
    have hd : 0 < 3 / 2 * Real.sqrt 3 - 259 / 100 := sub_pos.mpr coefficient_strict
    have hprod : Real.sqrt (ySq z) * xSq z = 0 := by
      have hn := mul_nonneg (Real.sqrt_nonneg (ySq z)) (xSq_nonneg z)
      rw [hC] at hu
      nlinarith
    rcases mul_eq_zero.mp hprod with hy | hx
    · have hy0 : ySq z = 0 := by
        have hs := Real.sq_sqrt (ySq_nonneg z)
        rw [hy] at hs
        simpa using hs.symm
      have hdot := dotTerm_zero_of_ySq_zero z hy0
      have hsplit := Q_decomp z
      rw [hQ, hy0] at hsplit
      have hxs : xSq z = 1 - z 0 ^ 2 := by linarith
      have hc := C_decomp z
      rw [hC, hy0, hdot, hxs] at hc
      have hf : (z 0 - 1) ^ 2 * (z 0 + 2) = 0 := by nlinarith [hc]
      have ht : -1 ≤ z 0 := by nlinarith [xSq_nonneg z]
      have ht2 : z 0 + 2 ≠ 0 := by linarith
      have ht1 : z 0 = 1 := by
        have hh := (mul_eq_zero.mp hf).resolve_right ht2
        nlinarith [sq_nonneg (z 0 - 1)]
      exact ⟨by rw [hxs, ht1]; norm_num, Or.inl ht1⟩
    · refine ⟨hx, ?_⟩
      have hdot := dotTerm_zero_of_xSq_zero z hx
      have hsplit := Q_decomp z
      rw [hQ, hx] at hsplit
      have hys : ySq z = 1 - z 0 ^ 2 := by linarith
      have hc := C_decomp z
      rw [hC, hx, hdot, hys] at hc
      have hf : (z 0 - 1) * (2 * z 0 + 1) ^ 2 = 0 := by nlinarith [hc]
      rcases mul_eq_zero.mp hf with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by nlinarith [sq_nonneg (2 * z 0 + 1)])
  · rintro ⟨hx, ht | ht⟩
    all_goals
      have hdot := dotTerm_zero_of_xSq_zero z hx
      have hsplit := Q_decomp z
      rw [hQ, hx, ht] at hsplit
      rw [C_decomp, hx, ht, hdot]
      nlinarith

theorem xSq_zero_iff (z : Fin 14 → ℝ) :
    xSq z = 0 ↔ z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 ∧ z 4 = 0 := by
  unfold xSq
  constructor
  · intro h
    have h1 := sq_nonneg (z 1)
    have h2 := sq_nonneg (z 2)
    have h3 := sq_nonneg (z 3)
    have h4 := sq_nonneg (z 4)
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp [h1, h2, h3, h4]

theorem cubic_unit_maximizers_coordinates (z : Fin 14 → ℝ) (hQ : Q z = 1) :
    C z = 1 ↔ (z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 ∧ z 4 = 0) ∧
      (z 0 = 1 ∨ z 0 = -1 / 2) := by
  rw [cubic_unit_maximizers z hQ, xSq_zero_iff]

theorem xSq_scale (z : Fin 14 → ℝ) (r : ℝ) :
    xSq (fun i => r * z i) = r ^ 2 * xSq z := by
  unfold xSq
  ring

/-- Global equality classification for the sharp homogeneous cubic bound. -/
theorem cubic_upper_equality (z : Fin 14 → ℝ) :
    C z = radius z ^ 3 ↔ xSq z = 0 ∧
      (z 0 = radius z ∨ z 0 = -radius z / 2) := by
  by_cases hz : Q z = 0
  · have heq := (Q_eq_zero_iff z).mp hz
    subst z
    simp [C, cubicPoly, radius, Q_eq_sum, xSq]
  · have hr : 0 < radius z := Real.sqrt_pos.mpr (lt_of_le_of_ne (Q_nonneg z) (Ne.symm hz))
    have hr0 : radius z ≠ 0 := ne_of_gt hr
    have hn : Q (fun i => (radius z)⁻¹ * z i) = 1 := by
      rw [Q_scale, ← radius_sq]
      field_simp
    have hc := cubic_unit_maximizers (fun i => (radius z)⁻¹ * z i) hn
    rw [C_scale, xSq_scale] at hc
    field_simp [hr0] at hc
    simpa only [mul_zero, eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)] using hc

theorem cubic_upper_equality_coordinates (z : Fin 14 → ℝ) :
    C z = radius z ^ 3 ↔ (z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 ∧ z 4 = 0) ∧
      (z 0 = radius z ∨ z 0 = -radius z / 2) := by
  rw [cubic_upper_equality, xSq_zero_iff]

end PersistentSOS
