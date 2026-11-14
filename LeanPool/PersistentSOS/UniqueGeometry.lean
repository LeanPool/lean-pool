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

public import LeanPool.PersistentSOS.Geometry
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Unique Geometry

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section

namespace PersistentSOS

/-- The selected cubic is the explicit convex combination of the original
cubic and the first coordinate times the squared Euclidean norm. -/
theorem unique_cubic_eq (z : Fin 14 → ℝ) :
    uniqueCubic z = (1000 * C z + z 0 * Q z) / 1001 := by
  simp [uniqueCubic, uniqueCubicPoly, C, Q]
  ring

/-- The selected quartic is evaluated on ordinary real vectors. -/
theorem unique_objective_eq (σ a b : ℝ) (z : Fin 14 → ℝ) :
    uniqueObjective σ a b z = σ / 4 * Q z ^ 2 - a / 2 * Q z - b * uniqueCubic z := by
  simp [uniqueObjective, uniqueQuarticPoly, Q, uniqueCubic]

/-- Every coordinate has absolute value bounded by the Euclidean radius. -/
theorem coordinate_abs_le_radius (z : Fin 14 → ℝ) (i : Fin 14) :
    |z i| ≤ radius z := by
  have hi : z i ^ 2 ≤ Q z := by
    rw [Q_eq_sum]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have hr := radius_nonneg z
  have hs := radius_sq z
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Squared distance to a point on the distinguished axis. -/
theorem Q_sub_axis (z : Fin 14 → ℝ) (r : ℝ) :
    Q (fun i => z i - axis r i) = Q z - 2 * r * z 0 + r ^ 2 := by
  simp [Q_eq_sum, axis, Fin.sum_univ_succ]
  ring

/-- Equality of the first coordinate with the radius forces all transverse
coordinates to vanish. -/
theorem eq_axis_of_first_eq_radius (z : Fin 14 → ℝ) (h : z 0 = radius z) :
    z = axis (radius z) := by
  have hq : Q (fun i => z i - axis (radius z) i) = 0 := by
    rw [Q_sub_axis, ← radius_sq, h]
    ring
  have hv := (Q_eq_zero_iff _).mp hq
  funext i
  have hi := congrFun hv i
  simpa only [Pi.zero_apply, sub_eq_zero] using hi

/-- The deficit separates into two nonnegative terms. -/
theorem unique_cubic_deficit (z : Fin 14 → ℝ) :
    radius z ^ 3 - uniqueCubic z =
      (1000 * (radius z ^ 3 - C z) + radius z ^ 2 * (radius z - z 0)) / 1001 := by
  rw [unique_cubic_eq, ← radius_sq]
  ring

/-- The original sharp bound and a coordinate bound give the same upper
bound for the selected cubic. -/
theorem unique_cubic_le (z : Fin 14 → ℝ) : uniqueCubic z ≤ radius z ^ 3 := by
  have hc := (le_abs_self (C z)).trans (cubic_abs_le z)
  have ht := (le_abs_self (z 0)).trans (coordinate_abs_le_radius z 0)
  apply sub_nonneg.mp
  rw [unique_cubic_deficit]
  exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hc))
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht))) (by norm_num)

/-- The selected cubic remains homogeneous of degree three. -/
theorem unique_cubic_scale (z : Fin 14 → ℝ) (r : ℝ) :
    uniqueCubic (fun i => r * z i) = r ^ 3 * uniqueCubic z := by
  rw [unique_cubic_eq, C_scale, Q_scale, unique_cubic_eq]
  ring

theorem unique_cubic_neg (z : Fin 14 → ℝ) :
    uniqueCubic (fun i => -z i) = -uniqueCubic z := by
  convert unique_cubic_scale z (-1) using 1 <;> norm_num

theorem radius_neg (z : Fin 14 → ℝ) : radius (fun i => -z i) = radius z := by
  unfold radius
  congr 1
  convert Q_scale z (-1) using 1 <;> norm_num

/-- The selected cubic has the sharp global homogeneous bound. -/
theorem unique_cubic_abs_le (z : Fin 14 → ℝ) : |uniqueCubic z| ≤ radius z ^ 3 := by
  have hu := unique_cubic_le z
  have hl := unique_cubic_le (fun i => -z i)
  rw [unique_cubic_neg, radius_neg] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

@[simp] theorem unique_cubic_axis (r : ℝ) : uniqueCubic (axis r) = r ^ 3 := by
  rw [unique_cubic_eq, C_axis, Q_axis]
  simp [axis]
  ring

/-- Equality in the upper cubic bound occurs exactly on the nonnegative
part of the distinguished coordinate axis, including the origin. -/
theorem unique_cubic_upper_equality (z : Fin 14 → ℝ) :
    uniqueCubic z = radius z ^ 3 ↔ z = axis (radius z) := by
  constructor
  · intro heq
    by_cases hz : radius z = 0
    · have hQ : Q z = 0 := by rw [← radius_sq, hz]; norm_num
      have hv := (Q_eq_zero_iff z).mp hQ
      rw [hz, hv]
      funext i
      simp [axis]
    · have hc := (le_abs_self (C z)).trans (cubic_abs_le z)
      have ht := (le_abs_self (z 0)).trans (coordinate_abs_le_radius z 0)
      have hd := unique_cubic_deficit z
      rw [heq, sub_self] at hd
      have hp := mul_nonneg (sq_nonneg (radius z)) (sub_nonneg.mpr ht)
      have hs : radius z ^ 2 * (radius z - z 0) = 0 := by nlinarith
      have hfirst := (mul_eq_zero.mp hs).resolve_left (pow_ne_zero 2 hz)
      exact eq_axis_of_first_eq_radius z (by linarith)
  · intro h
    calc
      uniqueCubic z = uniqueCubic (axis (radius z)) := congrArg uniqueCubic h
      _ = radius z ^ 3 := unique_cubic_axis _

/-- The selected cubic attains its unit - sphere maximum only at the first
coordinate unit vector. -/
theorem unique_cubic_unit_maximizer (z : Fin 14 → ℝ) (hQ : Q z = 1) :
    uniqueCubic z = 1 ↔ z = axis 1 := by
  have hr : radius z = 1 := by rw [radius, hQ]; norm_num
  simpa only [hr, one_pow] using unique_cubic_upper_equality z

/-- Decomposition into the radial envelope and the selected cubic deficit. -/
theorem unique_objective_radial_decomposition (σ a b : ℝ) (z : Fin 14 → ℝ) :
    uniqueObjective σ a b z = radialValue σ a b (radius z) +
      b * (radius z ^ 3 - uniqueCubic z) := by
  rw [unique_objective_eq, ← radius_sq]
  unfold radialValue
  ring

/-- Global optimality for every positive real regularization, quadratic
strength and cubic strength. -/
theorem unique_objective_global_lower_bound {σ a b : ℝ} (hσ : 0 < σ)
    (ha : 0 < a) (hb : 0 < b) (z : Fin 14 → ℝ) :
    minimumValue σ a b ≤ uniqueObjective σ a b z := by
  have hc := unique_cubic_le z
  have hscaled := mul_le_mul_of_nonneg_left hc (le_of_lt hb)
  have hrad := radial_global_minimum hσ ha hb (radius_nonneg z)
  rw [unique_objective_eq, ← radius_sq z]
  unfold radialValue at hrad
  nlinarith

/-- The distinguished point attains the explicit minimum. -/
theorem unique_objective_axis_attainment {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    uniqueObjective σ a b (axis (minimizingRadius σ a b)) = minimumValue σ a b := by
  rw [unique_objective_eq, Q_axis, unique_cubic_axis]
  calc
    _ = radialValue σ a b (minimizingRadius σ a b) := by unfold radialValue; ring
    _ = minimumValue σ a b := radial_at_minimizingRadius hσ ha

/-- The global minimizer is unique for every positive choice of all three
real parameters. -/
theorem unique_objective_minimizer {σ a b : ℝ} (hσ : 0 < σ)
    (ha : 0 < a) (hb : 0 < b) (z : Fin 14 → ℝ) :
    uniqueObjective σ a b z = minimumValue σ a b ↔
      z = axis (minimizingRadius σ a b) := by
  constructor
  · intro hobj
    have hrad := radial_global_minimum hσ ha hb (radius_nonneg z)
    have hc := unique_cubic_le z
    have hdef := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hc)
    have hid := unique_objective_radial_decomposition σ a b z
    have heq : radialValue σ a b (radius z) = minimumValue σ a b := by linarith
    have hr := (radial_minimum_eq_iff hσ ha hb (radius_nonneg z)).mp heq
    have hzero : b * (radius z ^ 3 - uniqueCubic z) = 0 := by linarith
    have hd := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hb)
    have hu : uniqueCubic z = radius z ^ 3 := by linarith
    have hz := (unique_cubic_upper_equality z).mp hu
    simpa only [hr] using hz
  · rintro rfl
    exact unique_objective_axis_attainment hσ ha

end PersistentSOS
