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

public import LeanPool.PersistentSOS.Transfer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Geometry

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section

namespace PersistentSOS

/-- The objective separates into its radial envelope and a nonnegative cubic deficit. -/
theorem objective_radial_decomposition (σ a b : ℝ) (z : Fin 14 → ℝ) :
    objective σ a b z = radialValue σ a b (radius z) +
      b * (radius z ^ 3 - C z) := by
  rw [objective_eq, ← radius_sq]
  unfold radialValue
  ring

/-- Equality in the global lower bound requires the unique radial minimum and
    equality in the sharp cubic bound. -/
theorem objective_minimizer_radius_iff {σ a b : ℝ} (hσ : 0 < σ)
    (ha : 0 < a) (hb : 0 < b) (z : Fin 14 → ℝ) :
    objective σ a b z = minimumValue σ a b ↔
      radius z = minimizingRadius σ a b ∧ C z = radius z ^ 3 := by
  constructor
  · intro hobj
    have hrad := radial_global_minimum hσ ha hb (radius_nonneg z)
    have hc := (le_abs_self (C z)).trans (cubic_abs_le z)
    have hdef := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hc)
    have hid := objective_radial_decomposition σ a b z
    have heq : radialValue σ a b (radius z) = minimumValue σ a b := by linarith
    have hr := (radial_minimum_eq_iff hσ ha hb (radius_nonneg z)).mp heq
    have hzero : b * (radius z ^ 3 - C z) = 0 := by linarith
    have hd := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hb)
    exact ⟨hr, by linarith⟩
  · rintro ⟨hr, hc⟩
    rw [objective_radial_decomposition, hc, sub_self, mul_zero, add_zero, hr]
    exact radial_at_minimizingRadius hσ ha

/-- Complete coordinate description of all global minimizers. Besides the
    distinguished axis point, they form a sphere in the nine `y` coordinates
    at first coordinate `-r / 2`, with squared radius `3 * r² / 4`. -/
theorem objective_all_minimizers {σ a b : ℝ} (hσ : 0 < σ)
    (ha : 0 < a) (hb : 0 < b) (z : Fin 14 → ℝ) :
    objective σ a b z = minimumValue σ a b ↔
      Q z = minimizingRadius σ a b ^ 2 ∧
      (z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 ∧ z 4 = 0) ∧
      (z 0 = minimizingRadius σ a b ∨ z 0 = -minimizingRadius σ a b / 2) := by
  rw [objective_minimizer_radius_iff hσ ha hb z]
  constructor
  · rintro ⟨hr, hc⟩
    obtain ⟨hx, ht⟩ := (cubic_upper_equality_coordinates z).mp hc
    exact ⟨by rw [← radius_sq, hr], hx, by simpa only [hr] using ht⟩
  · rintro ⟨hQ, hx, ht⟩
    have hp := minimizingRadius_pos hσ ha hb
    have hn := radius_nonneg z
    have hs := radius_sq z
    have hr : radius z = minimizingRadius σ a b := by nlinarith
    exact ⟨hr, (cubic_upper_equality_coordinates z).mpr ⟨hx, by simpa only [hr] using ht⟩⟩

end PersistentSOS
