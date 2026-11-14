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
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Radial

Part of the explicit persistent quartic SOS counterexample.
-/

@[expose] public section

namespace PersistentSOS

/-- The one - variable radial lower envelope. -/
noncomputable def radialValue (σ a b r : ℝ) : ℝ := σ / 4 * r ^ 4 - b * r ^ 3 - a / 2 * r ^ 2

theorem minimizingRadius_pos {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hb : 0 < b) :
    0 < minimizingRadius σ a b := by
  unfold minimizingRadius
  positivity

theorem minimizingRadius_equation {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    σ * minimizingRadius σ a b ^ 2 = 3 * b * minimizingRadius σ a b + a := by
  have hd : 0 ≤ 9 * b ^ 2 + 4 * a * σ := by positivity
  have hs := Real.sq_sqrt hd
  unfold minimizingRadius
  field_simp
  ring_nf at hs ⊢
  nlinarith

theorem radial_at_minimizingRadius {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    radialValue σ a b (minimizingRadius σ a b) = minimumValue σ a b := by
  have he := minimizingRadius_equation (b := b) hσ ha
  unfold radialValue minimumValue
  linear_combination (minimizingRadius σ a b) ^ 2 / 4 * he

theorem radial_factorization {σ a b r s : ℝ} (he : σ * r ^ 2 = 3 * b * r + a) :
    radialValue σ a b s + (b * r ^ 3 + a * r ^ 2) / 4 =
      (s - r) ^ 2 * (σ * s ^ 2 + (2 * σ * r - 4 * b) * s + b * r + a) / 4 := by
  unfold radialValue
  linear_combination (3 * s ^ 2 - 2 * r * s) / 4 * he

theorem radial_global_minimum {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) :
    minimumValue σ a b ≤ radialValue σ a b s := by
  set r := minimizingRadius σ a b with hrdef
  have hr : 0 < r := minimizingRadius_pos hσ ha hb
  have he : σ * r ^ 2 = 3 * b * r + a := minimizingRadius_equation hσ ha
  have hcoef : 0 < 2 * σ * r - 4 * b := by nlinarith
  have hbr : 0 ≤ σ * s ^ 2 + (2 * σ * r - 4 * b) * s + b * r + a := by positivity
  have hprod := mul_nonneg (sq_nonneg (s - r)) hbr
  have hf := radial_factorization (s := s) he
  change -(b * r ^ 3 + a * r ^ 2) / 4 ≤ _
  linarith

/-- The radial minimizer is unique among nonnegative radii. -/
theorem radial_minimum_eq_iff {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) :
    radialValue σ a b s = minimumValue σ a b ↔ s = minimizingRadius σ a b := by
  set r := minimizingRadius σ a b with hrdef
  have hr : 0 < r := minimizingRadius_pos hσ ha hb
  have he : σ * r ^ 2 = 3 * b * r + a := minimizingRadius_equation hσ ha
  have hcoef : 0 < 2 * σ * r - 4 * b := by nlinarith
  have hbr : 0 < σ * s ^ 2 + (2 * σ * r - 4 * b) * s + b * r + a := by positivity
  constructor
  · intro h
    have hf := radial_factorization (s := s) he
    change radialValue σ a b s = -(b * r ^ 3 + a * r ^ 2) / 4 at h
    have hz : (s - r) ^ 2 * (σ * s ^ 2 + (2 * σ * r - 4 * b) * s + b * r + a) = 0 := by linarith
    have hsq := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hbr)
    nlinarith [sq_nonneg (s - r)]
  · rintro rfl
    exact radial_at_minimizingRadius hσ ha

end PersistentSOS
