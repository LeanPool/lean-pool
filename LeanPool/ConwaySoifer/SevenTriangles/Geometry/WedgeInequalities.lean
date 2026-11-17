/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Polynomial inequalities for the 120-degree wedge area bounds. -/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

namespace ConwaySoifer.SevenTriangles

/-- Positivity of the determinant `c₀² + c₀ c₁ + c₁²` of two adjacent edge normals. -/
theorem quadDet_pos {c₀ c₁ : ℝ} (h : c₀ ≠ 0) : 0 < c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 := by
  have h1 : 0 < c₀ ^ 2 := by
    positivity
  nlinarith [sq_nonneg (c₁ + c₀ / 2)]

/-- Algebraic core of the strengthened bound: with `s² = X² + X Z + Z²` and
`(X + Z) a + X b < s (a + b)`, the quadratic form `(X+Z) b² + 2 Z a b - X a²` is nonnegative. -/
theorem strong_core (s X Z a b : ℝ) (hs : 0 < s) (hX : 0 < X) (hZ : 0 ≤ Z) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hD : s ^ 2 = X ^ 2 + X * Z + Z ^ 2) (h : (X + Z) * a + X * b < s * (a + b)) :
    0 ≤ (X + Z) * b ^ 2 + 2 * Z * a * b - X * a ^ 2 := by
  have hC : s ≤ X + Z := by
    by_contra hne
    push Not at hne
    nlinarith [mul_pos (sub_pos.2 hne) (by positivity : 0 < s + (X + Z))]
  have hXs : X ≤ s := by
    by_contra hne
    push Not at hne
    nlinarith [mul_pos (sub_pos.2 hne) (by positivity : 0 < s + X)]
  have hXs' : X < s := by
    rcases lt_or_eq_of_le hXs with h' | h'
    · exact h'
    · exfalso
      have hZ0 : Z = 0 := by
        nlinarith
      subst hZ0
      rw [h'] at h
      nlinarith
  -- (X + Z - s) a < (s - X) b
  have h1 : (X + Z - s) * a < (s - X) * b := by
    linarith
  have hid : (X + Z - s) * (s + Z) = X * (s - X) := by
    linear_combination -hD
  have h2 : (s - X) * (X * a) < (s - X) * ((s + Z) * b) := by
    have := mul_lt_mul_of_pos_right h1 (by positivity : 0 < s + Z)
    nlinarith
  have h3 : X * a < (s + Z) * b := lt_of_mul_lt_mul_left h2 (by linarith)
  have hid2 : (s + Z) * ((X + Z) * b - (s - Z) * a) = (X + Z) * ((s + Z) * b - X * a) := by
    linear_combination (-a) * hD
  have h4 : 0 < (X + Z) * b - (s - Z) * a := by
    have : 0 < (s + Z) * ((X + Z) * b - (s - Z) * a) := by
      rw [hid2]
      exact mul_pos (by linarith) (by linarith)
    exact pos_of_mul_pos_right this (by linarith)
  have hid3 : (X + Z) * ((X + Z) * b ^ 2 + 2 * Z * a * b - X * a ^ 2) =
      ((X + Z) * b - (s - Z) * a) * ((X + Z) * b + (s + Z) * a) := by
    linear_combination (a ^ 2) * hD
  have h5 : 0 ≤ (X + Z) * ((X + Z) * b ^ 2 + 2 * Z * a * b - X * a ^ 2) := by
    rw [hid3]
    exact mul_nonneg h4.le (by positivity)
  exact nonneg_of_mul_nonneg_right h5 (by linarith)

/-- Quadrilateral, weak bound: `D · min(a², b²) ≤ D² - X (2 X a b + (X - c₁) a² + c₁ b²)` with
`D = X² - X c₁ + c₁²`. -/
theorem quad_core_weak (X c₁ a b : ℝ) (hX : 0 < X) (ha : 0 < a) (hb : 0 < b)
    (hσ₁ : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b))
    (h1 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + c₁ * a)
    (h2 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + (X - c₁) * b) :
    (X ^ 2 - X * c₁ + c₁ ^ 2) * min (a ^ 2) (b ^ 2) ≤
      (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 - X * (2 * X * a * b + (X - c₁) * a ^ 2 + c₁ * b ^ 2) := by
  have hab : 0 ≤ a * b := by
    positivity
  rcases le_or_gt 0 c₁ with hc₁ | hc₁
  · rcases le_or_gt c₁ X with hc₁X | hc₁X
    · -- type 1: `0 ≤ c₁ ≤ X`
      have hsq : (X * (a + b)) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have hX2 : 0 ≤ c₁ * (X - c₁) := mul_nonneg hc₁ (by linarith)
      rcases le_total (a ^ 2) (b ^ 2) with hm | hm
      · rw [min_eq_left hm]
        nlinarith only [hsq, mul_nonneg (mul_nonneg hX.le (sub_nonneg.2 hc₁X)) (sub_nonneg.2 hm),
          mul_nonneg hX2 (sq_nonneg a)]
      · rw [min_eq_right hm]
        nlinarith only [hsq, mul_nonneg (mul_nonneg hX.le hc₁) (sub_nonneg.2 hm),
          mul_nonneg hX2 (sq_nonneg b)]
    · -- type 2b: `c₁ > X`, i.e. `c₂ < 0`
      have hZ : 0 < c₁ - X := by
        linarith
      have hsq : (X * a + c₁ * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have hXZ : 0 ≤ X * (c₁ - X) := mul_nonneg hX.le hZ.le
      rcases le_total (a ^ 2) (b ^ 2) with hm | hm
      · rw [min_eq_left hm]
        nlinarith only [hsq, mul_nonneg (mul_nonneg hc₁ hZ.le) (sub_nonneg.2 hm),
          mul_nonneg hXZ (sq_nonneg a), mul_nonneg (mul_nonneg hX.le hZ.le) hab]
      · rw [min_eq_right hm]
        nlinarith only [hsq, mul_nonneg (mul_nonneg hX.le hc₁) (sub_nonneg.2 hm),
          mul_nonneg hXZ (sq_nonneg b), mul_nonneg (mul_nonneg hX.le hZ.le) hab]
  · -- type 2a: `c₁ < 0`
    have hZ : 0 < -c₁ := by
      linarith
    have hsq : ((X - c₁) * a + X * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) (by linarith) 2
    have hXZ : 0 ≤ X * (-c₁) := mul_nonneg hX.le hZ.le
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [min_eq_left hm]
      nlinarith only [hsq,
        mul_nonneg (mul_nonneg hX.le (by linarith : (0 : ℝ) ≤ X - c₁)) (sub_nonneg.2 hm),
        mul_nonneg hXZ (sq_nonneg a), mul_nonneg hXZ hab]
    · rw [min_eq_right hm]
      nlinarith only [hsq,
        mul_nonneg (mul_nonneg hZ.le (by linarith : (0 : ℝ) ≤ X - c₁)) (sub_nonneg.2 hm),
        mul_nonneg hXZ (sq_nonneg b), mul_nonneg hXZ hab]

/-- Quadrilateral, strong bound (`s < a + b`). -/
theorem quad_core_strong (s X c₁ a b : ℝ) (hs : 0 < s) (hX : 0 < X) (ha : 0 < a) (hb : 0 < b)
    (hD : s ^ 2 = X ^ 2 - X * c₁ + c₁ ^ 2)
    (hσ₁ : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b))
    (h1 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + c₁ * a)
    (h2 : 0 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) - X * (a + b) + (X - c₁) * b)
    (hL₀B : 0 < X * a + c₁ * b) (hL₂A : 0 < X * b + (X - c₁) * a) (hab : s < a + b) :
    (X ^ 2 - X * c₁ + c₁ ^ 2) * max (a ^ 2) (b ^ 2) ≤
      (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 - X * (2 * X * a * b + (X - c₁) * a ^ 2 + c₁ * b ^ 2) := by
  have hab0 : 0 ≤ a * b := by
    positivity
  rcases le_or_gt 0 c₁ with hc₁ | hc₁
  · rcases le_or_gt c₁ X with hc₁X | hc₁X
    · -- type 1 is incompatible with `s < a + b`
      exfalso
      have hX2 : s ^ 2 ≤ X ^ 2 := by
        nlinarith [mul_nonneg hc₁ (sub_nonneg.2 hc₁X)]
      have hXs : s ≤ X := by
        by_contra h
        push Not at h
        nlinarith [mul_pos (sub_pos.2 h) (add_pos hs hX)]
      nlinarith [mul_lt_mul_of_pos_left hab hX, mul_le_mul_of_nonneg_right hXs hs.le]
    · -- type 2b: `Z' = c₁ - X > 0`
      have hZ : 0 < c₁ - X := by
        linarith
      have hsq : (X * a + c₁ * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      -- `Q'' ≥ D a²` from `X b > Z' a`
      have hQa : 0 ≤ (c₁ - X) * (-(c₁ - X) * a ^ 2 + 2 * X * a * b + c₁ * b ^ 2) := by
        apply mul_nonneg hZ.le
        nlinarith only [mul_pos hL₂A ha, mul_nonneg hc₁ (sq_nonneg b),
          mul_nonneg hZ.le (sq_nonneg a)]
      -- `Q'' ≥ D b²` from the strengthened hypothesis
      have hcore := strong_core s X (c₁ - X) b a hs hX hZ.le hb.le ha.le
        (by rw [hD]; ring) (by nlinarith [mul_lt_mul_of_pos_left hab hs])
      have hQb : 0 ≤ X * (c₁ * a ^ 2 + 2 * (c₁ - X) * a * b - X * b ^ 2) := by
        apply mul_nonneg hX.le
        nlinarith only [hcore]
      rcases le_total (a ^ 2) (b ^ 2) with hm | hm
      · rw [max_eq_right hm]
        nlinarith only [hsq, hQb]
      · rw [max_eq_left hm]
        nlinarith only [hsq, hQa]
  · -- type 2a: `Z = -c₁ > 0`
    have hZ : 0 < -c₁ := by
      linarith
    have hsq : ((X - c₁) * a + X * b) ^ 2 ≤ (X ^ 2 - X * c₁ + c₁ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) (by linarith) 2
    -- `Q ≥ D b²` from `X a > Z b`
    have hQb : 0 ≤ (-c₁) * ((X - c₁) * a ^ 2 + 2 * X * a * b - (-c₁) * b ^ 2) := by
      apply mul_nonneg hZ.le
      nlinarith only [mul_pos hL₀B hb,
        mul_nonneg (by linarith : (0 : ℝ) ≤ X - c₁) (sq_nonneg a),
        mul_nonneg hZ.le (sq_nonneg b)]
    have hcore := strong_core s X (-c₁) a b hs hX hZ.le ha.le hb.le
      (by rw [hD]; ring) (by nlinarith [mul_lt_mul_of_pos_left hab hs])
    have hQa : 0 ≤ X * ((X - c₁) * b ^ 2 + 2 * (-c₁) * a * b - X * a ^ 2) := by
      apply mul_nonneg hX.le
      nlinarith only [hcore]
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [max_eq_right hm]
      nlinarith only [hsq, hQb]
    · rw [max_eq_left hm]
      nlinarith only [hsq, hQa]

/-- Pentagon, weak bound: `D · min ≤ Q'` with `Q' = X C a² + 2 X Z a b + Z C b²`, `C = X + Z`. -/
theorem pent_core_weak (X Z a b : ℝ) (hX : 0 < X) (hZ : 0 < Z) (ha : 0 < a) (hb : 0 < b) :
    (X ^ 2 + X * Z + Z ^ 2) * min (a ^ 2) (b ^ 2) ≤
      X * (X + Z) * a ^ 2 + 2 * X * Z * a * b + Z * (X + Z) * b ^ 2 := by
  have hab : 0 ≤ a * b := by
    positivity
  have hXZ : 0 ≤ X * Z := by
    positivity
  rcases le_total (a ^ 2) (b ^ 2) with hm | hm
  · rw [min_eq_left hm]
    nlinarith only [mul_nonneg (mul_nonneg hZ.le (by linarith : (0 : ℝ) ≤ X + Z)) (sub_nonneg.2 hm),
      mul_nonneg hXZ (sq_nonneg a), mul_nonneg hXZ hab]
  · rw [min_eq_right hm]
    nlinarith only [mul_nonneg (mul_nonneg hX.le (by linarith : (0 : ℝ) ≤ X + Z)) (sub_nonneg.2 hm),
      mul_nonneg hXZ (sq_nonneg b), mul_nonneg hXZ hab]

/-- Pentagon, strong bound (`s < a + b`), with `D ≥ C a + Z b` and `D > X a + C b`. -/
theorem pent_core_strong (s X Z a b : ℝ) (hs : 0 < s) (hX : 0 < X) (hZ : 0 < Z) (ha : 0 < a)
    (hb : 0 < b) (hD : s ^ 2 = X ^ 2 + X * Z + Z ^ 2)
    (h1 : (X + Z) * a + Z * b ≤ X ^ 2 + X * Z + Z ^ 2)
    (h2 : X * a + (X + Z) * b < X ^ 2 + X * Z + Z ^ 2) (hab : s < a + b) :
    (X ^ 2 + X * Z + Z ^ 2) * max (a ^ 2) (b ^ 2) ≤
      X * (X + Z) * a ^ 2 + 2 * X * Z * a * b + Z * (X + Z) * b ^ 2 := by
  have hab0 : 0 ≤ a * b := by
    positivity
  have hsab : s * s < s * (a + b) := mul_lt_mul_of_pos_left hab hs
  rcases le_total (Z * a) (X * b) with hZX | hZX
  · -- `Z a ≤ X b`
    have hQa : 0 ≤ Z * (-Z * a ^ 2 + 2 * X * a * b + (X + Z) * b ^ 2) := by
      apply mul_nonneg hZ.le
      nlinarith [mul_le_mul_of_nonneg_left hZX ha.le, mul_nonneg (by linarith : (0 : ℝ) ≤ X + Z)
          (sq_nonneg b)]
    have hcore := strong_core s X Z b a hs hX hZ.le hb.le ha.le hD (by nlinarith)
    have hQb : 0 ≤ X * ((X + Z) * a ^ 2 + 2 * Z * a * b - X * b ^ 2) := by
      apply mul_nonneg hX.le
      nlinarith [hcore]
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [max_eq_right hm]
      nlinarith
    · rw [max_eq_left hm]
      nlinarith
  · -- `X b ≤ Z a`
    have hQb : 0 ≤ X * ((X + Z) * a ^ 2 + 2 * Z * a * b - X * b ^ 2) := by
      apply mul_nonneg hX.le
      nlinarith [mul_le_mul_of_nonneg_left hZX hb.le, mul_nonneg (by linarith : (0 : ℝ) ≤ X + Z)
          (sq_nonneg a)]
    have hcore := strong_core s Z X a b hs hZ hX.le ha.le hb.le (by rw [hD]; ring) (by nlinarith)
    have hQa : 0 ≤ Z * ((Z + X) * b ^ 2 + 2 * X * a * b - Z * a ^ 2) := by
      apply mul_nonneg hZ.le
      nlinarith [hcore]
    rcases le_total (a ^ 2) (b ^ 2) with hm | hm
    · rw [max_eq_right hm]
      nlinarith
    · rw [max_eq_left hm]
      nlinarith

/-- The quadrilateral area bound in the form produced by `coverBound_quad`. -/
theorem quad_bound (s c₀ c₁ a b : ℝ) (hs : 0 < s) (hc₀ : c₀ < 0) (ha : 0 < a) (hb : 0 < b)
    (hD : s ^ 2 = c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2)
    (hσ₁ : 0 ≤ c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b))
    (hL₁A : 0 ≤ c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b) + c₁ * a)
    (hL₁B : 0 ≤ c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 + c₀ * (a + b) + (-c₀ - c₁) * b)
    (hL₀B : 0 < -c₀ * a + c₁ * b) (hL₂A : 0 < -c₀ * b + (-c₀ - c₁) * a) :
    c₀ * (2 * c₀ * a * b + (c₀ + c₁) * a ^ 2 - c₁ * b ^ 2) /
        (2 * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2)) ≤ s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2 ∧
      (s < a + b → c₀ * (2 * c₀ * a * b + (c₀ + c₁) * a ^ 2 - c₁ * b ^ 2) /
        (2 * (c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2)) ≤ s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2) := by
  have hDpos : 0 < c₀ ^ 2 + c₀ * c₁ + c₁ ^ 2 := quadDet_pos hc₀.ne
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -c₀ := ⟨_, rfl⟩
  have hc₀' : c₀ = -X := by
    linarith
  subst hc₀'
  have hXpos : 0 < X := by
    linarith
  have hD' : s ^ 2 = X ^ 2 - X * c₁ + c₁ ^ 2 := by
    rw [hD]; ring
  have hw := quad_core_weak X c₁ a b hXpos ha hb (by linarith) (by linarith) (by linarith)
  constructor
  · rw [div_le_iff₀ (by positivity), hD]
    linarith
  · intro hab
    have hst := quad_core_strong s X c₁ a b hs hXpos ha hb hD' (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hab
    rw [div_le_iff₀ (by positivity), hD]
    linarith

/-- The pentagon area bound in the form produced by `coverBound_pent`. -/
theorem pent_bound (s c₀ c₂ σ₂ a b : ℝ) (hs : 0 < s) (hc₀ : c₀ < 0) (hc₂ : c₂ < 0) (ha : 0 < a)
    (hb : 0 < b) (hD : s ^ 2 = c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2)
    (hσ₂ : σ₂ = c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 + c₀ * a + c₂ * b)
    (hL₂A : 0 ≤ σ₂ + c₂ * a) (hL₂B : 0 < σ₂ + c₀ * b) :
    ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 -
        (-c₀ * (-c₀ - c₂) * a ^ 2 + 2 * c₀ * c₂ * a * b - c₂ * (-c₀ - c₂) * b ^ 2)) /
        (2 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2)) ≤ s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2 ∧
      (s < a + b → ((c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2) ^ 2 -
        (-c₀ * (-c₀ - c₂) * a ^ 2 + 2 * c₀ * c₂ * a * b - c₂ * (-c₀ - c₂) * b ^ 2)) /
        (2 * (c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2)) ≤ s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2) := by
  have hDpos : 0 < c₀ ^ 2 + c₀ * c₂ + c₂ ^ 2 := quadDet_pos hc₀.ne
  subst hσ₂
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -c₀ := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = -c₂ := ⟨_, rfl⟩
  have hc₀' : c₀ = -X := by
    linarith
  have hc₂' : c₂ = -Z := by
    linarith
  subst hc₀' hc₂'
  have hXpos : 0 < X := by
    linarith
  have hZpos : 0 < Z := by
    linarith
  have hD' : s ^ 2 = X ^ 2 + X * Z + Z ^ 2 := by
    rw [hD]; ring
  have hw := pent_core_weak X Z a b hXpos hZpos ha hb
  constructor
  · rw [div_le_iff₀ (by positivity), hD]
    linarith
  · intro hab
    have hst := pent_core_strong s X Z a b hs hXpos hZpos ha hb hD' (by linarith) (by linarith) hab
    rw [div_le_iff₀ (by positivity), hD]
    linarith

/-- Same-side bound from the diameter. -/
theorem same_side_bound (s a b : ℝ) (hdiam : a ^ 2 + a * b + b ^ 2 ≤ s ^ 2) :
    a * b / 2 ≤ s ^ 2 / 2 - min (a ^ 2) (b ^ 2) / 2 ∧
      a * b / 2 ≤ s ^ 2 / 2 - max (a ^ 2) (b ^ 2) / 2 := by
  constructor
  · nlinarith [min_le_left (a ^ 2) (b ^ 2), sq_nonneg b]
  · have := max_le (le_add_of_nonneg_right (sq_nonneg b) : a ^ 2 ≤ a ^ 2 + b ^ 2)
      (le_add_of_nonneg_left (sq_nonneg a) : b ^ 2 ≤ a ^ 2 + b ^ 2)
    nlinarith

end ConwaySoifer.SevenTriangles
