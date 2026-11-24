/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-! Scalar polynomial bounds used by the BridgeLocal support fan. -/

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

public section

namespace ConwaySoifer.Simplified.BridgeLocalPolynomials

theorem polynomialPositive1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) < (((2 / 3) * (s ^ 2)) + ((4 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((2 / 3) * (s ^ 2)) + ((4 / 3) * s)) = s ^ 1 * ((4 / 3) + (2 / 3) * (s - 0) ^ 1) :=
      by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) = (1 + 4 * (s - 0) ^ 1 * ((1 / 6) - s) ^
      1 + (10 / 3) * (s - 0) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s
      ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s ^ 4)))
      = s ^ 1 * ((565 / 486) + (332 / 9) * ((1 / 6) - s) ^ 3 + (236 / 3) * (s - 0) ^ 1 * ((1 /
      6) - s) ^ 2 + (124 / 3) * (s - 0) ^ 2 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + (2 * (s ^ 3))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (s ^ 2) + (-1 * s) + (2 * (s ^ 3))) = ((47 / 54) + 28 * ((1 / 6) - s) ^ 3 + 48
      * (s - 0) ^ 1 * ((1 / 6) - s) ^ 2 + 18 * (s - 0) ^ 2 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ ((4 * (s ^ 5)) + (4 * (s ^ 6)) + ((-10 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 2))
      + ((2 / 3) * (s ^ 3))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((4 * (s ^ 5)) + (4 * (s ^ 6)) + ((-10 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 2)) + ((2
      / 3) * (s ^ 3))) = s ^ 2 * ((2 / 3) + 144 * (s - 0) ^ 1 * ((1 / 6) - s) ^ 3 + 312 * (s -
      0) ^ 2 * ((1 / 6) - s) ^ 2 + 216 * (s - 0) ^ 3 * ((1 / 6) - s) ^ 1 + 52 * (s - 0) ^ 4) :=
      by
    ring
  rw [heq]
  positivity

theorem polynomialPositive2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) < (s + ((-8 / 3) * (s ^ 2)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 3))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-8 / 3) * (s ^ 2)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 3))) = s ^ 1 *
      ((385 / 648) + (263 / 3) * ((1 / 6) - s) ^ 3 + 167 * (s - 0) ^ 1 * ((1 / 6) - s) ^ 2 + 79 *
      (s - 0) ^ 2 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (s + ((-4 / 3) * (s ^ 3)) + ((-1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-4 / 3) * (s ^ 3)) + ((-1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4))) = s ^ 1 *
      ((295 / 324) + (58 / 3) * ((1 / 6) - s) ^ 3 + 46 * (s - 0) ^ 1 * ((1 / 6) - s) ^ 2 + 26 *
      (s - 0) ^ 2 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (((-32 / 9) * (s ^ 4)) + ((-16 / 9) * (s ^ 7)) + ((4 / 3) * (s ^ 3)) + ((4 /
      3) * (s ^ 6)) + ((4 / 9) * (s ^ 8)) + ((20 / 9) * (s ^ 5))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-32 / 9) * (s ^ 4)) + ((-16 / 9) * (s ^ 7)) + ((4 / 3) * (s ^ 3)) + ((4 / 3) *
      (s ^ 6)) + ((4 / 9) * (s ^ 8)) + ((20 / 9) * (s ^ 5))) = s ^ 3 * ((14125 / 17496) + (36812
      / 9) * ((1 / 6) - s) ^ 5 + (142588 / 9) * (s - 0) ^ 1 * ((1 / 6) - s) ^ 4 + (206552 / 9) *
      (s - 0) ^ 2 * ((1 / 6) - s) ^ 3 + (132680 / 9) * (s - 0) ^ 3 * ((1 / 6) - s) ^ 2 + (31900
      / 9) * (s - 0) ^ 4 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) < (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4)) + ((8 / 3) * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4)) + ((8 / 3) * (s ^ 2))) = s ^ 2 * ((115 /
      54) + (58 / 3) * ((1 / 6) - s) ^ 2 + (56 / 3) * (s - 0) ^ 1 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (s + ((-8 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 2)) + ((4 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-8 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 2)) + ((4 / 3) * (s ^ 4))) = s ^ 1 *
      ((80 / 81) + (8 / 3) * ((1 / 6) - s) ^ 3 + 20 * (s - 0) ^ 1 * ((1 / 6) - s) ^ 2 + 16 * (s
      - 0) ^ 2 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ ((8 * (s ^ 6)) + ((-64 / 9) * (s ^ 7)) + ((-56 / 9) * (s ^ 4)) + ((8 / 3) *
      (s ^ 3)) + ((8 / 9) * (s ^ 5)) + ((16 / 9) * (s ^ 8))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((8 * (s ^ 6)) + ((-64 / 9) * (s ^ 7)) + ((-56 / 9) * (s ^ 4)) + ((8 / 3) * (s ^
      3)) + ((8 / 9) * (s ^ 5)) + ((16 / 9) * (s ^ 8))) = s ^ 3 * ((7375 / 4374) + (68624 / 9) *
      ((1 / 6) - s) ^ 5 + (270544 / 9) * (s - 0) ^ 1 * ((1 / 6) - s) ^ 4 + (397664 / 9) * (s -
      0) ^ 2 * ((1 / 6) - s) ^ 3 + (258560 / 9) * (s - 0) ^ 3 * ((1 / 6) - s) ^ 2 + (62800 / 9)
      * (s - 0) ^ 4 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (1 + (-1 * s) + (3 * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (-1 * s) + (3 * (s ^ 2))) = ((11 / 12) + 3 * ((1 / 6) - s) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) = s ^ 2 * ((19
      / 54) + (34 / 3) * ((1 / 6) - s) ^ 2 + (8 / 3) * (s - 0) ^ 1 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) < ((-2 * (s ^ 2)) + (2 * (s ^ 3)) + ((-1 / 3) * (s ^ 4)) + ((1 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((-2 * (s ^ 2)) + (2 * (s ^ 3)) + ((-1 / 3) * (s ^ 4)) + ((1 / 3) * s)) = s ^ 1 *
      ((35 / 648) + (181 / 3) * ((1 / 6) - s) ^ 3 + 109 * (s - 0) ^ 1 * ((1 / 6) - s) ^ 2 + 49 *
      (s - 0) ^ 2 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ ((-1 * (s ^ 2)) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((-1 * (s ^ 2)) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * s)) = s ^ 1 * ((325 / 648) +
      (107 / 3) * ((1 / 6) - s) ^ 3 + 71 * (s - 0) ^ 1 * ((1 / 6) - s) ^ 2 + 35 * (s - 0) ^ 2 *
      ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) ≤ (((-2 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 6)) + ((1 / 9) * (s ^ 2)) + ((1 /
      9) * (s ^ 8)) + ((2 / 3) * (s ^ 4)) + ((4 / 9) * (s ^ 5))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-2 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 6)) + ((1 / 9) * (s ^ 2)) + ((1 / 9) * (s
      ^ 8)) + ((2 / 3) * (s ^ 4)) + ((4 / 9) * (s ^ 5))) = s ^ 2 * ((8425 / 419904) + (38231 /
      9) * ((1 / 6) - s) ^ 6 + (60910 / 3) * (s - 0) ^ 1 * ((1 / 6) - s) ^ 5 + (115987 / 3) * (s
      - 0) ^ 2 * ((1 / 6) - s) ^ 4 + (330028 / 9) * (s - 0) ^ 3 * ((1 / 6) - s) ^ 3 + (51979 /
      3) * (s - 0) ^ 4 * ((1 / 6) - s) ^ 2 + (9790 / 3) * (s - 0) ^ 5 * ((1 / 6) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    (0 : ℝ) < (((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)) = s ^ 1 * ((5 / 18) + (1 / 3) * ((1 / 6) - s)
      ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) < (((1 / 3) * (s ^ 2)) + ((5 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((1 / 3) * (s ^ 2)) + ((5 / 3) * s)) = s ^ 1 * ((31 / 18) + (1 / 3) * (s - (1 / 6))
      ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) = ((59 / 54) + (32 / 3) * (s - (1 / 6))
      ^ 1 * ((5 / 24) - s) ^ 1 + 10 * (s - (1 / 6)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s
      ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s ^ 4)))
      = s ^ 1 * ((34637 / 31104) + (6092 / 9) * ((5 / 24) - s) ^ 3 + (4108 / 3) * (s - (1 / 6))
      ^ 1 * ((5 / 24) - s) ^ 2 + 692 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (1 + ((-2 / 3) * s) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 3)) + ((5 / 3) *
      (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-2 / 3) * s) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 3)) + ((5 / 3) * (s ^
      2))) = ((3647 / 3888) + (512 / 3) * ((5 / 24) - s) ^ 4 + 160 * (s - (1 / 6)) ^ 2 * ((5 /
      24) - s) ^ 2 + 1024 * (s - (1 / 6)) ^ 3 * ((5 / 24) - s) ^ 1 + (2081 / 3) * (s - (1 / 6))
      ^ 4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (((-20 / 9) * (s ^ 3)) + ((-1 / 3) * s) + ((1 / 9) * (s ^ 8)) + ((4 / 9) *
      (s ^ 7)) + ((14 / 9) * (s ^ 6)) + ((16 / 9) * (s ^ 5)) + ((20 / 9) * (s ^ 4)) + ((22 / 9) * (s
      ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-20 / 9) * (s ^ 3)) + ((-1 / 3) * s) + ((1 / 9) * (s ^ 8)) + ((4 / 9) * (s ^ 7))
      + ((14 / 9) * (s ^ 6)) + ((16 / 9) * (s ^ 5)) + ((20 / 9) * (s ^ 4)) + ((22 / 9) * (s ^
      2))) = s ^ 1 * ((61009 / 2519424) + (3316314112 / 9) * (s - (1 / 6)) ^ 1 * ((5 / 24) - s)
      ^ 6 + 2205004800 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 5 + (49492100864 / 9) * (s - (1 /
      6)) ^ 3 * ((5 / 24) - s) ^ 4 + (21948220480 / 3) * (s - (1 / 6)) ^ 4 * ((5 / 24) - s) ^ 3
      + (16429036720 / 3) * (s - (1 / 6)) ^ 5 * ((5 / 24) - s) ^ 2 + 2186812028 * (s - (1 / 6))
      ^ 6 * ((5 / 24) - s) ^ 1 + (3275487757 / 9) * (s - (1 / 6)) ^ 7) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) < (s + ((-7 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-7 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4))) = s ^ 1 *
      ((11381 / 20736) + (3478 / 3) * ((5 / 24) - s) ^ 3 + 2294 * (s - (1 / 6)) ^ 1 * ((5 / 24) -
      s) ^ 2 + 1134 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4)) + ((4 / 3) *
      (s ^ 3))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4)) + ((4 / 3) * (s ^
      3))) = ((29807 / 31104) + (2080 / 3) * ((5 / 24) - s) ^ 4 + 1408 * (s - (1 / 6)) ^ 1 * ((5
      / 24) - s) ^ 3 + 704 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 2 + (34 / 3) * (s - (1 / 6)) ^
      4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (((-5 / 9) * (s ^ 2)) + ((1 / 3) * s) + ((2 / 9) * (s ^ 4)) + ((4 / 9) * (s
      ^ 5)) + ((4 / 9) * (s ^ 8)) + ((10 / 9) * (s ^ 3)) + ((16 / 9) * (s ^ 7)) + ((20 / 9) * (s ^
      6))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-5 / 9) * (s ^ 2)) + ((1 / 3) * s) + ((2 / 9) * (s ^ 4)) + ((4 / 9) * (s ^ 5)) +
      ((4 / 9) * (s ^ 8)) + ((10 / 9) * (s ^ 3)) + ((16 / 9) * (s ^ 7)) + ((20 / 9) * (s ^ 6)))
      = s ^ 1 * ((2783078093 / 10319560704) + (149120204 / 9) * ((5 / 24) - s) ^ 7 + 87618036 *
      (s - (1 / 6)) ^ 1 * ((5 / 24) - s) ^ 6 + (567226772 / 3) * (s - (1 / 6)) ^ 2 * ((5 / 24) -
      s) ^ 5 + (634364236 / 3) * (s - (1 / 6)) ^ 3 * ((5 / 24) - s) ^ 4 + (1147993828 / 9) * (s
      - (1 / 6)) ^ 4 * ((5 / 24) - s) ^ 3 + 38371100 * (s - (1 / 6)) ^ 5 * ((5 / 24) - s) ^ 2 +
      (38200580 / 9) * (s - (1 / 6)) ^ 6 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg19 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (s + ((-4 / 3) * (s ^ 3)) + ((-1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-4 / 3) * (s ^ 3)) + ((-1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4))) = s ^ 1 *
      ((18221 / 20736) + (1318 / 3) * ((5 / 24) - s) ^ 3 + 902 * (s - (1 / 6)) ^ 1 * ((5 / 24) -
      s) ^ 2 + 462 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (((-32 / 9) * (s ^ 4)) + ((-16 / 9) * (s ^ 7)) + ((4 / 3) * (s ^ 3)) + ((4 /
      3) * (s ^ 6)) + ((4 / 9) * (s ^ 8)) + ((20 / 9) * (s ^ 5))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-32 / 9) * (s ^ 4)) + ((-16 / 9) * (s ^ 7)) + ((4 / 3) * (s ^ 3)) + ((4 / 3) *
      (s ^ 6)) + ((4 / 9) * (s ^ 8)) + ((20 / 9) * (s ^ 5))) = s ^ 3 * ((12503957 / 17915904) +
      (7840172 / 9) * ((5 / 24) - s) ^ 5 + (10344820 / 3) * (s - (1 / 6)) ^ 1 * ((5 / 24) - s) ^
      4 + (46061240 / 9) * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 3 + (10126696 / 3) * (s - (1 /
      6)) ^ 3 * ((5 / 24) - s) ^ 2 + (7513132 / 9) * (s - (1 / 6)) ^ 4 * ((5 / 24) - s) ^ 1) :=
      by
    ring
  rw [heq]
  positivity

theorem polynomialPositive8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) < (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4)) + ((8 / 3) * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4)) + ((8 / 3) * (s ^ 2))) = s ^ 2 * ((1729
      / 864) + 74 * ((5 / 24) - s) ^ 2 + (220 / 3) * (s - (1 / 6)) ^ 1 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg21 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (s + ((-8 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 2)) + ((4 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-8 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 2)) + ((4 / 3) * (s ^ 4))) = s ^ 1 *
      ((10013 / 10368) + (908 / 3) * ((5 / 24) - s) ^ 3 + 652 * (s - (1 / 6)) ^ 1 * ((5 / 24) -
      s) ^ 2 + 348 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg22 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ ((8 * (s ^ 6)) + ((-64 / 9) * (s ^ 7)) + ((-56 / 9) * (s ^ 4)) + ((8 / 3) *
      (s ^ 3)) + ((8 / 9) * (s ^ 5)) + ((16 / 9) * (s ^ 8))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((8 * (s ^ 6)) + ((-64 / 9) * (s ^ 7)) + ((-56 / 9) * (s ^ 4)) + ((8 / 3) * (s ^
      3)) + ((8 / 9) * (s ^ 5)) + ((16 / 9) * (s ^ 8))) = s ^ 3 * ((6577781 / 4478976) +
      (15587504 / 9) * ((5 / 24) - s) ^ 5 + (20620240 / 3) * (s - (1 / 6)) ^ 1 * ((5 / 24) - s)
      ^ 4 + (92038880 / 9) * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 3 + (20282272 / 3) * (s - (1 /
      6)) ^ 3 * ((5 / 24) - s) ^ 2 + (15081136 / 9) * (s - (1 / 6)) ^ 4 * ((5 / 24) - s) ^ 1) :=
      by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg23 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (1 + (-1 * s) + (3 * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (-1 * s) + (3 * (s ^ 2))) = ((11 / 12) + 3 * (s - (1 / 6)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg24 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) = s ^ 2 * ((37
      / 108) + (16 / 3) * ((5 / 24) - s) ^ 2 + (10 / 3) * (s - (1 / 6)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) < ((-2 * (s ^ 2)) + (2 * (s ^ 3)) + ((-1 / 3) * (s ^ 4)) + ((1 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((-2 * (s ^ 2)) + (2 * (s ^ 3)) + ((-1 / 3) * (s ^ 4)) + ((1 / 3) * s)) = s ^ 1 *
      ((19 / 41472) + (2221 / 3) * ((5 / 24) - s) ^ 3 + 1437 * (s - (1 / 6)) ^ 1 * ((5 / 24) - s)
      ^ 2 + 697 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg25 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ ((-1 * (s ^ 2)) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((-1 * (s ^ 2)) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * s)) = s ^ 1 * ((19133 / 41472) +
      (1667 / 3) * ((5 / 24) - s) ^ 3 + 1107 * (s - (1 / 6)) ^ 1 * ((5 / 24) - s) ^ 2 + 551 * (s
      - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg26 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) ≤ (((-2 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 6)) + ((1 / 9) * (s ^ 2)) + ((1 /
      9) * (s ^ 8)) + ((2 / 3) * (s ^ 4)) + ((4 / 9) * (s ^ 5))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-2 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 6)) + ((1 / 9) * (s ^ 2)) + ((1 / 9) * (s
      ^ 8)) + ((2 / 3) * (s ^ 4)) + ((4 / 9) * (s ^ 5))) = s ^ 2 * ((6758281 / 1719926784) +
      3083391 * ((5 / 24) - s) ^ 6 + (45476078 / 3) * (s - (1 / 6)) ^ 1 * ((5 / 24) - s) ^ 5 +
      29801073 * (s - (1 / 6)) ^ 2 * ((5 / 24) - s) ^ 4 + (263567948 / 9) * (s - (1 / 6)) ^ 3 *
      ((5 / 24) - s) ^ 3 + 14385249 * (s - (1 / 6)) ^ 4 * ((5 / 24) - s) ^ 2 + (8477078 / 3) *
      (s - (1 / 6)) ^ 5 * ((5 / 24) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    (0 : ℝ) < (((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)) = s ^ 1 * ((19 / 72) + (1 / 3) * ((5 / 24) -
      s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) < (((1 / 3) * (s ^ 2)) + ((5 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((1 / 3) * (s ^ 2)) + ((5 / 3) * s)) = s ^ 1 * ((125 / 72) + (1 / 3) * (s - (5 /
      24)) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg27 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) = ((959 / 864) + (28 / 3) * (s - (5 /
      24)) ^ 1 * ((1 / 4) - s) ^ 1 + (26 / 3) * (s - (5 / 24)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg28 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s
      ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s ^ 4)))
      = s ^ 1 * ((17 / 16) + (6356 / 9) * ((1 / 4) - s) ^ 3 + (4280 / 3) * (s - (5 / 24)) ^ 1 *
      ((1 / 4) - s) ^ 2 + 720 * (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg29 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (1 + ((-2 / 3) * s) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 3)) + ((5 / 3) *
      (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-2 / 3) * s) + ((1 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 3)) + ((5 / 3) * (s ^
      2))) = ((935713 / 995328) + (5252 / 3) * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 3 + 6502 *
      (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 2 + (23324 / 3) * (s - (5 / 24)) ^ 3 * ((1 / 4) - s)
      ^ 1 + (9071 / 3) * (s - (5 / 24)) ^ 4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg30 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (((-20 / 9) * (s ^ 3)) + ((-1 / 3) * s) + ((1 / 9) * (s ^ 8)) + ((4 / 9) *
      (s ^ 7)) + ((14 / 9) * (s ^ 6)) + ((16 / 9) * (s ^ 5)) + ((20 / 9) * (s ^ 4)) + ((22 / 9) * (s
      ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-20 / 9) * (s ^ 3)) + ((-1 / 3) * s) + ((1 / 9) * (s ^ 8)) + ((4 / 9) * (s ^ 7))
      + ((14 / 9) * (s ^ 6)) + ((16 / 9) * (s ^ 5)) + ((20 / 9) * (s ^ 4)) + ((22 / 9) * (s ^
      2))) = s ^ 1 * ((4275059213 / 41278242816) + (3247106047 / 9) * (s - (5 / 24)) ^ 1 * ((1 /
      4) - s) ^ 6 + (6489046609 / 3) * (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 5 + (48642445505 /
      9) * (s - (5 / 24)) ^ 3 * ((1 / 4) - s) ^ 4 + (64840967849 / 9) * (s - (5 / 24)) ^ 4 * ((1
      / 4) - s) ^ 3 + (16211016517 / 3) * (s - (5 / 24)) ^ 5 * ((1 / 4) - s) ^ 2 + (19459914853
      / 9) * (s - (5 / 24)) ^ 6 * ((1 / 4) - s) ^ 1 + (3245421427 / 9) * (s - (5 / 24)) ^ 7) :=
      by
    ring
  rw [heq]
  positivity

theorem polynomialPositive12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) < (s + ((-7 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-7 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4))) = s ^ 1 * ((15
      / 32) + (3322 / 3) * ((1 / 4) - s) ^ 3 + 2188 * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 2 +
      1080 * (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg31 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4)) + ((4 / 3) *
      (s ^ 3))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4)) + ((4 / 3) * (s ^
      3))) = ((476929 / 497664) + (136 / 3) * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 3 + 908 * (s
      - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 2 + (5176 / 3) * (s - (5 / 24)) ^ 3 * ((1 / 4) - s) ^ 1
      + (2590 / 3) * (s - (5 / 24)) ^ 4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg32 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (((-5 / 9) * (s ^ 2)) + ((1 / 3) * s) + ((2 / 9) * (s ^ 4)) + ((4 / 9) * (s
      ^ 5)) + ((4 / 9) * (s ^ 8)) + ((10 / 9) * (s ^ 3)) + ((16 / 9) * (s ^ 7)) + ((20 / 9) * (s ^
      6))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-5 / 9) * (s ^ 2)) + ((1 / 3) * s) + ((2 / 9) * (s ^ 4)) + ((4 / 9) * (s ^ 5)) +
      ((4 / 9) * (s ^ 8)) + ((10 / 9) * (s ^ 3)) + ((16 / 9) * (s ^ 7)) + ((20 / 9) * (s ^ 6)))
      = s ^ 1 * ((3245332751 / 12039487488) + (38200580 / 63) * ((1 / 4) - s) ^ 7 + 170520 * (s
      - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 5 + (68124424 / 3) * (s - (5 / 24)) ^ 3 * ((1 / 4) - s)
      ^ 4 + (203882728 / 3) * (s - (5 / 24)) ^ 4 * ((1 / 4) - s) ^ 3 + 82075400 * (s - (5 / 24))
      ^ 5 * ((1 / 4) - s) ^ 2 + (138010760 / 3) * (s - (5 / 24)) ^ 6 * ((1 / 4) - s) ^ 1 +
      (209114504 / 21) * (s - (5 / 24)) ^ 7) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg33 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (s + ((-4 / 3) * (s ^ 3)) + ((-1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-4 / 3) * (s ^ 3)) + ((-1 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 4))) = s ^ 1 *
      ((27 / 32) + (1450 / 3) * ((1 / 4) - s) ^ 3 + 988 * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 2
      + 504 * (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg34 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (((-32 / 9) * (s ^ 4)) + ((-16 / 9) * (s ^ 7)) + ((4 / 3) * (s ^ 3)) + ((4 /
      3) * (s ^ 6)) + ((4 / 9) * (s ^ 8)) + ((20 / 9) * (s ^ 5))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-32 / 9) * (s ^ 4)) + ((-16 / 9) * (s ^ 7)) + ((4 / 3) * (s ^ 3)) + ((4 / 3) *
      (s ^ 6)) + ((4 / 9) * (s ^ 8)) + ((20 / 9) * (s ^ 5))) = s ^ 3 * ((153 / 256) + (7185620 /
      9) * ((1 / 4) - s) ^ 5 + (9471656 / 3) * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 4 + 4681248
      * (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 3 + 3084480 * (s - (5 / 24)) ^ 3 * ((1 / 4) - s) ^
      2 + 762048 * (s - (5 / 24)) ^ 4 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) < (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4)) + ((8 / 3) * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 4)) + ((8 / 3) * (s ^ 2))) = s ^ 2 * ((15 /
      8) + (218 / 3) * ((1 / 4) - s) ^ 2 + 72 * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg35 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (s + ((-8 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 2)) + ((4 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (s + ((-8 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 2)) + ((4 / 3) * (s ^ 4))) = s ^ 1 *
      ((15 / 16) + (1172 / 3) * ((1 / 4) - s) ^ 3 + 824 * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 2
      + 432 * (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg36 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ ((8 * (s ^ 6)) + ((-64 / 9) * (s ^ 7)) + ((-56 / 9) * (s ^ 4)) + ((8 / 3) *
      (s ^ 3)) + ((8 / 9) * (s ^ 5)) + ((16 / 9) * (s ^ 8))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((8 * (s ^ 6)) + ((-64 / 9) * (s ^ 7)) + ((-56 / 9) * (s ^ 4)) + ((8 / 3) * (s ^
      3)) + ((8 / 9) * (s ^ 5)) + ((16 / 9) * (s ^ 8))) = s ^ 3 * ((81 / 64) + (14545232 / 9) *
      ((1 / 4) - s) ^ 5 + (19215008 / 3) * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 4 + 9516672 * (s
      - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 3 + 6283008 * (s - (5 / 24)) ^ 3 * ((1 / 4) - s) ^ 2 +
      1555200 * (s - (5 / 24)) ^ 4 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg37 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (1 + (-1 * s) + (3 * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (-1 * s) + (3 * (s ^ 2))) = ((59 / 64) + 6 * (s - (5 / 24)) ^ 1 * ((1 / 4) -
      s) ^ 1 + 9 * (s - (5 / 24)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg38 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) = s ^ 2 *
      ((301 / 864) + (20 / 3) * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 1 + (46 / 3) * (s - (5 /
      24)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) < (1 + ((-7 / 3) * s) + ((1 / 3) * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-7 / 3) * s) + ((1 / 3) * (s ^ 2))) = ((7 / 16) + (157 / 3) * ((1 / 4) - s) ^
      2 + 52 * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg39 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (1 + (-2 * (s ^ 3)) + (5 * (s ^ 2)) + ((-4 / 3) * s) + ((1 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (-2 * (s ^ 3)) + (5 * (s ^ 2)) + ((-4 / 3) * s) + ((1 / 3) * (s ^ 4))) =
      ((917473 / 995328) + (20804 / 3) * (s - (5 / 24)) ^ 1 * ((1 / 4) - s) ^ 3 + 23014 * (s -
      (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 2 + (75548 / 3) * (s - (5 / 24)) ^ 3 * ((1 / 4) - s) ^ 1 +
      (27311 / 3) * (s - (5 / 24)) ^ 4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg40 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    (0 : ℝ) ≤ (((-188 / 9) * (s ^ 5)) + ((-44 / 3) * (s ^ 3)) + ((-4 / 3) * (s ^ 7)) +
      ((-2 / 3) * s) + ((1 / 9) * (s ^ 8)) + ((22 / 3) * (s ^ 6)) + ((49 / 9) * (s ^ 2)) + ((92 / 3)
      * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-188 / 9) * (s ^ 5)) + ((-44 / 3) * (s ^ 3)) + ((-4 / 3) * (s ^ 7)) + ((-2 / 3)
      * s) + ((1 / 9) * (s ^ 8)) + ((22 / 3) * (s ^ 6)) + ((49 / 9) * (s ^ 2)) + ((92 / 3) * (s
      ^ 4))) = s ^ 1 * ((2961071501 / 41278242816) + (4535198719 / 9) * (s - (5 / 24)) ^ 1 * ((1
      / 4) - s) ^ 6 + (9062909137 / 3) * (s - (5 / 24)) ^ 2 * ((1 / 4) - s) ^ 5 + (67964054081 /
      9) * (s - (5 / 24)) ^ 3 * ((1 / 4) - s) ^ 4 + (90671164457 / 9) * (s - (5 / 24)) ^ 4 * ((1
      / 4) - s) ^ 3 + (22696164037 / 3) * (s - (5 / 24)) ^ 5 * ((1 / 4) - s) ^ 2 + (27287262181
      / 9) * (s - (5 / 24)) ^ 6 * ((1 / 4) - s) ^ 1 + (4559409139 / 9) * (s - (5 / 24)) ^ 7) :=
      by
    ring
  rw [heq]
  positivity

theorem polynomialPositive15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) < (((2 / 3) * (s ^ 2)) + ((4 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((2 / 3) * (s ^ 2)) + ((4 / 3) * s)) = s ^ 1 * ((3 / 2) + (2 / 3) * (s - (1 / 4)) ^
      1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg41 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)) = ((9 / 8) + 4 * (s - (1 / 4)) ^ 1 * ((1
      / 3) - s) ^ 1 + (10 / 3) * (s - (1 / 4)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg42 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s
      ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-8 / 9) * (s ^ 2)) + ((-8 / 9) * (s ^ 3)) + ((4 / 3) * s) + ((4 / 9) * (s ^ 4)))
      = s ^ 1 * ((232 / 243) + (1676 / 9) * ((1 / 3) - s) ^ 3 + (1136 / 3) * (s - (1 / 4)) ^ 1 *
      ((1 / 3) - s) ^ 2 + 192 * (s - (1 / 4)) ^ 2 * ((1 / 3) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg43 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + (2 * (s ^ 3))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (s ^ 2) + (-1 * s) + (2 * (s ^ 3))) = ((121 / 144) + 6 * ((1 / 3) - s) ^ 3 +
      12 * (s - (1 / 4)) ^ 2 * ((1 / 3) - s) ^ 1 + 20 * (s - (1 / 4)) ^ 3) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg44 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ ((4 * (s ^ 5)) + (4 * (s ^ 6)) + ((-10 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 2))
      + ((2 / 3) * (s ^ 3))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : ((4 * (s ^ 5)) + (4 * (s ^ 6)) + ((-10 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 2)) + ((2
      / 3) * (s ^ 3))) = s ^ 2 * ((45 / 64) + 168 * (s - (1 / 4)) ^ 2 * ((1 / 3) - s) ^ 2 + 432
      * (s - (1 / 4)) ^ 3 * ((1 / 3) - s) ^ 1 + 268 * (s - (1 / 4)) ^ 4) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) < (1 + ((-4 / 3) * s) + ((-1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 3)) + ((7 / 3) *
      (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-4 / 3) * s) + ((-1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 3)) + ((7 / 3) * (s ^
      2))) = ((213 / 256) + 108 * (s - (1 / 4)) ^ 1 * ((1 / 3) - s) ^ 3 + 786 * (s - (1 / 4)) ^ 2
      * ((1 / 3) - s) ^ 2 + 1260 * (s - (1 / 4)) ^ 3 * ((1 / 3) - s) ^ 1 + (1745 / 3) * (s - (1 /
      4)) ^ 4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg45 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (1 + ((-5 / 3) * s) + ((-2 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 3)) + ((11 / 3)
      * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-5 / 3) * s) + ((-2 / 3) * (s ^ 4)) + ((2 / 3) * (s ^ 3)) + ((11 / 3) * (s ^
      2))) = ((105 / 128) + 432 * (s - (1 / 4)) ^ 1 * ((1 / 3) - s) ^ 3 + 1860 * (s - (1 / 4)) ^
      2 * ((1 / 3) - s) ^ 2 + 2424 * (s - (1 / 4)) ^ 3 * ((1 / 3) - s) ^ 1 + (2986 / 3) * (s -
      (1 / 4)) ^ 4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg46 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (((-110 / 9) * (s ^ 3)) + ((-40 / 9) * (s ^ 6)) + ((-8 / 9) * (s ^ 7)) +
      ((-4 / 3) * s) + ((4 / 9) * (s ^ 8)) + ((64 / 9) * (s ^ 5)) + ((70 / 9) * (s ^ 2)) + ((86 / 9)
      * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-110 / 9) * (s ^ 3)) + ((-40 / 9) * (s ^ 6)) + ((-8 / 9) * (s ^ 7)) + ((-4 / 3)
      * s) + ((4 / 9) * (s ^ 8)) + ((64 / 9) * (s ^ 5)) + ((70 / 9) * (s ^ 2)) + ((86 / 9) * (s
      ^ 4))) = s ^ 1 * ((81 / 4096) + 11381148 * (s - (1 / 4)) ^ 1 * ((1 / 3) - s) ^ 6 +
      67508964 * (s - (1 / 4)) ^ 2 * ((1 / 3) - s) ^ 5 + 167111100 * (s - (1 / 4)) ^ 3 * ((1 /
      3) - s) ^ 4 + 220979388 * (s - (1 / 4)) ^ 4 * ((1 / 3) - s) ^ 3 + 164643236 * (s - (1 /
      4)) ^ 5 * ((1 / 3) - s) ^ 2 + (196604324 / 3) * (s - (1 / 4)) ^ 6 * ((1 / 3) - s) ^ 1 +
      (97988788 / 9) * (s - (1 / 4)) ^ 7) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg47 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (1 + (-1 * s) + (3 * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (-1 * s) + (3 * (s ^ 2))) = ((15 / 16) + 6 * (s - (1 / 4)) ^ 1 * ((1 / 3) - s)
      ^ 1 + 9 * (s - (1 / 4)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg48 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-10 / 3) * (s ^ 3)) + ((2 / 3) * (s ^ 2)) + ((26 / 3) * (s ^ 4))) = s ^ 2 * ((3
      / 8) + 12 * (s - (1 / 4)) ^ 1 * ((1 / 3) - s) ^ 1 + (62 / 3) * (s - (1 / 4)) ^ 2) := by
    ring
  rw [heq]
  positivity

theorem polynomialPositive17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) < (1 + ((-7 / 3) * s) + ((1 / 3) * (s ^ 2))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + ((-7 / 3) * s) + ((1 / 3) * (s ^ 2))) = ((7 / 27) + (77 / 3) * ((1 / 3) - s) ^ 2
      + (76 / 3) * (s - (1 / 4)) ^ 1 * ((1 / 3) - s) ^ 1) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg49 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (1 + (-2 * (s ^ 3)) + (5 * (s ^ 2)) + ((-4 / 3) * s) + ((1 / 3) * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (1 + (-2 * (s ^ 3)) + (5 * (s ^ 2)) + ((-4 / 3) * s) + ((1 / 3) * (s ^ 4))) = ((243
      / 256) + 1404 * (s - (1 / 4)) ^ 1 * ((1 / 3) - s) ^ 3 + 4734 * (s - (1 / 4)) ^ 2 * ((1 /
      3) - s) ^ 2 + 5236 * (s - (1 / 4)) ^ 3 * ((1 / 3) - s) ^ 1 + (5719 / 3) * (s - (1 / 4)) ^
      4) := by
    ring
  rw [heq]
  positivity

theorem polynomialNonneg50 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    (0 : ℝ) ≤ (((-188 / 9) * (s ^ 5)) + ((-44 / 3) * (s ^ 3)) + ((-4 / 3) * (s ^ 7)) +
      ((-2 / 3) * s) + ((1 / 9) * (s ^ 8)) + ((22 / 3) * (s ^ 6)) + ((49 / 9) * (s ^ 2)) + ((92 / 3)
      * (s ^ 4))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have heq : (((-188 / 9) * (s ^ 5)) + ((-44 / 3) * (s ^ 3)) + ((-4 / 3) * (s ^ 7)) + ((-2 / 3)
      * s) + ((1 / 9) * (s ^ 8)) + ((22 / 3) * (s ^ 6)) + ((49 / 9) * (s ^ 2)) + ((92 / 3) * (s
      ^ 4))) = s ^ 1 * ((2985 / 16384) + 8035767 * (s - (1 / 4)) ^ 1 * ((1 / 3) - s) ^ 6 +
      48605265 * (s - (1 / 4)) ^ 2 * ((1 / 3) - s) ^ 5 + 122779287 * (s - (1 / 4)) ^ 3 * ((1 /
      3) - s) ^ 4 + 165757527 * (s - (1 / 4)) ^ 4 * ((1 / 3) - s) ^ 3 + 126113793 * (s - (1 /
      4)) ^ 5 * ((1 / 3) - s) ^ 2 + (153781249 / 3) * (s - (1 / 4)) ^ 6 * ((1 / 3) - s) ^ 1 +
      (78249253 / 9) * (s - (1 / 4)) ^ 7) := by
    ring
  rw [heq]
  positivity

end ConwaySoifer.Simplified.BridgeLocalPolynomials
