/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.SupportFan
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! Explicit real support fans for the handwritten geometric point set.
The polynomial decompositions are proved by `ring`; their signs by `positivity`.
Each cone carries one fixed triple on both endpoints. No Boolean checker is used. -/

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

noncomputable section
namespace ConwaySoifer.Simplified

/-- The four-point configuration used by the adaptive central-core obstruction. -/
def adaptiveCoreLocalPoint (s : ℝ) : Fin 4 → Point :=
  ![(1, 0), (1, (-1 * s)), ((((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)), (((-1 / 3) * (s ^ 2)) + ((1 / 3)
      * s))), ((1 + (-1 * s)), s)]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)) := by
    have heq : (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)) = s ^ 1 * ((2 / 3) + (1 / 3) * (s - 0) ^ 1) :=
        by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = (1 + (4 / 3) * (s - 0) ^ 1 * ((1 / 4) -
          s) ^ 1 + 2 * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((2 / 3) + (208 / 9) * (s - 0) ^ 1 * ((1 / 4) - s) ^ 2 + 48 * (s - 0) ^ 2 * ((1
          / 4) - s) ^ 1 + (76 / 3) * (s - 0) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq (1, 0) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) := by
      have heq : (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((207 /
          256) + 49 * ((1 / 4) - s) ^ 4 + 132 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 3 + 118 * (s - 0) ^ 2
          * ((1 / 4) - s) ^ 2 + (104 / 3) * (s - 0) ^ 3 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) := by
      have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1
          / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = s ^ 2 * ((1121 / 4096) +
          (4829 / 3) * ((1 / 4) - s) ^ 6 + 7610 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 5 + 14417 * (s - 0)
          ^ 2 * ((1 / 4) - s) ^ 4 + 13676 * (s - 0) ^ 3 * ((1 / 4) - s) ^ 3 + (58441 / 9) * (s - 0)
          ^ 4 * ((1 / 4) - s) ^ 2 + 1234 * (s - 0) ^ 5 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1 /
        9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = (supportNum ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) (adaptiveCoreLocalPoint s
        3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + (-3 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((7 / 3) * (s ^
      2))) := by
    have heq : (1 + (-3 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((7 / 3) * (s ^ 2))) =
        ((95 / 256) + 161 * ((1 / 4) - s) ^ 4 + 452 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 3 + (1282 / 3) *
        (s - 0) ^ 2 * ((1 / 4) - s) ^ 2 + 136 * (s - 0) ^ 3 * ((1 / 4) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) := by
      have heq : (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((207 /
          256) + 49 * ((1 / 4) - s) ^ 4 + 132 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 3 + 118 * (s - 0) ^ 2
          * ((1 / 4) - s) ^ 2 + (104 / 3) * (s - 0) ^ 3 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) := by
      have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1
          / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = s ^ 2 * ((1121 / 4096) +
          (4829 / 3) * ((1 / 4) - s) ^ 6 + 7610 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 5 + 14417 * (s - 0)
          ^ 2 * ((1 / 4) - s) ^ 4 + 13676 * (s - 0) ^ 3 * ((1 / 4) - s) ^ 3 + (58441 / 9) * (s - 0)
          ^ 4 * ((1 / 4) - s) ^ 2 + 1234 * (s - 0) ^ 5 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1 /
        9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = (supportNum ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) (adaptiveCoreLocalPoint s
        2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2)))
      := by
      have heq : (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2))) = ((215
          / 256) + 41 * ((1 / 4) - s) ^ 4 + 100 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 3 + (242 / 3) * (s -
          0) ^ 2 * ((1 / 4) - s) ^ 2 + (64 / 3) * (s - 0) ^ 3 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) +
      ((1 / 9) * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) := by
      have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9)
          * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = s ^ 2 * ((1425 / 4096) + 2671
          * ((1 / 4) - s) ^ 6 + (36814 / 3) * (s - 0) ^ 1 * ((1 / 4) - s) ^ 5 + (203401 / 9) * (s -
          0) ^ 2 * ((1 / 4) - s) ^ 4 + (187660 / 9) * (s - 0) ^ 3 * ((1 / 4) - s) ^ 3 + (86713 / 9)
          * (s - 0) ^ 4 * ((1 / 4) - s) ^ 2 + (5350 / 3) * (s - 0) ^ 5 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9) *
        (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2))
        + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + (-2 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((10 / 3) * (s ^
      2))) := by
    have heq : (1 + (-2 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((10 / 3) * (s ^ 2))) =
        ((175 / 256) + 81 * ((1 / 4) - s) ^ 4 + 196 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 3 + (466 / 3) *
        (s - 0) ^ 2 * ((1 / 4) - s) ^ 2 + 40 * (s - 0) ^ 3 * ((1 / 4) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2)))
      := by
      have heq : (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2))) = ((215
          / 256) + 41 * ((1 / 4) - s) ^ 4 + 100 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 3 + (242 / 3) * (s -
          0) ^ 2 * ((1 / 4) - s) ^ 2 + (64 / 3) * (s - 0) ^ 3 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) +
      ((1 / 9) * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) := by
      have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9)
          * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = s ^ 2 * ((1425 / 4096) + 2671
          * ((1 / 4) - s) ^ 6 + (36814 / 3) * (s - 0) ^ 1 * ((1 / 4) - s) ^ 5 + (203401 / 9) * (s -
          0) ^ 2 * ((1 / 4) - s) ^ 4 + (187660 / 9) * (s - 0) ^ 3 * ((1 / 4) - s) ^ 3 + (86713 / 9)
          * (s - 0) ^ 4 * ((1 / 4) - s) ^ 2 + (5350 / 3) * (s - 0) ^ 5 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9) *
        (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2))
        + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (3 * (s ^ 2)) + ((-4 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)))
      := by
      have heq : (1 + (-1 * s) + (3 * (s ^ 2)) + ((-4 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((173
          / 192) + (76 / 3) * ((1 / 4) - s) ^ 4 + (112 / 3) * (s - 0) ^ 1 * ((1 / 4) - s) ^ 3 + 8 *
          (s - 0) ^ 2 * ((1 / 4) - s) ^ 2 + (13 / 3) * (s - 0) ^ 4) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) := by
      have heq : ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^ 7)) +
          ((1 / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) = s ^ 2 * ((10425 /
          4096) + (13781 / 3) * ((1 / 4) - s) ^ 6 + 20394 * (s - 0) ^ 1 * ((1 / 4) - s) ^ 5 + 36137
          * (s - 0) ^ 2 * ((1 / 4) - s) ^ 4 + (95780 / 3) * (s - 0) ^ 3 * ((1 / 4) - s) ^ 3 +
          (126481 / 9) * (s - 0) ^ 4 * ((1 / 4) - s) ^ 2 + (7390 / 3) * (s - 0) ^ 5 * ((1 / 4) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^ 7)) + ((1
        / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) = (supportNum ((-1 + ((-2 /
        3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2))))
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2
        - normSq ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)) := by
    have heq : (((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)) = s ^ 1 * ((5 / 4) + (1 / 3) * ((1 / 4) - s) ^
        1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-2 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 2))) := by
      have heq : (1 + ((-2 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 2))) = (1 + (64 /
          3) * (s - 0) ^ 2 * ((1 / 4) - s) ^ 2 + 40 * (s - 0) ^ 3 * ((1 / 4) - s) ^ 1 + 19 * (s - 0)
          ^ 4) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^
      2)) + ((1 / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4)))
      := by
      have heq : ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^ 2)) +
          ((1 / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4))) =
          s ^ 1 * ((30825 / 16384) + 1943 * ((1 / 4) - s) ^ 7 + (32611 / 3) * (s - 0) ^ 1 * ((1 / 4)
          - s) ^ 6 + (74281 / 3) * (s - 0) ^ 2 * ((1 / 4) - s) ^ 5 + (263629 / 9) * (s - 0) ^ 3 *
          ((1 / 4) - s) ^ 4 + 18853 * (s - 0) ^ 4 * ((1 / 4) - s) ^ 3 + 6179 * (s - 0) ^ 5 * ((1 /
          4) - s) ^ 2 + 785 * (s - 0) ^ 6 * ((1 / 4) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^ 2)) + ((1
        / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4))) =
        (supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) *
        (s ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint
        s 3)) ^ 2 - normSq ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 /
        3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = (1 + (4 / 3) * (s - 0) ^ 1 * ((1 / 4) -
          s) ^ 1 + 2 * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((2 / 3) + (208 / 9) * (s - 0) ^ 1 * ((1 / 4) - s) ^ 2 + 48 * (s - 0) ^ 2 * ((1
          / 4) - s) ^ 1 + (76 / 3) * (s - 0) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3)) ^ 2 - normSq (-1, 1) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)) := by
    have heq : (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)) = s ^ 1 * ((3 / 4) + (1 / 3) * (s - (1 / 4)) ^
        1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = ((9 / 8) + (16 / 3) * (s - (1 / 4)) ^ 1
          * ((3 / 8) - s) ^ 1 + 6 * (s - (1 / 4)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((17 / 16) + 112 * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 2 + (2072 / 9) * (s - (1
          / 4)) ^ 2 * ((3 / 8) - s) ^ 1 + (356 / 3) * (s - (1 / 4)) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq (1, 0) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) := by
      have heq : (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((3091 /
          4096) + 221 * ((3 / 8) - s) ^ 4 + (1820 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 3 + 550
          * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 2 + 164 * (s - (1 / 4)) ^ 3 * ((3 / 8) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) := by
      have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1
          / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = s ^ 2 * ((111395 / 786432)
          + (103837 / 3) * ((3 / 8) - s) ^ 6 + 168186 * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 5 +
          (2942281 / 9) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 4 + (953188 / 3) * (s - (1 / 4)) ^ 3 *
          ((3 / 8) - s) ^ 3 + 154381 * (s - (1 / 4)) ^ 4 * ((3 / 8) - s) ^ 2 + 29998 * (s - (1 / 4))
          ^ 5 * ((3 / 8) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1 /
        9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = (supportNum ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) (adaptiveCoreLocalPoint s
        3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + (-3 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((7 / 3) * (s ^
      2))) := by
    have heq : (1 + (-3 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((7 / 3) * (s ^ 2))) =
        ((499 / 4096) + 1021 * ((3 / 8) - s) ^ 4 + 2996 * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 3 +
        (8818 / 3) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 2 + 964 * (s - (1 / 4)) ^ 3 * ((3 / 8) - s)
        ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) := by
      have heq : (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((3091 /
          4096) + 221 * ((3 / 8) - s) ^ 4 + (1820 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 3 + 550
          * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 2 + 164 * (s - (1 / 4)) ^ 3 * ((3 / 8) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) := by
      have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1
          / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = s ^ 2 * ((111395 / 786432)
          + (103837 / 3) * ((3 / 8) - s) ^ 6 + 168186 * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 5 +
          (2942281 / 9) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 4 + (953188 / 3) * (s - (1 / 4)) ^ 3 *
          ((3 / 8) - s) ^ 3 + 154381 * (s - (1 / 4)) ^ 4 * ((3 / 8) - s) ^ 2 + 29998 * (s - (1 / 4))
          ^ 5 * ((3 / 8) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1 /
        9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = (supportNum ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) (adaptiveCoreLocalPoint s
        2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2)))
      := by
      have heq : (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2))) =
          ((3331 / 4096) + 109 * ((3 / 8) - s) ^ 4 + (796 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^
          3 + (626 / 3) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 2 + 52 * (s - (1 / 4)) ^ 3 * ((3 / 8)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) +
      ((1 / 9) * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) := by
      have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9)
          * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = s ^ 2 * ((44545 / 262144) +
          46655 * ((3 / 8) - s) ^ 6 + (668590 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 5 +
          (3833833 / 9) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 4 + (3665068 / 9) * (s - (1 / 4)) ^ 3
          * ((3 / 8) - s) ^ 3 + (1752277 / 9) * (s - (1 / 4)) ^ 4 * ((3 / 8) - s) ^ 2 + (111722 / 3)
          * (s - (1 / 4)) ^ 5 * ((3 / 8) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9) *
        (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2))
        + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + (-2 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((10 / 3) * (s ^
      2))) := by
    have heq : (1 + (-2 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((10 / 3) * (s ^ 2))) =
        ((2611 / 4096) + 189 * ((3 / 8) - s) ^ 4 + 436 * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 3 +
        (946 / 3) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 2 + 68 * (s - (1 / 4)) ^ 3 * ((3 / 8) - s) ^
        1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound19 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2)))
      := by
      have heq : (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2))) =
          ((3331 / 4096) + 109 * ((3 / 8) - s) ^ 4 + (796 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^
          3 + (626 / 3) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 2 + 52 * (s - (1 / 4)) ^ 3 * ((3 / 8)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) +
      ((1 / 9) * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) := by
      have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9)
          * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = s ^ 2 * ((44545 / 262144) +
          46655 * ((3 / 8) - s) ^ 6 + (668590 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 5 +
          (3833833 / 9) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 4 + (3665068 / 9) * (s - (1 / 4)) ^ 3
          * ((3 / 8) - s) ^ 3 + (1752277 / 9) * (s - (1 / 4)) ^ 4 * ((3 / 8) - s) ^ 2 + (111722 / 3)
          * (s - (1 / 4)) ^ 5 * ((3 / 8) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9) *
        (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2))
        + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (3 * (s ^ 2)) + ((-4 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)))
      := by
      have heq : (1 + (-1 * s) + (3 * (s ^ 2)) + ((-4 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((235
          / 256) + (416 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 3 + 552 * (s - (1 / 4)) ^ 2 * ((3
          / 8) - s) ^ 2 + 680 * (s - (1 / 4)) ^ 3 * ((3 / 8) - s) ^ 1 + 267 * (s - (1 / 4)) ^ 4) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) := by
      have heq : ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^ 7)) +
          ((1 / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) = s ^ 2 * ((1840691 /
          786432) + (160909 / 3) * ((3 / 8) - s) ^ 6 + (728974 / 3) * (s - (1 / 4)) ^ 1 * ((3 / 8) -
          s) ^ 5 + (3943801 / 9) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 4 + 392844 * (s - (1 / 4)) ^
          3 * ((3 / 8) - s) ^ 3 + 174877 * (s - (1 / 4)) ^ 4 * ((3 / 8) - s) ^ 2 + 30878 * (s - (1 /
          4)) ^ 5 * ((3 / 8) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^ 7)) + ((1
        / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) = (supportNum ((-1 + ((-2 /
        3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2))))
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2
        - normSq ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound21 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)) := by
    have heq : (((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)) = s ^ 1 * ((29 / 24) + (1 / 3) * ((3 / 8) - s)
        ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound22 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-2 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 2))) := by
      have heq : (1 + ((-2 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 2))) = ((275 /
          256) + 288 * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 3 + (2776 / 3) * (s - (1 / 4)) ^ 2 * ((3
          / 8) - s) ^ 2 + 984 * (s - (1 / 4)) ^ 3 * ((3 / 8) - s) ^ 1 + 347 * (s - (1 / 4)) ^ 4) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^
      2)) + ((1 / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4)))
      := by
      have heq : ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^ 2)) +
          ((1 / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4))) =
          s ^ 1 * ((30955079 / 16515072) + (932168 / 63) * ((3 / 8) - s) ^ 7 + (480008 / 9) * (s -
          (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 6 + (168872 / 3) * (s - (1 / 4)) ^ 2 * ((3 / 8) - s) ^ 5 +
          (32248 / 9) * (s - (1 / 4)) ^ 3 * ((3 / 8) - s) ^ 4 + (156508 / 3) * (s - (1 / 4)) ^ 5 *
          ((3 / 8) - s) ^ 2 + (482822 / 9) * (s - (1 / 4)) ^ 6 * ((3 / 8) - s) ^ 1 + (985781 / 63) *
          (s - (1 / 4)) ^ 7) := by
        ring
      rw [heq]
      positivity
    have heq : ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^ 2)) + ((1
        / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4))) =
        (supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) *
        (s ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint
        s 3)) ^ 2 - normSq ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 /
        3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound23 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = ((9 / 8) + (16 / 3) * (s - (1 / 4)) ^ 1
          * ((3 / 8) - s) ^ 1 + 6 * (s - (1 / 4)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((17 / 16) + 112 * (s - (1 / 4)) ^ 1 * ((3 / 8) - s) ^ 2 + (2072 / 9) * (s - (1
          / 4)) ^ 2 * ((3 / 8) - s) ^ 1 + (356 / 3) * (s - (1 / 4)) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3)) ^ 2 - normSq (-1, 1) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound24 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)) := by
    have heq : (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)) = s ^ 1 * ((19 / 24) + (1 / 3) * (s - (3 / 8))
        ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound25 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = ((39 / 32) + (40 / 3) * (s - (3 / 8)) ^
          1 * ((7 / 16) - s) ^ 1 + 14 * (s - (3 / 8)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((497 / 384) + (4528 / 9) * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 2 + (3064 / 3)
          * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 1 + (1556 / 3) * (s - (3 / 8)) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq (1, 0) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound26 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) := by
      have heq : (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((48379 /
          65536) + 1077 * ((7 / 16) - s) ^ 4 + 2996 * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 3 + 2758
          * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 2 + (2516 / 3) * (s - (3 / 8)) ^ 3 * ((7 / 16) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) := by
      have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1
          / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = s ^ 2 * ((1485417 /
          16777216) + (2673029 / 3) * ((7 / 16) - s) ^ 6 + 4386122 * (s - (3 / 8)) ^ 1 * ((7 / 16) -
          s) ^ 5 + 8635721 * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 4 + (25501124 / 3) * (s - (3 / 8))
          ^ 3 * ((7 / 16) - s) ^ 3 + (37647229 / 9) * (s - (3 / 8)) ^ 4 * ((7 / 16) - s) ^ 2 +
          (2469778 / 3) * (s - (3 / 8)) ^ 5 * ((7 / 16) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1 /
        9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = (supportNum ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) (adaptiveCoreLocalPoint s
        3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound27 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + (-3 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((7 / 3) * (s ^
      2))) := by
    have heq : (1 + (-3 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((7 / 3) * (s ^ 2))) =
        ((443 / 65536) + 7541 * ((7 / 16) - s) ^ 4 + 22452 * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 3
        + (66898 / 3) * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 2 + 7388 * (s - (3 / 8)) ^ 3 * ((7 /
        16) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound28 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) := by
      have heq : (1 + (s ^ 2) + (-1 * s) + ((-1 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) = ((48379 /
          65536) + 1077 * ((7 / 16) - s) ^ 4 + 2996 * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 3 + 2758
          * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 2 + (2516 / 3) * (s - (3 / 8)) ^ 3 * ((7 / 16) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) := by
      have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1
          / 9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = s ^ 2 * ((1485417 /
          16777216) + (2673029 / 3) * ((7 / 16) - s) ^ 6 + 4386122 * (s - (3 / 8)) ^ 1 * ((7 / 16) -
          s) ^ 5 + 8635721 * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 4 + (25501124 / 3) * (s - (3 / 8))
          ^ 3 * ((7 / 16) - s) ^ 3 + (37647229 / 9) * (s - (3 / 8)) ^ 4 * ((7 / 16) - s) ^ 2 +
          (2469778 / 3) * (s - (3 / 8)) ^ 5 * ((7 / 16) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-2 * (s ^ 3)) + (2 * (s ^ 4)) + ((-4 / 3) * (s ^ 5)) + ((-2 / 9) * (s ^ 7)) + ((1 /
        9) * (s ^ 8)) + ((2 / 3) * (s ^ 2)) + ((7 / 9) * (s ^ 6))) = (supportNum ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) (adaptiveCoreLocalPoint s
        2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((1 + ((-4 / 3) *
        s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound29 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2)))
      := by
      have heq : (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2))) =
          ((53083 / 65536) + 213 * ((7 / 16) - s) ^ 4 + 436 * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 3
          + (722 / 3) * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 2 + (52 / 3) * (s - (3 / 8)) ^ 3 * ((7
          / 16) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) +
      ((1 / 9) * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) := by
      have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9)
          * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = s ^ 2 * ((1788585 / 16777216)
          + 1062295 * ((7 / 16) - s) ^ 6 + (15546206 / 3) * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 5 +
          (91006417 / 9) * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 4 + (88791628 / 9) * (s - (3 / 8)) ^
          3 * ((7 / 16) - s) ^ 3 + (43315261 / 9) * (s - (3 / 8)) ^ 4 * ((7 / 16) - s) ^ 2 +
          (2817362 / 3) * (s - (3 / 8)) ^ 5 * ((7 / 16) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9) *
        (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2))
        + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound30 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + (-2 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((10 / 3) * (s ^
      2))) := by
    have heq : (1 + (-2 * s) + ((-5 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((10 / 3) * (s ^ 2))) =
        ((93551 / 147456) + (1780 / 9) * ((7 / 16) - s) ^ 4 + (2224 / 9) * (s - (3 / 8)) ^ 1 * ((7 /
        16) - s) ^ 3 + (280 / 9) * (s - (3 / 8)) ^ 3 * ((7 / 16) - s) ^ 1 + (727 / 9) * (s - (3 /
        8)) ^ 4) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound31 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2)))
      := by
      have heq : (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2))) =
          ((53083 / 65536) + 213 * ((7 / 16) - s) ^ 4 + 436 * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 3
          + (722 / 3) * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 2 + (52 / 3) * (s - (3 / 8)) ^ 3 * ((7
          / 16) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) +
      ((1 / 9) * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) := by
      have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9)
          * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = s ^ 2 * ((1788585 / 16777216)
          + 1062295 * ((7 / 16) - s) ^ 6 + (15546206 / 3) * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 5 +
          (91006417 / 9) * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 4 + (88791628 / 9) * (s - (3 / 8)) ^
          3 * ((7 / 16) - s) ^ 3 + (43315261 / 9) * (s - (3 / 8)) ^ 4 * ((7 / 16) - s) ^ 2 +
          (2817362 / 3) * (s - (3 / 8)) ^ 5 * ((7 / 16) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9) *
        (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2))
        + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound32 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (3 * (s ^ 2)) + ((-4 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)))
      := by
      have heq : (1 + (-1 * s) + (3 * (s ^ 2)) + ((-4 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4))) =
          ((4027 / 4096) + 3104 * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 3 + 9768 * (s - (3 / 8)) ^ 2
          * ((7 / 16) - s) ^ 2 + (30632 / 3) * (s - (3 / 8)) ^ 3 * ((7 / 16) - s) ^ 1 + 3547 * (s -
          (3 / 8)) ^ 4) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^
      7)) + ((1 / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) := by
      have heq : ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^ 7)) +
          ((1 / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) = s ^ 2 * ((38591433 /
          16777216) + (2029925 / 3) * ((7 / 16) - s) ^ 6 + 3071754 * (s - (3 / 8)) ^ 1 * ((7 / 16) -
          s) ^ 5 + 5536937 * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 4 + (14838340 / 3) * (s - (3 / 8))
          ^ 3 * ((7 / 16) - s) ^ 3 + (19667101 / 9) * (s - (3 / 8)) ^ 4 * ((7 / 16) - s) ^ 2 +
          (1142834 / 3) * (s - (3 / 8)) ^ 5 * ((7 / 16) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((-7 * (s ^ 3)) + (12 * (s ^ 4)) + ((-26 / 3) * (s ^ 5)) + ((-8 / 9) * (s ^ 7)) + ((1
        / 9) * (s ^ 8)) + ((11 / 3) * (s ^ 2)) + ((34 / 9) * (s ^ 6))) = (supportNum ((-1 + ((-2 /
        3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2))))
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2
        - normSq ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound33 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)) := by
    have heq : (((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)) = s ^ 1 * ((19 / 16) + (1 / 3) * ((7 / 16) -
        s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound34 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-2 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 2))) := by
      have heq : (1 + ((-2 / 3) * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((4 / 3) * (s ^ 2))) = ((4747 /
          4096) + 3232 * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 3 + (29752 / 3) * (s - (3 / 8)) ^ 2 *
          ((7 / 16) - s) ^ 2 + 10136 * (s - (3 / 8)) ^ 3 * ((7 / 16) - s) ^ 1 + 3451 * (s - (3 / 8))
          ^ 4) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^
      2)) + ((1 / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4)))
      := by
      have heq : ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^ 2)) +
          ((1 / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4))) =
          s ^ 1 * ((3946451 / 2097152) + (10729792 / 3) * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 6 +
          (70031392 / 3) * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 5 + (568177360 / 9) * (s - (3 / 8))
          ^ 3 * ((7 / 16) - s) ^ 4 + (271851608 / 3) * (s - (3 / 8)) ^ 4 * ((7 / 16) - s) ^ 3 +
          72855884 * (s - (3 / 8)) ^ 5 * ((7 / 16) - s) ^ 2 + 31124026 * (s - (3 / 8)) ^ 6 * ((7 /
          16) - s) ^ 1 + 5521727 * (s - (3 / 8)) ^ 7) := by
        ring
      rw [heq]
      positivity
    have heq : ((2 * s) + ((-16 / 9) * (s ^ 5)) + ((-4 / 9) * (s ^ 7)) + ((-2 / 3) * (s ^ 2)) + ((1
        / 3) * (s ^ 3)) + ((1 / 9) * (s ^ 8)) + ((4 / 3) * (s ^ 6)) + ((19 / 9) * (s ^ 4))) =
        (supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) *
        (s ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint
        s 3)) ^ 2 - normSq ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 /
        3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound35 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = ((39 / 32) + (40 / 3) * (s - (3 / 8)) ^
          1 * ((7 / 16) - s) ^ 1 + 14 * (s - (3 / 8)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((497 / 384) + (4528 / 9) * (s - (3 / 8)) ^ 1 * ((7 / 16) - s) ^ 2 + (3064 / 3)
          * (s - (3 / 8)) ^ 2 * ((7 / 16) - s) ^ 1 + (1556 / 3) * (s - (3 / 8)) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3)) ^ 2 - normSq (-1, 1) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound36 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    0 < cross (1, 0) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
    have heq : (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))) = ((1 / 3) + (50 / 3) * ((1 / 2) - s) ^ 2
        + 16 * (s - (7 / 16)) ^ 1 * ((1 / 2) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound37 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = ((163 / 128) + (44 / 3) * (s - (7 /
          16)) ^ 1 * ((1 / 2) - s) ^ 1 + (46 / 3) * (s - (7 / 16)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((1455 / 1024) + (1604 / 3) * (s - (7 / 16)) ^ 1 * ((1 / 2) - s) ^ 2 + (9772 /
          9) * (s - (7 / 16)) ^ 2 * ((1 / 2) - s) ^ 1 + (4964 / 9) * (s - (7 / 16)) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq (1, 0) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound38 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((2 * s) + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 3))) := by
      have heq : ((2 * s) + ((-2 / 3) * (s ^ 2)) + ((2 / 3) * (s ^ 3))) = s ^ 1 * ((11 / 6) + (2 /
          3) * ((1 / 2) - s) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (-1 + (-1 * (s ^ 3)) + (2 * s) + ((-8 / 9) * (s ^ 5)) + ((2 / 3) * (s ^ 2))
      + ((4 / 9) * (s ^ 6)) + ((25 / 9) * (s ^ 4))) := by
      have heq : (-1 + (-1 * (s ^ 3)) + (2 * s) + ((-8 / 9) * (s ^ 5)) + ((2 / 3) * (s ^ 2)) + ((4 /
          9) * (s ^ 6)) + ((25 / 9) * (s ^ 4))) = ((39849 / 4194304) + (8869304 / 3) * (s - (7 /
          16)) ^ 1 * ((1 / 2) - s) ^ 5 + (134245252 / 9) * (s - (7 / 16)) ^ 2 * ((1 / 2) - s) ^ 4 +
          (271008944 / 9) * (s - (7 / 16)) ^ 3 * ((1 / 2) - s) ^ 3 + (91213100 / 3) * (s - (7 / 16))
          ^ 4 * ((1 / 2) - s) ^ 2 + (138193256 / 9) * (s - (7 / 16)) ^ 5 * ((1 / 2) - s) ^ 1 +
          (27925564 / 9) * (s - (7 / 16)) ^ 6) := by
        ring
      rw [heq]
      positivity
    have heq : (-1 + (-1 * (s ^ 3)) + (2 * s) + ((-8 / 9) * (s ^ 5)) + ((2 / 3) * (s ^ 2)) + ((4 /
        9) * (s ^ 6)) + ((25 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)),
        (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 3)
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound39 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 * s), (2 * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (s + (s ^ 2)) := by
    have heq : (s + (s ^ 2)) = s ^ 1 * ((23 / 16) + 1 * (s - (7 / 16)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound40 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2)))
      := by
      have heq : (1 + (-1 * s) + (-1 * (s ^ 3)) + ((1 / 3) * (s ^ 4)) + ((5 / 3) * (s ^ 2))) =
          ((39809 / 49152) + (13 / 3) * ((1 / 2) - s) ^ 4 + (488 / 3) * (s - (7 / 16)) ^ 2 * ((1 /
          2) - s) ^ 2 + 336 * (s - (7 / 16)) ^ 3 * ((1 / 2) - s) ^ 1 + (508 / 3) * (s - (7 / 16)) ^
          4) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) +
      ((1 / 9) * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) := by
      have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9)
          * (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = s ^ 2 * ((11 / 192) + (2482171
          / 3) * ((1 / 2) - s) ^ 6 + (12075664 / 3) * (s - (7 / 16)) ^ 1 * ((1 / 2) - s) ^ 5 +
          (70492096 / 9) * (s - (7 / 16)) ^ 2 * ((1 / 2) - s) ^ 4 + (68577280 / 9) * (s - (7 / 16))
          ^ 3 * ((1 / 2) - s) ^ 3 + (33353728 / 9) * (s - (7 / 16)) ^ 4 * ((1 / 2) - s) ^ 2 + 720896
          * (s - (7 / 16)) ^ 5 * ((1 / 2) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (-4 * (s ^ 5)) + ((-11 / 3) * (s ^ 3)) + ((-2 / 3) * (s ^ 7)) + ((1 / 9) *
        (s ^ 8)) + ((19 / 9) * (s ^ 6)) + ((46 / 9) * (s ^ 4))) = (supportNum ((((-1 / 3) * (s ^ 2))
        + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2 - normSq ((((-1 / 3) * (s ^
        2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound41 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((-1 * s), (2 * s)) ≤ supportNum ((-1 * s), (2 * s)) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((s ^ 3) + (2 * s)) := by
      have heq : ((s ^ 3) + (2 * s)) = s ^ 1 * ((561 / 256) + 14 * (s - (7 / 16)) ^ 1 * ((1 / 2) -
          s) ^ 1 + 15 * (s - (7 / 16)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (s ^ 6) + (4 * (s ^ 4))) := by
      have heq : ((s ^ 2) + (s ^ 6) + (4 * (s ^ 4))) = s ^ 2 * ((118113 / 65536) + 15708 * (s - (7 /
          16)) ^ 1 * ((1 / 2) - s) ^ 3 + 48442 * (s - (7 / 16)) ^ 2 * ((1 / 2) - s) ^ 2 + 49788 * (s
          - (7 / 16)) ^ 3 * ((1 / 2) - s) ^ 1 + 17055 * (s - (7 / 16)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (s ^ 6) + (4 * (s ^ 4))) = (supportNum ((-1 * s), (2 * s))
        (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)) ^ 2
        - normSq ((-1 * s), (2 * s)) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound42 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    0 < cross ((-1 * s), (2 * s)) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < s := by
    have heq : s = s ^ 1 * (1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound43 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((-1 * s), (2 * s)) ≤ supportNum ((-1 * s), (2 * s)) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (s ^ 3) + (2 * s)) := by
      have heq : ((s ^ 2) + (s ^ 3) + (2 * s)) = s ^ 1 * ((673 / 256) + 30 * (s - (7 / 16)) ^ 1 *
          ((1 / 2) - s) ^ 1 + 31 * (s - (7 / 16)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((s ^ 2) + (s ^ 6) + (2 * (s ^ 5)) + (4 * (s ^ 3)) + (5 * (s ^ 4))) := by
      have heq : ((s ^ 2) + (s ^ 6) + (2 * (s ^ 5)) + (4 * (s ^ 3)) + (5 * (s ^ 4))) = s ^ 2 *
          ((256321 / 65536) + 40380 * (s - (7 / 16)) ^ 1 * ((1 / 2) - s) ^ 3 + 123386 * (s - (7 /
          16)) ^ 2 * ((1 / 2) - s) ^ 2 + 125692 * (s - (7 / 16)) ^ 3 * ((1 / 2) - s) ^ 1 + 42687 *
          (s - (7 / 16)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((s ^ 2) + (s ^ 6) + (2 * (s ^ 5)) + (4 * (s ^ 3)) + (5 * (s ^ 4))) = (supportNum
        ((-1 * s), (2 * s)) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3)) ^ 2 - normSq ((-1 * s), (2 * s)) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound44 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) := by
      have heq : (1 + ((1 / 3) * s) + ((2 / 3) * (s ^ 2))) = ((163 / 128) + (44 / 3) * (s - (7 /
          16)) ^ 1 * ((1 / 2) - s) ^ 1 + (46 / 3) * (s - (7 / 16)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [adaptiveCoreLocalPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s
      ^ 2))) := by
      have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2)))
          = s ^ 1 * ((1455 / 1024) + (1604 / 3) * (s - (7 / 16)) ^ 1 * ((1 / 2) - s) ^ 2 + (9772 /
          9) * (s - (7 / 16)) ^ 2 * ((1 / 2) - s) ^ 1 + (4964 / 9) * (s - (7 / 16)) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((2 / 3) * s) + ((4 / 9) * (s ^ 3)) + ((4 / 9) * (s ^ 4)) + ((13 / 9) * (s ^ 2))) =
        (supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3)) ^ 2 - normSq (-1, 1) := by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem adaptiveCoreLocal_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 2)) (hq : 0 < Q.side)
    (hpts : ∀ i, adaptiveCoreLocalPoint s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 4)
  · have hl : 0 ≤ s - 0 := by
      linarith
    have hh : 0 ≤ (1 / 4) - s := by
      linarith
    have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2))
        + ((2 / 3) * s))) :=
      ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
          adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
    have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 /
        3) * s))) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 2, hpts 2,
          adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
    have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
    have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
    have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
    have hc2 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) *
        (s ^ 2)))) ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
          adaptiveCoreLocalPoint s 0, hpts 0, hb2_0, hb2_1⟩
    have hd3 := arithmeticBound9 ⟨hs0, hl, hh⟩
    have hb3_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
    have hb3_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
    have hc3 : ConeBound Q ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 /
        3) * (s ^ 2)))) (-1, 1) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
          adaptiveCoreLocalPoint s 3, hpts 3, hb3_0, hb3_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
          adaptiveCoreLocalPoint s 3, hpts 3, hb3_1⟩
    apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s
        ^ 2)) + ((2 / 3) * s))), ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2
        / 3) * (s ^ 2)))), ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 /
        3) * (s ^ 2)))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, by norm_num [rot, eastDir], hend⟩
  · by_cases hsplit : s ≤ (3 / 8)
    · have hl : 0 ≤ s - (1 / 4) := by
        linarith
      have hh : 0 ≤ (3 / 8) - s := by
        linarith
      have hd0 := arithmeticBound12 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^
          2)) + ((2 / 3) * s))) :=
        ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
            adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
      have hd1 := arithmeticBound15 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound16 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound17 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2
          / 3) * s))) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
          2)))) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 2, hpts 2,
            adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
      have hd2 := arithmeticBound18 ⟨hs0, hl, hh⟩
      have hb2_0 := arithmeticBound19 ⟨hs0, hl, hh⟩
      have hb2_1 := arithmeticBound20 ⟨hs0, hl, hh⟩
      have hc2 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3)
          * (s ^ 2)))) ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3)
          * (s ^ 2)))) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
            adaptiveCoreLocalPoint s 0, hpts 0, hb2_0, hb2_1⟩
      have hd3 := arithmeticBound21 ⟨hs0, hl, hh⟩
      have hb3_0 := arithmeticBound22 ⟨hs0, hl, hh⟩
      have hb3_1 := arithmeticBound23 ⟨hs0, hl, hh⟩
      have hc3 : ConeBound Q ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1
          / 3) * (s ^ 2)))) (-1, 1) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
            adaptiveCoreLocalPoint s 3, hpts 3, hb3_0, hb3_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
            adaptiveCoreLocalPoint s 3, hpts 3, hb3_1⟩
      apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) *
          (s ^ 2)) + ((2 / 3) * s))), ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) +
          ((2 / 3) * (s ^ 2)))), ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) +
          ((1 / 3) * (s ^ 2)))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, by norm_num [rot, eastDir], hend⟩
    · by_cases hsplit : s ≤ (7 / 16)
      · have hl : 0 ≤ s - (3 / 8) := by
          linarith
        have hh : 0 ≤ (7 / 16) - s := by
          linarith
        have hd0 := arithmeticBound24 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound25 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound26 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^
            2)) + ((2 / 3) * s))) :=
          ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
              adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
        have hd1 := arithmeticBound27 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound28 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound29 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) +
            ((2 / 3) * s))) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3)
            * (s ^ 2)))) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 2, hpts 2,
              adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
        have hd2 := arithmeticBound30 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound31 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound32 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 /
            3) * (s ^ 2)))) ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1
            / 3) * (s ^ 2)))) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 0, hpts 0, hb2_0, hb2_1⟩
        have hd3 := arithmeticBound33 ⟨hs0, hl, hh⟩
        have hb3_0 := arithmeticBound34 ⟨hs0, hl, hh⟩
        have hb3_1 := arithmeticBound35 ⟨hs0, hl, hh⟩
        have hc3 : ConeBound Q ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) +
            ((1 / 3) * (s ^ 2)))) (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb3_0, hb3_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb3_1⟩
        apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) *
            (s ^ 2)) + ((2 / 3) * s))), ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s)
            + ((2 / 3) * (s ^ 2)))), ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) *
            s) + ((1 / 3) * (s ^ 2)))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, by norm_num [rot, eastDir], hend⟩
      · have hl : 0 ≤ s - (7 / 16) := by
          linarith
        have hh : 0 ≤ (1 / 2) - s := by
          linarith
        have hd0 := arithmeticBound36 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound37 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound38 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) +
            ((2 / 3) * (s ^ 2)))) :=
          ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
              adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
        have hd1 := arithmeticBound39 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound40 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound41 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 /
            3) * (s ^ 2)))) ((-1 * s), (2 * s)) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
        have hd2 := arithmeticBound42 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound43 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound44 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q ((-1 * s), (2 * s)) (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb2_0, hb2_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb2_1⟩
        apply one_le_side_of_fan hq (vs := [((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3)
            * s) + ((2 / 3) * (s ^ 2)))), ((-1 * s), (2 * s)), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
