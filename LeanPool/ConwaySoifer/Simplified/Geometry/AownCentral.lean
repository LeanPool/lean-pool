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

/-- The five-point configuration used by the Aown central obstruction. -/
def aownCentralPoint (s : ℝ) : Fin 5 → Point :=
  ![((-1 * s), ((1 / 2) * s)), (((-1 / 2) * s), ((-1 / 2) * s)), (((1 / 2) * s), (-1 * s)), ((1 +
      ((-4 / 3) * s)), 0), (((-1 / 2) * s), s)]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (1, 0) (s, (1 + ((-11 / 6) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((-11 / 6) * s)) := by
    have heq : (1 + ((-11 / 6) * s)) = ((49 / 60) + (11 / 6) * ((1 / 10) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len (1, 0) ≤ supportNum (1, 0) (aownCentralPoint s 4) (aownCentralPoint s 1) (aownCentralPoint s
        3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((2 / 3) * s)) := by
      have heq : (1 + ((2 / 3) * s)) = (1 + (2 / 3) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((4 / 3) * s) + ((4 / 9) * (s ^ 2))) := by
      have heq : (((4 / 3) * s) + ((4 / 9) * (s ^ 2))) = s ^ 1 * ((4 / 3) + (4 / 9) * (s - 0) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    have heq : (((4 / 3) * s) + ((4 / 9) * (s ^ 2))) = (supportNum (1, 0) (aownCentralPoint s 4)
        (aownCentralPoint s 1) (aownCentralPoint s 3)) ^ 2 - normSq (1, 0) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len (s, (1 + ((-11 / 6) * s))) ≤ supportNum (s, (1 + ((-11 / 6) * s))) (aownCentralPoint s 4)
        (aownCentralPoint s 1) (aownCentralPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-7 / 6) * s) + ((23 / 18) * (s ^ 2))) := by
      have heq : (1 + ((-7 / 6) * s) + ((23 / 18) * (s ^ 2))) = ((1613 / 1800) + (187 / 18) * ((1 /
          10) - s) ^ 2 + (82 / 9) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-161 / 54) * (s ^ 3)) + ((1 / 3) * s) + ((25 / 18) * (s ^ 2)) + ((529 /
      324) * (s ^ 4))) := by
      have heq : (((-161 / 54) * (s ^ 3)) + ((1 / 3) * s) + ((25 / 18) * (s ^ 2)) + ((529 / 324) *
          (s ^ 4))) = s ^ 1 * ((1 / 3) + (1250 / 9) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 2 + (6695 / 27)
          * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1 + (35869 / 324) * (s - 0) ^ 3) := by
        ring
      rw [heq]
      positivity
    have heq : (((-161 / 54) * (s ^ 3)) + ((1 / 3) * s) + ((25 / 18) * (s ^ 2)) + ((529 / 324) * (s
        ^ 4))) = (supportNum (s, (1 + ((-11 / 6) * s))) (aownCentralPoint s 4) (aownCentralPoint s
        1) (aownCentralPoint s 3)) ^ 2 - normSq (s, (1 + ((-11 / 6) * s))) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (s, (1 + ((-11 / 6) * s))) ((-1 * s), (1 + ((-5 / 6) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((2 * s) + ((-8 / 3) * (s ^ 2))) := by
    have heq : ((2 * s) + ((-8 / 3) * (s ^ 2))) = s ^ 1 * ((26 / 15) + (8 / 3) * ((1 / 10) - s) ^ 1)
        := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len (s, (1 + ((-11 / 6) * s))) ≤ supportNum (s, (1 + ((-11 / 6) * s))) (aownCentralPoint s 0)
        (aownCentralPoint s 2) (aownCentralPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-14 / 9) * (s ^ 2)) + ((-1 / 6) * s)) := by
      have heq : (1 + ((-14 / 9) * (s ^ 2)) + ((-1 / 6) * s)) = ((871 / 900) + (29 / 9) * ((1 / 10)
          - s) ^ 2 + (43 / 9) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-101 / 18) * (s ^ 2)) + ((7 / 3) * s) + ((14 / 27) * (s ^ 3)) + ((196 /
      81) * (s ^ 4))) := by
      have heq : (((-101 / 18) * (s ^ 2)) + ((7 / 3) * s) + ((14 / 27) * (s ^ 3)) + ((196 / 81) * (s
          ^ 4))) = s ^ 1 * ((72083 / 40500) + (44834 / 81) * ((1 / 10) - s) ^ 3 + (29684 / 27) * (s
          - 0) ^ 1 * ((1 / 10) - s) ^ 2 + (14674 / 27) * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-101 / 18) * (s ^ 2)) + ((7 / 3) * s) + ((14 / 27) * (s ^ 3)) + ((196 / 81) * (s ^
        4))) = (supportNum (s, (1 + ((-11 / 6) * s))) (aownCentralPoint s 0) (aownCentralPoint s 2)
        (aownCentralPoint s 3)) ^ 2 - normSq (s, (1 + ((-11 / 6) * s))) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len ((-1 * s), (1 + ((-5 / 6) * s))) ≤ supportNum ((-1 * s), (1 + ((-5 / 6) * s)))
        (aownCentralPoint s 0) (aownCentralPoint s 2) (aownCentralPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) := by
      have heq : (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) = ((793 / 900) + (107 / 9) * ((1 / 10)
          - s) ^ 2 + (109 / 9) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27)
      * (s ^ 3))) := by
      have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
          3))) = s ^ 1 * ((7187 / 40500) + (12626 / 81) * ((1 / 10) - s) ^ 3 + (8276 / 27) * (s - 0)
          ^ 1 * ((1 / 10) - s) ^ 2 + (4066 / 27) * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
        3))) = (supportNum ((-1 * s), (1 + ((-5 / 6) * s))) (aownCentralPoint s 0) (aownCentralPoint
        s 2) (aownCentralPoint s 3)) ^ 2 - normSq ((-1 * s), (1 + ((-5 / 6) * s))) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    0 < cross ((-1 * s), (1 + ((-5 / 6) * s))) (((-1 / 2) * s), s) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((1 / 2) * s) + ((-17 / 12) * (s ^ 2))) := by
    have heq : (((1 / 2) * s) + ((-17 / 12) * (s ^ 2))) = s ^ 1 * ((43 / 120) + (17 / 12) * ((1 /
        10) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len ((-1 * s), (1 + ((-5 / 6) * s))) ≤ supportNum ((-1 * s), (1 + ((-5 / 6) * s)))
        (aownCentralPoint s 0) (aownCentralPoint s 3) (aownCentralPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) := by
      have heq : (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) = ((793 / 900) + (107 / 9) * ((1 / 10)
          - s) ^ 2 + (109 / 9) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27)
      * (s ^ 3))) := by
      have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
          3))) = s ^ 1 * ((7187 / 40500) + (12626 / 81) * ((1 / 10) - s) ^ 3 + (8276 / 27) * (s - 0)
          ^ 1 * ((1 / 10) - s) ^ 2 + (4066 / 27) * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
        3))) = (supportNum ((-1 * s), (1 + ((-5 / 6) * s))) (aownCentralPoint s 0) (aownCentralPoint
        s 3) (aownCentralPoint s 3)) ^ 2 - normSq ((-1 * s), (1 + ((-5 / 6) * s))) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len (((-1 / 2) * s), s) ≤ supportNum (((-1 / 2) * s), s) (aownCentralPoint s 0)
        (aownCentralPoint s 3) (aownCentralPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (s + ((-7 / 12) * (s ^ 2))) := by
      have heq : (s + ((-7 / 12) * (s ^ 2))) = s ^ 1 * ((113 / 120) + (7 / 12) * ((1 / 10) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-7 / 6) * (s ^ 3)) + ((1 / 4) * (s ^ 2)) + ((49 / 144) * (s ^ 4))) := by
      have heq : (((-7 / 6) * (s ^ 3)) + ((1 / 4) * (s ^ 2)) + ((49 / 144) * (s ^ 4))) = s ^ 2 *
          ((1969 / 14400) + (1631 / 144) * ((1 / 10) - s) ^ 2 + (791 / 72) * (s - 0) ^ 1 * ((1 / 10)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-7 / 6) * (s ^ 3)) + ((1 / 4) * (s ^ 2)) + ((49 / 144) * (s ^ 4))) = (supportNum
        (((-1 / 2) * s), s) (aownCentralPoint s 0) (aownCentralPoint s 3) (aownCentralPoint s 3)) ^
        2 - normSq (((-1 / 2) * s), s) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (((-1 / 2) * s), s) ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (((1 / 2) * s) + ((-17 / 12) * (s ^ 2))) := by
    have heq : (((1 / 2) * s) + ((-17 / 12) * (s ^ 2))) = s ^ 1 * ((43 / 120) + (17 / 12) * ((1 /
        10) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len (((-1 / 2) * s), s) ≤ supportNum (((-1 / 2) * s), s) (aownCentralPoint s 1)
        (aownCentralPoint s 3) (aownCentralPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (s + ((-7 / 12) * (s ^ 2))) := by
      have heq : (s + ((-7 / 12) * (s ^ 2))) = s ^ 1 * ((113 / 120) + (7 / 12) * ((1 / 10) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-7 / 6) * (s ^ 3)) + ((1 / 4) * (s ^ 2)) + ((49 / 144) * (s ^ 4))) := by
      have heq : (((-7 / 6) * (s ^ 3)) + ((1 / 4) * (s ^ 2)) + ((49 / 144) * (s ^ 4))) = s ^ 2 *
          ((1969 / 14400) + (1631 / 144) * ((1 / 10) - s) ^ 2 + (791 / 72) * (s - 0) ^ 1 * ((1 / 10)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-7 / 6) * (s ^ 3)) + ((1 / 4) * (s ^ 2)) + ((49 / 144) * (s ^ 4))) = (supportNum
        (((-1 / 2) * s), s) (aownCentralPoint s 1) (aownCentralPoint s 3) (aownCentralPoint s 3)) ^
        2 - normSq (((-1 / 2) * s), s) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) ≤ supportNum ((-1 + ((11 / 6) * s)), (1 + ((-5
        / 6) * s))) (aownCentralPoint s 1) (aownCentralPoint s 3) (aownCentralPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) := by
      have heq : (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) = ((793 / 900) + (107 / 9) * ((1 / 10)
          - s) ^ 2 + (109 / 9) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27)
      * (s ^ 3))) := by
      have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
          3))) = s ^ 1 * ((7187 / 40500) + (12626 / 81) * ((1 / 10) - s) ^ 3 + (8276 / 27) * (s - 0)
          ^ 1 * ((1 / 10) - s) ^ 2 + (4066 / 27) * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
        3))) = (supportNum ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) (aownCentralPoint s 1)
        (aownCentralPoint s 3) (aownCentralPoint s 3)) ^ 2 - normSq ((-1 + ((11 / 6) * s)), (1 +
        ((-5 / 6) * s))) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    0 < cross ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < s := by
    have heq : s = s ^ 1 * (1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) ≤ supportNum ((-1 + ((11 / 6) * s)), (1 + ((-5
        / 6) * s))) (aownCentralPoint s 1) (aownCentralPoint s 3) (aownCentralPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) := by
      have heq : (1 + ((-7 / 6) * s) + ((-2 / 9) * (s ^ 2))) = ((793 / 900) + (107 / 9) * ((1 / 10)
          - s) ^ 2 + (109 / 9) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27)
      * (s ^ 3))) := by
      have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
          3))) = s ^ 1 * ((7187 / 40500) + (12626 / 81) * ((1 / 10) - s) ^ 3 + (8276 / 27) * (s - 0)
          ^ 1 * ((1 / 10) - s) ^ 2 + (4066 / 27) * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-29 / 18) * (s ^ 2)) + ((1 / 3) * s) + ((4 / 81) * (s ^ 4)) + ((14 / 27) * (s ^
        3))) = (supportNum ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) (aownCentralPoint s 1)
        (aownCentralPoint s 3) (aownCentralPoint s 4)) ^ 2 - normSq ((-1 + ((11 / 6) * s)), (1 +
        ((-5 / 6) * s))) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 10) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (aownCentralPoint s 1) (aownCentralPoint s 3) (aownCentralPoint
        s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((2 / 3) * s)) := by
      have heq : (1 + ((2 / 3) * s)) = (1 + (2 / 3) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [aownCentralPoint, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((4 / 3) * s) + ((4 / 9) * (s ^ 2))) := by
      have heq : (((4 / 3) * s) + ((4 / 9) * (s ^ 2))) = s ^ 1 * ((4 / 3) + (4 / 9) * (s - 0) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    have heq : (((4 / 3) * s) + ((4 / 9) * (s ^ 2))) = (supportNum (-1, 1) (aownCentralPoint s 1)
        (aownCentralPoint s 3) (aownCentralPoint s 4)) ^ 2 - normSq (-1, 1) := by
      simp [aownCentralPoint, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem aownCentral_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, aownCentralPoint s i ∈ Q.carrier) : 1 ≤ Q.side := by
  have hl : 0 ≤ s - 0 := by
    linarith
  have hh : 0 ≤ (1 / 10) - s := by
    linarith
  have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
  have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
  have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
  have hc0 : ConeBound Q (1, 0) (s, (1 + ((-11 / 6) * s))) :=
    ⟨aownCentralPoint s 4, hpts 4, aownCentralPoint s 1, hpts 1, aownCentralPoint s 3, hpts 3,
        hb0_0, hb0_1⟩
  have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
  have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
  have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
  have hc1 : ConeBound Q (s, (1 + ((-11 / 6) * s))) ((-1 * s), (1 + ((-5 / 6) * s))) :=
    ⟨aownCentralPoint s 0, hpts 0, aownCentralPoint s 2, hpts 2, aownCentralPoint s 3, hpts 3,
        hb1_0, hb1_1⟩
  have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
  have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
  have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
  have hc2 : ConeBound Q ((-1 * s), (1 + ((-5 / 6) * s))) (((-1 / 2) * s), s) :=
    ⟨aownCentralPoint s 0, hpts 0, aownCentralPoint s 3, hpts 3, aownCentralPoint s 3, hpts 3,
        hb2_0, hb2_1⟩
  have hd3 := arithmeticBound9 ⟨hs0, hl, hh⟩
  have hb3_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
  have hb3_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
  have hc3 : ConeBound Q (((-1 / 2) * s), s) ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) :=
    ⟨aownCentralPoint s 1, hpts 1, aownCentralPoint s 3, hpts 3, aownCentralPoint s 3, hpts 3,
        hb3_0, hb3_1⟩
  have hd4 := arithmeticBound12 ⟨hs0, hl, hh⟩
  have hb4_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
  have hb4_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
  have hc4 : ConeBound Q ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))) (-1, 1) :=
    ⟨aownCentralPoint s 1, hpts 1, aownCentralPoint s 3, hpts 3, aownCentralPoint s 4, hpts 4,
        hb4_0, hb4_1⟩
  have hend : SupportBound Q (-1, 1) :=
    ⟨aownCentralPoint s 1, hpts 1, aownCentralPoint s 3, hpts 3, aownCentralPoint s 4, hpts 4,
        hb4_1⟩
  apply one_le_side_of_fan hq (vs := [(s, (1 + ((-11 / 6) * s))), ((-1 * s), (1 + ((-5 / 6) * s))),
      (((-1 / 2) * s), s), ((-1 + ((11 / 6) * s)), (1 + ((-5 / 6) * s))), (-1, 1)])
  exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, hd4, hc4, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
