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

/-- The four-point configuration for profile 5, owner 0, parameterized by the minimal section. -/
def profile5q0Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, ((3 / 2) * s)), ((1 + ((-5 / 4) * s)), 1), (((1 / 10) + ((-9 / 50) * s)), ((9 / 10)
      + ((-81 / 50) * s)))]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((33 / 10) * s) := by
    have heq : (((33 / 10) * s) : ℝ) = s ^ 1 * ((33 / 10)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile5q0Point s 2)
        (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) ≤ supportNum (((9 / 10) + ((-78 / 25) *
        s)), ((33 / 10) * s)) (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) : ℝ) = ((279411 /
          320000) + (8589 / 200) * ((1 / 40) - s) ^ 2 + (3909 / 100) * (s - 0) ^ 1 * ((1 / 40) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s)
      + ((594441 / 40000) * (s ^ 4))) := by
      have heq : ((((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
          ((594441 / 40000) * (s ^ 4))) : ℝ) = s ^ 1 * ((1239249321 / 2560000000) + (143150679 /
          40000) * ((1 / 40) - s) ^ 3 + (300140037 / 40000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 2 +
          (156394917 / 40000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
        ((594441 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s))
        (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-78 / 25) * s)), ((33 / 10) * s)) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) (((9 / 10) + ((-107 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-7617 / 5000) * (s ^ 2)) + ((-228 / 125) * s)) := by
    have heq : (((9 / 100) + ((-7617 / 5000) * (s ^ 2)) + ((-228 / 125) * s)) : ℝ) = ((347583 /
        8000000) + (372417 / 5000) * ((1 / 40) - s) ^ 2 + (190017 / 2500) * (s - 0) ^ 1 * ((1 / 40)
        - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) ≤ supportNum (((9 / 10) + ((-78 / 25) *
        s)), ((33 / 10) * s)) (profile5q0Point s 2) (profile5q0Point s 1) (profile5q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) : ℝ) = ((279411 /
          320000) + (8589 / 200) * ((1 / 40) - s) ^ 2 + (3909 / 100) * (s - 0) ^ 1 * ((1 / 40) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s)
      + ((594441 / 40000) * (s ^ 4))) := by
      have heq : ((((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
          ((594441 / 40000) * (s ^ 4))) : ℝ) = s ^ 1 * ((1239249321 / 2560000000) + (143150679 /
          40000) * ((1 / 40) - s) ^ 3 + (300140037 / 40000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 2 +
          (156394917 / 40000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
        ((594441 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s))
        (profile5q0Point s 2) (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-78 / 25) * s)), ((33 / 10) * s)) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile5q0Point s 2) (profile5q0Point s
        1) (profile5q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) := by
      have heq : ((1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) : ℝ) = ((7841 / 8000) + (159 / 5) *
          ((1 / 40) - s) ^ 2 + (153 / 5) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s
      ^ 4)) + ((41789 / 40000) * (s ^ 2))) := by
      have heq : (((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4))
          + ((41789 / 40000) * (s ^ 2))) : ℝ) = ((712289 / 12800000) + (439711 / 5) * ((1 / 40) - s)
          ^ 4 + (1311164 / 5) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 3 + (6517919 / 25) * (s - 0) ^ 2 *
          ((1 / 40) - s) ^ 2 + (2160618 / 25) * (s - 0) ^ 3 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4)) +
        ((41789 / 40000) * (s ^ 2))) = (supportNum (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile5q0Point s 2) (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((11 / 20) * s)) := by
    have heq : ((1 + ((11 / 20) * s)) : ℝ) = (1 + (11 / 20) * (s - 0) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile5q0Point s 3) (profile5q0Point s
        1) (profile5q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) := by
      have heq : ((1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) : ℝ) = ((7841 / 8000) + (159 / 5) *
          ((1 / 40) - s) ^ 2 + (153 / 5) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s
      ^ 4)) + ((41789 / 40000) * (s ^ 2))) := by
      have heq : (((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4))
          + ((41789 / 40000) * (s ^ 2))) : ℝ) = ((712289 / 12800000) + (439711 / 5) * ((1 / 40) - s)
          ^ 4 + (1311164 / 5) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 3 + (6517919 / 25) * (s - 0) ^ 2 *
          ((1 / 40) - s) ^ 2 + (2160618 / 25) * (s - 0) ^ 3 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4)) +
        ((41789 / 40000) * (s ^ 2))) = (supportNum (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile5q0Point s 3)
        (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((33 / 10) * s) := by
    have heq : (((33 / 10) * s) : ℝ) = s ^ 1 * ((33 / 10)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((209 / 200) + (9 / 5) * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3681 / 1000) + (81 / 25)
          * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile5q0Point s 2)
        (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) ≤ supportNum (((9 / 10) + ((-78 / 25) *
        s)), ((33 / 10) * s)) (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) : ℝ) = ((1102779 /
          1280000) + (2973 / 40) * ((3 / 80) - s) ^ 2 + (7047 / 100) * (s - (1 / 40)) ^ 1 * ((3 /
          80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s)
      + ((594441 / 40000) * (s ^ 4))) := by
      have heq : ((((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
          ((594441 / 40000) * (s ^ 4))) : ℝ) = s ^ 1 * ((9263709747 / 20480000000) + (650284821 /
          40000) * ((3 / 80) - s) ^ 3 + (265054959 / 8000) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 2
          + (674395533 / 40000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
        ((594441 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s))
        (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-78 / 25) * s)), ((33 / 10) * s)) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) (((9 / 10) + ((-107 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-7617 / 5000) * (s ^ 2)) + ((-228 / 125) * s)) := by
    have heq : (((9 / 100) + ((-7617 / 5000) * (s ^ 2)) + ((-228 / 125) * s)) : ℝ) = ((622647 /
        32000000) + (153537 / 1000) * ((3 / 80) - s) ^ 2 + (387651 / 2500) * (s - (1 / 40)) ^ 1 *
        ((3 / 80) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) ≤ supportNum (((9 / 10) + ((-78 / 25) *
        s)), ((33 / 10) * s)) (profile5q0Point s 2) (profile5q0Point s 1) (profile5q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) : ℝ) = ((1102779 /
          1280000) + (2973 / 40) * ((3 / 80) - s) ^ 2 + (7047 / 100) * (s - (1 / 40)) ^ 1 * ((3 /
          80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s)
      + ((594441 / 40000) * (s ^ 4))) := by
      have heq : ((((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
          ((594441 / 40000) * (s ^ 4))) : ℝ) = s ^ 1 * ((9263709747 / 20480000000) + (650284821 /
          40000) * ((3 / 80) - s) ^ 3 + (265054959 / 8000) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 2
          + (674395533 / 40000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
        ((594441 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s))
        (profile5q0Point s 2) (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-78 / 25) * s)), ((33 / 10) * s)) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile5q0Point s 2) (profile5q0Point s
        1) (profile5q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) := by
      have heq : ((1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) : ℝ) = ((3883 / 4000) + 60 * ((3 /
          80) - s) ^ 2 + (294 / 5) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s
      ^ 4)) + ((41789 / 40000) * (s ^ 2))) := by
      have heq : (((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4))
          + ((41789 / 40000) * (s ^ 2))) : ℝ) = ((99597 / 2560000) + (3428864 / 5) * ((3 / 80) - s)
          ^ 4 + (51292336 / 25) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 3 + (51155348 / 25) * (s -
          (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 2 + (17007296 / 25) * (s - (1 / 40)) ^ 3 * ((3 / 80) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4)) +
        ((41789 / 40000) * (s ^ 2))) = (supportNum (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile5q0Point s 2) (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((11 / 20) * s)) := by
    have heq : ((1 + ((11 / 20) * s)) : ℝ) = ((811 / 800) + (11 / 20) * (s - (1 / 40)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile5q0Point s 3) (profile5q0Point s
        1) (profile5q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) := by
      have heq : ((1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) : ℝ) = ((3883 / 4000) + 60 * ((3 /
          80) - s) ^ 2 + (294 / 5) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s
      ^ 4)) + ((41789 / 40000) * (s ^ 2))) := by
      have heq : (((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4))
          + ((41789 / 40000) * (s ^ 2))) : ℝ) = ((99597 / 2560000) + (3428864 / 5) * ((3 / 80) - s)
          ^ 4 + (51292336 / 25) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 3 + (51155348 / 25) * (s -
          (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 2 + (17007296 / 25) * (s - (1 / 40)) ^ 3 * ((3 / 80) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4)) +
        ((41789 / 40000) * (s ^ 2))) = (supportNum (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((209 / 200) + (9 / 5) * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3681 / 1000) + (81 / 25)
          * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile5q0Point s 3)
        (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((1 / 10) + ((81 / 50) * s)) := by
    have heq : (((1 / 10) + ((81 / 50) * s)) : ℝ) = ((643 / 4000) + (81 / 50) * (s - (3 / 80)) ^ 1)
        := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound19 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((427 / 400) + (9 / 5) * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((7443 / 2000) + (81 / 25)
          * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile5q0Point s 2)
        (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile5q0Point s 2) (profile5q0Point s
        3) (profile5q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((91 / 100) + ((999 / 1000) * s) + ((13617 / 5000) * (s ^ 2))) := by
      have heq : (((91 / 100) + ((999 / 1000) * s) + ((13617 / 5000) * (s ^ 2))) : ℝ) = ((30441353 /
          32000000) + (240651 / 2500) * (s - (3 / 80)) ^ 1 * ((1 / 20) - s) ^ 1 + (494919 / 5000) *
          (s - (3 / 80)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-819 / 10000) + ((103459 / 50000) * s) + ((3918689 / 1000000) * (s ^ 2)) +
      ((13603383 / 2500000) * (s ^ 3)) + ((185422689 / 25000000) * (s ^ 4))) := by
      have heq : (((-819 / 10000) + ((103459 / 50000) * s) + ((3918689 / 1000000) * (s ^ 2)) +
          ((13603383 / 2500000) * (s ^ 3)) + ((185422689 / 25000000) * (s ^ 4))) : ℝ) =
          ((1542676470609 / 1024000000000000) + (7640326040803 / 6250000) * (s - (3 / 80)) ^ 1 * ((1
          / 20) - s) ^ 3 + (46209429956221 / 12500000) * (s - (3 / 80)) ^ 2 * ((1 / 20) - s) ^ 2 +
          (23291728778479 / 6250000) * (s - (3 / 80)) ^ 3 * ((1 / 20) - s) ^ 1 + (250476358299 /
          200000) * (s - (3 / 80)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-819 / 10000) + ((103459 / 50000) * s) + ((3918689 / 1000000) * (s ^ 2)) +
        ((13603383 / 2500000) * (s ^ 3)) + ((185422689 / 25000000) * (s ^ 4))) = (supportNum (((9 /
        10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile5q0Point s 2)
        (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-107 / 100) * s)),
        ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound21 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((11 / 20) * s)) := by
    have heq : ((1 + ((11 / 20) * s)) : ℝ) = ((1633 / 1600) + (11 / 20) * (s - (3 / 80)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound22 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile5q0Point s 3) (profile5q0Point s
        1) (profile5q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) := by
      have heq : ((1 + ((-33 / 40) * s) + ((6 / 5) * (s ^ 2))) : ℝ) = ((3847 / 4000) + (288 / 5) *
          ((1 / 20) - s) ^ 2 + (282 / 5) * (s - (3 / 80)) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s
      ^ 4)) + ((41789 / 40000) * (s ^ 2))) := by
      have heq : (((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4))
          + ((41789 / 40000) * (s ^ 2))) : ℝ) = ((358773 / 16000000) + (16877328 / 25) * ((1 / 20) -
          s) ^ 4 + (50502016 / 25) * (s - (3 / 80)) ^ 1 * ((1 / 20) - s) ^ 3 + (10075108 / 5) * (s -
          (3 / 80)) ^ 2 * ((1 / 20) - s) ^ 2 + (16750816 / 25) * (s - (3 / 80)) ^ 3 * ((1 / 20) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-1399 / 1000) * s) + ((-99 / 50) * (s ^ 3)) + ((36 / 25) * (s ^ 4)) +
        ((41789 / 40000) * (s ^ 2))) = (supportNum (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound23 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((427 / 400) + (9 / 5) * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((7443 / 2000) + (81 / 25)
          * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile5q0Point s 3)
        (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound24 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((33 / 10) * s) := by
    have heq : (((33 / 10) * s) : ℝ) = s ^ 1 * ((33 / 10)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound25 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile5q0Point s 2)
        (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound26 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) ≤ supportNum (((9 / 10) + ((-78 / 25) *
        s)), ((33 / 10) * s)) (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-117 / 100) * s) + ((771 / 200) * (s ^ 2))) : ℝ) = ((16431 / 20000)
          + (2367 / 200) * ((1 / 10) - s) ^ 2 + (399 / 50) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^
          1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s)
      + ((594441 / 40000) * (s ^ 4))) := by
      have heq : ((((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
          ((594441 / 40000) * (s ^ 4))) : ℝ) = s ^ 1 * ((10504161 / 40000000) + (49816593 / 40000) *
          ((1 / 10) - s) ^ 3 + (52235991 / 20000) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 2 +
          (13515237 / 10000) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-90207 / 10000) * (s ^ 3)) + ((-4041 / 2000) * (s ^ 2)) + ((27 / 50) * s) +
        ((594441 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s))
        (profile5q0Point s 2) (profile5q0Point s 3) (profile5q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-78 / 25) * s)), ((33 / 10) * s)) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound27 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 10) + ((9 / 50) * s)) := by
    have heq : (((9 / 10) + ((9 / 50) * s)) : ℝ) = ((909 / 1000) + (9 / 50) * (s - (1 / 20)) ^ 1) :=
        by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound28 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) ≤ supportNum (((9 / 10) + ((-78 / 25) *
        s)), ((33 / 10) * s)) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((81 / 100) + ((327 / 500) * s) + ((6723 / 1250) * (s ^ 2))) := by
      have heq : (((81 / 100) + ((327 / 500) * s) + ((6723 / 1250) * (s ^ 2))) : ℝ) = ((428073 /
          500000) + (14898 / 625) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1 + (36519 / 1250) * (s -
          (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-1539 / 10000) + ((-296919 / 250000) * (s ^ 2)) + ((92637 / 25000) * s) +
      ((2198421 / 312500) * (s ^ 3)) + ((45198729 / 1562500) * (s ^ 4))) := by
      have heq : (((-1539 / 10000) + ((-296919 / 250000) * (s ^ 2)) + ((92637 / 25000) * s) +
          ((2198421 / 312500) * (s ^ 3)) + ((45198729 / 1562500) * (s ^ 4))) : ℝ) = ((7366243329 /
          250000000000) + (11418556554 / 390625) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 3 +
          (68605549911 / 781250) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 2 + (34450039503 / 390625)
          * (s - (1 / 20)) ^ 3 * ((1 / 10) - s) ^ 1 + (9261696627 / 312500) * (s - (1 / 20)) ^ 4) :=
          by
        ring
      rw [heq]
      positivity
    have heq : ((-1539 / 10000) + ((-296919 / 250000) * (s ^ 2)) + ((92637 / 25000) * s) + ((2198421
        / 312500) * (s ^ 3)) + ((45198729 / 1562500) * (s ^ 4))) = (supportNum (((9 / 10) + ((-78 /
        25) * s)), ((33 / 10) * s)) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s
        0)) ^ 2 - normSq (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound29 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile5q0Point s 3) (profile5q0Point s 1) (profile5q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile5q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile5q0Point s 3)
        (profile5q0Point s 1) (profile5q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile5q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem profile5q0_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile5q0Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 20)
  · by_cases hsplit : s ≤ (1 / 40)
    · have hl : 0 ≤ s - 0 := by
        linarith
      have hh : 0 ≤ (1 / 40) - s := by
        linarith
      have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) :=
        ⟨profile5q0Point s 2, hpts 2, profile5q0Point s 3, hpts 3, profile5q0Point s 0, hpts 0,
            hb0_0, hb0_1⟩
      have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) (((9 / 10) + ((-107 /
          100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
        ⟨profile5q0Point s 2, hpts 2, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
            hb1_0, hb1_1⟩
      have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
      have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
      have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
      have hc2 : ConeBound Q (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1)
          :=
        ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
            hb2_0, hb2_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
            hb2_1⟩
      apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)), (((9 /
          10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
    · by_cases hsplit : s ≤ (3 / 80)
      · have hl : 0 ≤ s - (1 / 40) := by
          linarith
        have hh : 0 ≤ (3 / 80) - s := by
          linarith
        have hd0 := arithmeticBound9 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) :=
          ⟨profile5q0Point s 2, hpts 2, profile5q0Point s 3, hpts 3, profile5q0Point s 0, hpts 0,
              hb0_0, hb0_1⟩
        have hd1 := arithmeticBound12 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) (((9 / 10) + ((-107
            / 100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
          ⟨profile5q0Point s 2, hpts 2, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
              hb1_0, hb1_1⟩
        have hd2 := arithmeticBound15 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound16 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound17 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1,
            1) :=
          ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
              hb2_0, hb2_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
              hb2_1⟩
        apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)), (((9 /
            10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
      · have hl : 0 ≤ s - (3 / 80) := by
          linarith
        have hh : 0 ≤ (1 / 20) - s := by
          linarith
        have hd0 := arithmeticBound18 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound19 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound20 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) *
            s))) :=
          ⟨profile5q0Point s 2, hpts 2, profile5q0Point s 3, hpts 3, profile5q0Point s 0, hpts 0,
              hb0_0, hb0_1⟩
        have hd1 := arithmeticBound21 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound22 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound23 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q (((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1,
            1) :=
          ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
              hb1_0, hb1_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0,
              hb1_1⟩
        apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-107 / 100) * s)), ((1 / 10) + ((81 / 50)
            * s))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩
  · have hl : 0 ≤ s - (1 / 20) := by
      linarith
    have hh : 0 ≤ (1 / 10) - s := by
      linarith
    have hd0 := arithmeticBound24 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound25 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound26 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) :=
      ⟨profile5q0Point s 2, hpts 2, profile5q0Point s 3, hpts 3, profile5q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound27 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound28 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound29 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)) (-1, 1) :=
      ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile5q0Point s 3, hpts 3, profile5q0Point s 1, hpts 1, profile5q0Point s 0, hpts 0, hb1_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-78 / 25) * s)), ((33 / 10) * s)), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
