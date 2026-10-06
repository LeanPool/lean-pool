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

/-- The four-point configuration for profile 6, owner 0, parameterized by the minimal section. -/
def profile6q0Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, ((7 / 4) * s)), ((1 + ((-3 / 2) * s)), 1), (((1 / 10) + ((-9 / 50) * s)), ((9 / 10)
      + ((-81 / 50) * s)))]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((71 / 20) * s) := by
    have heq : (((71 / 20) * s) : ℝ) = s ^ 1 * ((71 / 20)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile6q0Point s 2)
        (profile6q0Point s 3) (profile6q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) ≤ supportNum (((9 / 10) + ((-337 / 100) *
        s)), ((71 / 20) * s)) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) : ℝ) = ((138921 /
          160000) + (5079 / 100) * ((1 / 40) - s) ^ 2 + (2289 / 50) * (s - 0) ^ 1 * ((1 / 40) - s) ^
          1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s)
      + ((251001 / 10000) * (s ^ 4))) := by
      have heq : ((((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
          ((251001 / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((208549841 / 640000000) + (21850159 / 10000)
          * ((1 / 40) - s) ^ 3 + (49040477 / 10000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 2 + (26939317 /
          10000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
        ((251001 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) *
        s)) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0)) ^ 2 - normSq (((9 /
        10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) (((9 / 10) + ((-33 / 25) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-3867 / 5000) * (s ^ 2)) + ((-1037 / 500) * s)) := by
    have heq : (((9 / 100) + ((-3867 / 5000) * (s ^ 2)) + ((-1037 / 500) * s)) : ℝ) = ((301333 /
        8000000) + (418667 / 5000) * ((1 / 40) - s) ^ 2 + (211267 / 2500) * (s - 0) ^ 1 * ((1 / 40)
        - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) ≤ supportNum (((9 / 10) + ((-337 / 100) *
        s)), ((71 / 20) * s)) (profile6q0Point s 2) (profile6q0Point s 1) (profile6q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) : ℝ) = ((138921 /
          160000) + (5079 / 100) * ((1 / 40) - s) ^ 2 + (2289 / 50) * (s - 0) ^ 1 * ((1 / 40) - s) ^
          1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s)
      + ((251001 / 10000) * (s ^ 4))) := by
      have heq : ((((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
          ((251001 / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((208549841 / 640000000) + (21850159 / 10000)
          * ((1 / 40) - s) ^ 3 + (49040477 / 10000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 2 + (26939317 /
          10000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
        ((251001 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) *
        s)) (profile6q0Point s 2) (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 - normSq (((9 /
        10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile6q0Point s 2) (profile6q0Point s 1)
        (profile6q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) : ℝ) = ((309981 / 320000) +
          (10019 / 200) * ((1 / 40) - s) ^ 2 + (4819 / 100) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 /
      2500) * (s ^ 2)) + ((145161 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s
          ^ 2)) + ((145161 / 40000) * (s ^ 4))) : ℝ) = ((4620162761 / 102400000000) + (4595837239 /
          40000) * ((1 / 40) - s) ^ 4 + (3396477239 / 10000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 3 +
          (6696042917 / 20000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 2 + (1100467239 / 10000) * (s - 0) ^
          3 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s ^
        2)) + ((145161 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-33 / 25) * s)), ((1 / 10)
        + ((81 / 50) * s))) (profile6q0Point s 2) (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((3 / 10) * s)) := by
    have heq : ((1 + ((3 / 10) * s)) : ℝ) = (1 + (3 / 10) * (s - 0) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile6q0Point s 3) (profile6q0Point s 1)
        (profile6q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) : ℝ) = ((309981 / 320000) +
          (10019 / 200) * ((1 / 40) - s) ^ 2 + (4819 / 100) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 /
      2500) * (s ^ 2)) + ((145161 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s
          ^ 2)) + ((145161 / 40000) * (s ^ 4))) : ℝ) = ((4620162761 / 102400000000) + (4595837239 /
          40000) * ((1 / 40) - s) ^ 4 + (3396477239 / 10000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 3 +
          (6696042917 / 20000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 2 + (1100467239 / 10000) * (s - 0) ^
          3 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s ^
        2)) + ((145161 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-33 / 25) * s)), ((1 / 10)
        + ((81 / 50) * s))) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile6q0Point s 3)
        (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((71 / 20) * s) := by
    have heq : (((71 / 20) * s) : ℝ) = s ^ 1 * ((71 / 20)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((209 / 200) + (9 / 5) * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3681 / 1000) + (81 / 25)
          * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile6q0Point s 2)
        (profile6q0Point s 3) (profile6q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) ≤ supportNum (((9 / 10) + ((-337 / 100) *
        s)), ((71 / 20) * s)) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) : ℝ) = ((547029 /
          640000) + (1731 / 20) * ((3 / 80) - s) ^ 2 + (4077 / 50) * (s - (1 / 40)) ^ 1 * ((3 / 80)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s)
      + ((251001 / 10000) * (s ^ 4))) := by
      have heq : ((((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
          ((251001 / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((1551216147 / 5120000000) + (117182581 /
          10000) * ((3 / 80) - s) ^ 3 + (9751619 / 400) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 2 +
          (126356893 / 10000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
        ((251001 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) *
        s)) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0)) ^ 2 - normSq (((9 /
        10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) (((9 / 10) + ((-33 / 25) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-3867 / 5000) * (s ^ 2)) + ((-1037 / 500) * s)) := by
    have heq : (((9 / 100) + ((-3867 / 5000) * (s ^ 2)) + ((-1037 / 500) * s)) : ℝ) = ((356397 /
        32000000) + (169787 / 1000) * ((3 / 80) - s) ^ 2 + (426401 / 2500) * (s - (1 / 40)) ^ 1 *
        ((3 / 80) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) ≤ supportNum (((9 / 10) + ((-337 / 100) *
        s)), ((71 / 20) * s)) (profile6q0Point s 2) (profile6q0Point s 1) (profile6q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) : ℝ) = ((547029 /
          640000) + (1731 / 20) * ((3 / 80) - s) ^ 2 + (4077 / 50) * (s - (1 / 40)) ^ 1 * ((3 / 80)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s)
      + ((251001 / 10000) * (s ^ 4))) := by
      have heq : ((((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
          ((251001 / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((1551216147 / 5120000000) + (117182581 /
          10000) * ((3 / 80) - s) ^ 3 + (9751619 / 400) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 2 +
          (126356893 / 10000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
        ((251001 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) *
        s)) (profile6q0Point s 2) (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 - normSq (((9 /
        10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile6q0Point s 2) (profile6q0Point s 1)
        (profile6q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) : ℝ) = ((1221029 / 1280000) +
          (3779 / 40) * ((3 / 80) - s) ^ 2 + (9257 / 100) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 /
      2500) * (s ^ 2)) + ((145161 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s
          ^ 2)) + ((145161 / 40000) * (s ^ 4))) : ℝ) = ((39439025241 / 1638400000000) + (6896715787
          / 8000) * ((3 / 80) - s) ^ 4 + (25679841023 / 10000) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s)
          ^ 3 + (10200253453 / 4000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 2 + (8441651053 /
          10000) * (s - (1 / 40)) ^ 3 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s ^
        2)) + ((145161 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-33 / 25) * s)), ((1 / 10)
        + ((81 / 50) * s))) (profile6q0Point s 2) (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((3 / 10) * s)) := by
    have heq : ((1 + ((3 / 10) * s)) : ℝ) = ((403 / 400) + (3 / 10) * (s - (1 / 40)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile6q0Point s 3) (profile6q0Point s 1)
        (profile6q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) : ℝ) = ((1221029 / 1280000) +
          (3779 / 40) * ((3 / 80) - s) ^ 2 + (9257 / 100) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 /
      2500) * (s ^ 2)) + ((145161 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s
          ^ 2)) + ((145161 / 40000) * (s ^ 4))) : ℝ) = ((39439025241 / 1638400000000) + (6896715787
          / 8000) * ((3 / 80) - s) ^ 4 + (25679841023 / 10000) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s)
          ^ 3 + (10200253453 / 4000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 2 + (8441651053 /
          10000) * (s - (1 / 40)) ^ 3 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s ^
        2)) + ((145161 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-33 / 25) * s)), ((1 / 10)
        + ((81 / 50) * s))) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((209 / 200) + (9 / 5) * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3681 / 1000) + (81 / 25)
          * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile6q0Point s 3)
        (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
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
    len (1, 0) ≤ supportNum (1, 0) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((427 / 400) + (9 / 5) * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((7443 / 2000) + (81 / 25)
          * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile6q0Point s 2)
        (profile6q0Point s 3) (profile6q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile6q0Point s 2) (profile6q0Point s 3)
        (profile6q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((91 / 100) + ((387 / 500) * s) + ((1674 / 625) * (s ^ 2))) := by
      have heq : (((91 / 100) + ((387 / 500) * s) + ((1674 / 625) * (s ^ 2))) : ℝ) = ((1885583 /
          2000000) + (48744 / 625) * (s - (3 / 80)) ^ 1 * ((1 / 20) - s) ^ 1 + (50418 / 625) * (s -
          (3 / 80)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-819 / 10000) + ((53367 / 25000) * s) + ((323919 / 78125) * (s ^ 3)) +
      ((811341 / 250000) * (s ^ 2)) + ((2802276 / 390625) * (s ^ 4))) := by
      have heq : (((-819 / 10000) + ((53367 / 25000) * s) + ((323919 / 78125) * (s ^ 3)) + ((811341
          / 250000) * (s ^ 2)) + ((2802276 / 390625) * (s ^ 4))) : ℝ) = ((11788499889 /
          4000000000000) + (479417431008 / 390625) * (s - (3 / 80)) ^ 1 * ((1 / 20) - s) ^ 3 +
          (1447683134328 / 390625) * (s - (3 / 80)) ^ 2 * ((1 / 20) - s) ^ 2 + (1457277170544 /
          390625) * (s - (3 / 80)) ^ 3 * ((1 / 20) - s) ^ 1 + (3912114156 / 3125) * (s - (3 / 80)) ^
          4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-819 / 10000) + ((53367 / 25000) * s) + ((323919 / 78125) * (s ^ 3)) + ((811341 /
        250000) * (s ^ 2)) + ((2802276 / 390625) * (s ^ 4))) = (supportNum (((9 / 10) + ((-33 / 25)
        * s)), ((1 / 10) + ((81 / 50) * s))) (profile6q0Point s 2) (profile6q0Point s 3)
        (profile6q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) *
        s))) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound21 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((3 / 10) * s)) := by
    have heq : ((1 + ((3 / 10) * s)) : ℝ) = ((809 / 800) + (3 / 10) * (s - (3 / 80)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound22 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile6q0Point s 3) (profile6q0Point s 1)
        (profile6q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-13 / 10) * s) + ((381 / 200) * (s ^ 2))) : ℝ) = ((75181 / 80000) + (18133
          / 200) * ((1 / 20) - s) ^ 2 + (2219 / 25) * (s - (3 / 80)) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 /
      2500) * (s ^ 2)) + ((145161 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s
          ^ 2)) + ((145161 / 40000) * (s ^ 4))) : ℝ) = ((24848361 / 6400000000) + (1323113793 /
          1600) * ((1 / 20) - s) ^ 4 + (6159048443 / 2500) * (s - (3 / 80)) ^ 1 * ((1 / 20) - s) ^ 3
          + (3058436819 / 1250) * (s - (3 / 80)) ^ 2 * ((1 / 20) - s) ^ 2 + (506295356 / 625) * (s -
          (3 / 80)) ^ 3 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-4953 / 1000) * (s ^ 3)) + ((-937 / 500) * s) + ((8179 / 2500) * (s ^
        2)) + ((145161 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-33 / 25) * s)), ((1 / 10)
        + ((81 / 50) * s))) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound23 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (1 / 20) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((427 / 400) + (9 / 5) * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((7443 / 2000) + (81 / 25)
          * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile6q0Point s 3)
        (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound24 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((71 / 20) * s) := by
    have heq : (((71 / 20) * s) : ℝ) = s ^ 1 * ((71 / 20)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound25 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile6q0Point s 2)
        (profile6q0Point s 3) (profile6q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound26 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) ≤ supportNum (((9 / 10) + ((-337 / 100) *
        s)), ((71 / 20) * s)) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-279 / 200) * s) + ((501 / 100) * (s ^ 2))) : ℝ) = ((4053 / 5000) +
          (1287 / 100) * ((1 / 10) - s) ^ 2 + (393 / 50) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s)
      + ((251001 / 10000) * (s ^ 4))) := by
      have heq : ((((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
          ((251001 / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((177667 / 1250000) + (10757233 / 10000) *
          ((1 / 10) - s) ^ 3 + (11653021 / 5000) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 2 + (768613
          / 625) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-139779 / 10000) * (s ^ 3)) + ((-1651 / 1600) * (s ^ 2)) + ((9 / 25) * s) +
        ((251001 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) *
        s)) (profile6q0Point s 2) (profile6q0Point s 3) (profile6q0Point s 0)) ^ 2 - normSq (((9 /
        10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound27 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) (-1, 1) := by
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
    len (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) ≤ supportNum (((9 / 10) + ((-337 / 100) *
        s)), ((71 / 20) * s)) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((81 / 100) + ((679 / 1000) * s) + ((28917 / 5000) * (s ^ 2))) := by
      have heq : (((81 / 100) + ((679 / 1000) * s) + ((28917 / 5000) * (s ^ 2))) : ℝ) = ((1716817 /
          2000000) + (62867 / 2500) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1 + (154651 / 5000) * (s
          - (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-1539 / 10000) + ((-2165751 / 1000000) * (s ^ 2)) + ((198549 / 50000) * s)
      + ((19634643 / 2500000) * (s ^ 3)) + ((836192889 / 25000000) * (s ^ 4))) := by
      have heq : (((-1539 / 10000) + ((-2165751 / 1000000) * (s ^ 2)) + ((198549 / 50000) * s) +
          ((19634643 / 2500000) * (s ^ 3)) + ((836192889 / 25000000) * (s ^ 4))) : ℝ) =
          ((161701611489 / 4000000000000) + (191501634339 / 6250000) * (s - (1 / 20)) ^ 1 * ((1 /
          10) - s) ^ 3 + (1146580022601 / 12500000) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 2 +
          (573893044623 / 6250000) * (s - (1 / 20)) ^ 3 * ((1 / 10) - s) ^ 1 + (153850972707 /
          5000000) * (s - (1 / 20)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-1539 / 10000) + ((-2165751 / 1000000) * (s ^ 2)) + ((198549 / 50000) * s) +
        ((19634643 / 2500000) * (s ^ 3)) + ((836192889 / 25000000) * (s ^ 4))) = (supportNum (((9 /
        10) + ((-337 / 100) * s)), ((71 / 20) * s)) (profile6q0Point s 3) (profile6q0Point s 1)
        (profile6q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound29 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile6q0Point s 3) (profile6q0Point s 1) (profile6q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile6q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile6q0Point s 3)
        (profile6q0Point s 1) (profile6q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile6q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem profile6q0_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile6q0Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 20)
  · by_cases hsplit : s ≤ (1 / 40)
    · have hl : 0 ≤ s - 0 := by
        linarith
      have hh : 0 ≤ (1 / 40) - s := by
        linarith
      have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) :=
        ⟨profile6q0Point s 2, hpts 2, profile6q0Point s 3, hpts 3, profile6q0Point s 0, hpts 0,
            hb0_0, hb0_1⟩
      have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) (((9 / 10) + ((-33 /
          25) * s)), ((1 / 10) + ((81 / 50) * s))) :=
        ⟨profile6q0Point s 2, hpts 2, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
            hb1_0, hb1_1⟩
      have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
      have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
      have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
      have hc2 : ConeBound Q (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1)
          :=
        ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
            hb2_0, hb2_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
            hb2_1⟩
      apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)), (((9 /
          10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
    · by_cases hsplit : s ≤ (3 / 80)
      · have hl : 0 ≤ s - (1 / 40) := by
          linarith
        have hh : 0 ≤ (3 / 80) - s := by
          linarith
        have hd0 := arithmeticBound9 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) :=
          ⟨profile6q0Point s 2, hpts 2, profile6q0Point s 3, hpts 3, profile6q0Point s 0, hpts 0,
              hb0_0, hb0_1⟩
        have hd1 := arithmeticBound12 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) (((9 / 10) + ((-33
            / 25) * s)), ((1 / 10) + ((81 / 50) * s))) :=
          ⟨profile6q0Point s 2, hpts 2, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
              hb1_0, hb1_1⟩
        have hd2 := arithmeticBound15 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound16 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound17 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1)
            :=
          ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
              hb2_0, hb2_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
              hb2_1⟩
        apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)), (((9
            / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
      · have hl : 0 ≤ s - (3 / 80) := by
          linarith
        have hh : 0 ≤ (1 / 20) - s := by
          linarith
        have hd0 := arithmeticBound18 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound19 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound20 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s)))
            :=
          ⟨profile6q0Point s 2, hpts 2, profile6q0Point s 3, hpts 3, profile6q0Point s 0, hpts 0,
              hb0_0, hb0_1⟩
        have hd1 := arithmeticBound21 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound22 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound23 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q (((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1)
            :=
          ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
              hb1_0, hb1_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0,
              hb1_1⟩
        apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-33 / 25) * s)), ((1 / 10) + ((81 / 50) *
            s))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩
  · have hl : 0 ≤ s - (1 / 20) := by
      linarith
    have hh : 0 ≤ (1 / 10) - s := by
      linarith
    have hd0 := arithmeticBound24 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound25 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound26 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) :=
      ⟨profile6q0Point s 2, hpts 2, profile6q0Point s 3, hpts 3, profile6q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound27 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound28 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound29 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)) (-1, 1) :=
      ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile6q0Point s 3, hpts 3, profile6q0Point s 1, hpts 1, profile6q0Point s 0, hpts 0, hb1_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-337 / 100) * s)), ((71 / 20) * s)), (-1,
        1)])
    exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
