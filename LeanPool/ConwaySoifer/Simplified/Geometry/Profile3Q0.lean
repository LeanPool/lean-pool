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

/-- The four-point configuration for profile 3, owner 0, parameterized by the minimal section. -/
def profile3q0Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, s), ((1 + ((-3 / 4) * s)), 1), (((1 / 10) + ((-9 / 50) * s)), ((9 / 10) + ((-81 /
      50) * s)))]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((14 / 5) * s) := by
    have heq : (((14 / 5) * s) : ℝ) = s ^ 1 * ((14 / 5)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile3q0Point s 2) (profile3q0Point s 3) (profile3q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile3q0Point s 2)
        (profile3q0Point s 3) (profile3q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s)) ≤ supportNum (((9 / 10) + ((-131 / 50) *
        s)), ((14 / 5) * s)) (profile3q0Point s 2) (profile3q0Point s 3) (profile3q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-18 / 25) * s) + ((48 / 25) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-18 / 25) * s) + ((48 / 25) * (s ^ 2))) : ℝ) = ((543 / 625) + (312 /
          25) * ((1 / 20) - s) ^ 2 + (264 / 25) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-1728 / 625) * (s ^ 3)) + ((-1697 / 500) * (s ^ 2)) + ((9 / 10) * s) +
      ((2304 / 625) * (s ^ 4))) := by
      have heq : ((((-1728 / 625) * (s ^ 3)) + ((-1697 / 500) * (s ^ 2)) + ((9 / 10) * s) + ((2304 /
          625) * (s ^ 4))) : ℝ) = s ^ 1 * ((904811 / 1250000) + (880756 / 625) * ((1 / 20) - s) ^ 3
          + (1793768 / 625) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 2 + (910708 / 625) * (s - 0) ^ 2 * ((1
          / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-1728 / 625) * (s ^ 3)) + ((-1697 / 500) * (s ^ 2)) + ((9 / 10) * s) + ((2304 /
        625) * (s ^ 4))) = (supportNum (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s))
        (profile3q0Point s 2) (profile3q0Point s 3) (profile3q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-131 / 50) * s)), ((14 / 5) * s)) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s)) (((9 / 10) + ((-57 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-6621 / 2500) * (s ^ 2)) + ((-331 / 250) * s)) := by
    have heq : (((9 / 100) + ((-6621 / 2500) * (s ^ 2)) + ((-331 / 250) * s)) : ℝ) = ((17179 /
        1000000) + (72821 / 2500) * ((1 / 20) - s) ^ 2 + (39721 / 1250) * (s - 0) ^ 1 * ((1 / 20) -
        s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s)) ≤ supportNum (((9 / 10) + ((-131 / 50) *
        s)), ((14 / 5) * s)) (profile3q0Point s 2) (profile3q0Point s 1) (profile3q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-18 / 25) * s) + ((48 / 25) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-18 / 25) * s) + ((48 / 25) * (s ^ 2))) : ℝ) = ((543 / 625) + (312 /
          25) * ((1 / 20) - s) ^ 2 + (264 / 25) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-1728 / 625) * (s ^ 3)) + ((-1697 / 500) * (s ^ 2)) + ((9 / 10) * s) +
      ((2304 / 625) * (s ^ 4))) := by
      have heq : ((((-1728 / 625) * (s ^ 3)) + ((-1697 / 500) * (s ^ 2)) + ((9 / 10) * s) + ((2304 /
          625) * (s ^ 4))) : ℝ) = s ^ 1 * ((904811 / 1250000) + (880756 / 625) * ((1 / 20) - s) ^ 3
          + (1793768 / 625) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 2 + (910708 / 625) * (s - 0) ^ 2 * ((1
          / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-1728 / 625) * (s ^ 3)) + ((-1697 / 500) * (s ^ 2)) + ((9 / 10) * s) + ((2304 /
        625) * (s ^ 4))) = (supportNum (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s))
        (profile3q0Point s 2) (profile3q0Point s 1) (profile3q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-131 / 50) * s)), ((14 / 5) * s)) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile3q0Point s 2) (profile3q0Point s
        1) (profile3q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 8) * s) + ((33 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((1 / 8) * s) + ((33 / 200) * (s ^ 2))) : ℝ) = (1 + (5 / 2) * (s - 0) ^ 1 *
          ((1 / 20) - s) ^ 1 + (533 / 200) * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 /
      800) * (s ^ 3)) + ((1089 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 / 800) * (s
          ^ 3)) + ((1089 / 40000) * (s ^ 4))) : ℝ) = ((405469689 / 6400000000) + (170530311 / 40000)
          * ((1 / 20) - s) ^ 4 + (134610311 / 10000) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 3 + (282628733
          / 20000) * (s - 0) ^ 2 * ((1 / 20) - s) ^ 2 + (49336361 / 10000) * (s - 0) ^ 3 * ((1 / 20)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 / 800) * (s ^
        3)) + ((1089 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile3q0Point s 2) (profile3q0Point s 1) (profile3q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((21 / 20) * s)) := by
    have heq : ((1 + ((21 / 20) * s)) : ℝ) = (1 + (21 / 20) * (s - 0) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile3q0Point s 3) (profile3q0Point s
        1) (profile3q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 8) * s) + ((33 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((1 / 8) * s) + ((33 / 200) * (s ^ 2))) : ℝ) = (1 + (5 / 2) * (s - 0) ^ 1 *
          ((1 / 20) - s) ^ 1 + (533 / 200) * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 /
      800) * (s ^ 3)) + ((1089 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 / 800) * (s
          ^ 3)) + ((1089 / 40000) * (s ^ 4))) : ℝ) = ((405469689 / 6400000000) + (170530311 / 40000)
          * ((1 / 20) - s) ^ 4 + (134610311 / 10000) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 3 + (282628733
          / 20000) * (s - 0) ^ 2 * ((1 / 20) - s) ^ 2 + (49336361 / 10000) * (s - 0) ^ 3 * ((1 / 20)
          - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 / 800) * (s ^
        3)) + ((1089 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile3q0Point s 3) (profile3q0Point s 1) (profile3q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile3q0Point s 3) (profile3q0Point s 1) (profile3q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile3q0Point s 3)
        (profile3q0Point s 1) (profile3q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((1 / 10) + ((81 / 50) * s)) := by
    have heq : (((1 / 10) + ((81 / 50) * s)) : ℝ) = ((181 / 1000) + (81 / 50) * (s - (1 / 20)) ^ 1)
        := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile3q0Point s 2) (profile3q0Point s 3) (profile3q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile3q0Point s 2)
        (profile3q0Point s 3) (profile3q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile3q0Point s 2) (profile3q0Point s
        3) (profile3q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((91 / 100) + ((1449 / 1000) * s) + ((14067 / 5000) * (s ^ 2))) := by
      have heq : (((91 / 100) + ((1449 / 1000) * s) + ((14067 / 5000) * (s ^ 2))) : ℝ) = ((1978967 /
          2000000) + (86517 / 2500) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1 + (187101 / 5000) * (s
          - (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-819 / 10000) + ((96909 / 50000) * s) + ((5194089 / 1000000) * (s ^ 2)) +
      ((20383083 / 2500000) * (s ^ 3)) + ((197880489 / 25000000) * (s ^ 4))) := by
      have heq : (((-819 / 10000) + ((96909 / 50000) * s) + ((5194089 / 1000000) * (s ^ 2)) +
          ((20383083 / 2500000) * (s ^ 3)) + ((197880489 / 25000000) * (s ^ 4))) : ℝ) =
          ((116251387089 / 4000000000000) + (126134787939 / 6250000) * (s - (1 / 20)) ^ 1 * ((1 /
          10) - s) ^ 3 + (789487739001 / 12500000) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 2 +
          (412300409823 / 6250000) * (s - (1 / 20)) ^ 3 * ((1 / 10) - s) ^ 1 + (114992638707 /
          5000000) * (s - (1 / 20)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-819 / 10000) + ((96909 / 50000) * s) + ((5194089 / 1000000) * (s ^ 2)) +
        ((20383083 / 2500000) * (s ^ 3)) + ((197880489 / 25000000) * (s ^ 4))) = (supportNum (((9 /
        10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile3q0Point s 2)
        (profile3q0Point s 3) (profile3q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-57 / 100) * s)),
        ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((21 / 20) * s)) := by
    have heq : ((1 + ((21 / 20) * s)) : ℝ) = ((421 / 400) + (21 / 20) * (s - (1 / 20)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile3q0Point s 3) (profile3q0Point s
        1) (profile3q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((1 / 8) * s) + ((33 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((1 / 8) * s) + ((33 / 200) * (s ^ 2))) : ℝ) = ((80533 / 80000) + (283 / 100)
          * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1 + (599 / 200) * (s - (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 /
      800) * (s ^ 3)) + ((1089 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 / 800) * (s
          ^ 3)) + ((1089 / 40000) * (s ^ 4))) : ℝ) = ((11336489 / 400000000) + (44817173 / 8000) *
          ((1 / 10) - s) ^ 4 + (10921844 / 625) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 3 +
          (90712499 / 5000) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 2 + (3918543 / 625) * (s - (1 /
          20)) ^ 3 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-67211 / 40000) * (s ^ 2)) + ((-449 / 1000) * s) + ((33 / 800) * (s ^
        3)) + ((1089 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) +
        ((81 / 50) * s))) (profile3q0Point s 3) (profile3q0Point s 1) (profile3q0Point s 0)) ^ 2 -
        normSq (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile3q0Point s 3) (profile3q0Point s 1) (profile3q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile3q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile3q0Point s 3)
        (profile3q0Point s 1) (profile3q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile3q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem profile3q0_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile3q0Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 20)
  · have hl : 0 ≤ s - 0 := by
      linarith
    have hh : 0 ≤ (1 / 20) - s := by
      linarith
    have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s)) :=
      ⟨profile3q0Point s 2, hpts 2, profile3q0Point s 3, hpts 3, profile3q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s)) (((9 / 10) + ((-57 /
        100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
      ⟨profile3q0Point s 2, hpts 2, profile3q0Point s 1, hpts 1, profile3q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
    have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
    have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
    have hc2 : ConeBound Q (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) :=
      ⟨profile3q0Point s 3, hpts 3, profile3q0Point s 1, hpts 1, profile3q0Point s 0, hpts 0, hb2_0,
          hb2_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile3q0Point s 3, hpts 3, profile3q0Point s 1, hpts 1, profile3q0Point s 0, hpts 0, hb2_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-131 / 50) * s)), ((14 / 5) * s)), (((9 / 10)
        + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
  · have hl : 0 ≤ s - (1 / 20) := by
      linarith
    have hh : 0 ≤ (1 / 10) - s := by
      linarith
    have hd0 := arithmeticBound9 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
      ⟨profile3q0Point s 2, hpts 2, profile3q0Point s 3, hpts 3, profile3q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound12 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) :=
      ⟨profile3q0Point s 3, hpts 3, profile3q0Point s 1, hpts 1, profile3q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile3q0Point s 3, hpts 3, profile3q0Point s 1, hpts 1, profile3q0Point s 0, hpts 0, hb1_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-57 / 100) * s)), ((1 / 10) + ((81 / 50) *
        s))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
