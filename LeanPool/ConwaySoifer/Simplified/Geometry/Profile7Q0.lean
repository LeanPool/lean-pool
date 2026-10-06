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

/-- The four-point configuration for profile 7, owner 0, parameterized by the minimal section. -/
def profile7q0Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, (2 * s)), ((1 + ((-7 / 4) * s)), 1), (((1 / 10) + ((-9 / 50) * s)), ((9 / 10) +
      ((-81 / 50) * s)))]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((19 / 5) * s) := by
    have heq : (((19 / 5) * s) : ℝ) = s ^ 1 * ((19 / 5)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile7q0Point s 2)
        (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) : ℝ) = ((138149 / 160000)
          + (5851 / 100) * ((1 / 40) - s) ^ 2 + (2611 / 50) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) +
      ((395641 / 10000) * (s ^ 4))) := by
      have heq : ((((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641
          / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((109971801 / 640000000) + (5228199 / 10000) * ((1 /
          40) - s) ^ 3 + (18212597 / 10000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 2 + (12588757 / 10000)
          * (s - 0) ^ 2 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641 /
        10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s))
        (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (((9 / 10) + ((-157 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-581 / 250) * s) + ((127 / 1250) * (s ^ 2))) := by
    have heq : (((9 / 100) + ((-581 / 250) * s) + ((127 / 1250) * (s ^ 2))) : ℝ) = ((63927 /
        2000000) + (116073 / 1250) * ((1 / 40) - s) ^ 2 + (57973 / 625) * (s - 0) ^ 1 * ((1 / 40) -
        s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 2) (profile7q0Point s 1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) : ℝ) = ((138149 / 160000)
          + (5851 / 100) * ((1 / 40) - s) ^ 2 + (2611 / 50) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) +
      ((395641 / 10000) * (s ^ 4))) := by
      have heq : ((((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641
          / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((109971801 / 640000000) + (5228199 / 10000) * ((1 /
          40) - s) ^ 3 + (18212597 / 10000) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 2 + (12588757 / 10000)
          * (s - 0) ^ 2 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641 /
        10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s))
        (profile7q0Point s 2) (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile7q0Point s 2) (profile7q0Point s
        1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) : ℝ) = ((306347 / 320000) +
          (13653 / 200) * ((1 / 40) - s) ^ 2 + (6553 / 100) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
      40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
          40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) : ℝ) = ((3576106809 / 102400000000) +
          (5639893191 / 40000) * ((1 / 40) - s) ^ 4 + (4136533191 / 10000) * (s - 0) ^ 1 * ((1 / 40)
          - s) ^ 3 + (8093910773 / 20000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 2 + (1320320691 / 10000)
          * (s - 0) ^ 3 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 / 40000) *
        (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-157 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) (profile7q0Point s 2) (profile7q0Point s 1) (profile7q0Point s 0))
        ^ 2 - normSq (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    0 < cross (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((1 / 20) * s)) := by
    have heq : ((1 + ((1 / 20) * s)) : ℝ) = (1 + (1 / 20) * (s - 0) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile7q0Point s 3) (profile7q0Point s
        1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) : ℝ) = ((306347 / 320000) +
          (13653 / 200) * ((1 / 40) - s) ^ 2 + (6553 / 100) * (s - 0) ^ 1 * ((1 / 40) - s) ^ 1) :=
          by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
      40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
          40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) : ℝ) = ((3576106809 / 102400000000) +
          (5639893191 / 40000) * ((1 / 40) - s) ^ 4 + (4136533191 / 10000) * (s - 0) ^ 1 * ((1 / 40)
          - s) ^ 3 + (8093910773 / 20000) * (s - 0) ^ 2 * ((1 / 40) - s) ^ 2 + (1320320691 / 10000)
          * (s - 0) ^ 3 * ((1 / 40) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 / 40000) *
        (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-157 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s 0))
        ^ 2 - normSq (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 40) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile7q0Point s 3)
        (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((19 / 5) * s) := by
    have heq : (((19 / 5) * s) : ℝ) = s ^ 1 * ((19 / 5)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((209 / 200) + (9 / 5) * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3681 / 1000) + (81 / 25)
          * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile7q0Point s 2)
        (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) : ℝ) = ((542781 / 640000)
          + (1963 / 20) * ((3 / 80) - s) ^ 2 + (4593 / 50) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^
          1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) +
      ((395641 / 10000) * (s ^ 4))) := by
      have heq : ((((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641
          / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((815885187 / 5120000000) + (63889221 / 10000) * ((3 /
          80) - s) ^ 3 + (28262527 / 2000) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 2 + (77027773 /
          10000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641 /
        10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s))
        (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (((9 / 10) + ((-157 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-581 / 250) * s) + ((127 / 1250) * (s ^ 2))) := by
    have heq : (((9 / 100) + ((-581 / 250) * s) + ((127 / 1250) * (s ^ 2))) : ℝ) = ((23943 /
        8000000) + (46353 / 250) * ((3 / 80) - s) ^ 2 + (115819 / 625) * (s - (1 / 40)) ^ 1 * ((3 /
        80) - s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 2) (profile7q0Point s 1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) : ℝ) = ((542781 / 640000)
          + (1963 / 20) * ((3 / 80) - s) ^ 2 + (4593 / 50) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^
          1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) +
      ((395641 / 10000) * (s ^ 4))) := by
      have heq : ((((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641
          / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((815885187 / 5120000000) + (63889221 / 10000) * ((3 /
          80) - s) ^ 3 + (28262527 / 2000) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^ 2 + (77027773 /
          10000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641 /
        10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s))
        (profile7q0Point s 2) (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile7q0Point s 2) (profile7q0Point s
        1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) : ℝ) = ((1199723 / 1280000) +
          (5133 / 40) * ((3 / 80) - s) ^ 2 + (12559 / 100) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^
          1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
      40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
          40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) : ℝ) = ((16314963129 / 1638400000000) +
          (8180549163 / 8000) * ((3 / 80) - s) ^ 4 + (30340180287 / 10000) * (s - (1 / 40)) ^ 1 *
          ((3 / 80) - s) ^ 3 + (12004158157 / 4000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 2 +
          (9895826757 / 10000) * (s - (1 / 40)) ^ 3 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 / 40000) *
        (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-157 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) (profile7q0Point s 2) (profile7q0Point s 1) (profile7q0Point s 0))
        ^ 2 - normSq (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    0 < cross (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((1 / 20) * s)) := by
    have heq : ((1 + ((1 / 20) * s)) : ℝ) = ((801 / 800) + (1 / 20) * (s - (1 / 40)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile7q0Point s 3) (profile7q0Point s
        1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) : ℝ) = ((1199723 / 1280000) +
          (5133 / 40) * ((3 / 80) - s) ^ 2 + (12559 / 100) * (s - (1 / 40)) ^ 1 * ((3 / 80) - s) ^
          1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
      40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
          40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) : ℝ) = ((16314963129 / 1638400000000) +
          (8180549163 / 8000) * ((3 / 80) - s) ^ 4 + (30340180287 / 10000) * (s - (1 / 40)) ^ 1 *
          ((3 / 80) - s) ^ 3 + (12004158157 / 4000) * (s - (1 / 40)) ^ 2 * ((3 / 80) - s) ^ 2 +
          (9895826757 / 10000) * (s - (1 / 40)) ^ 3 * ((3 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 / 40000) *
        (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-157 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s 0))
        ^ 2 - normSq (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 40) ∧ 0 ≤ (3 / 80) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((209 / 200) + (9 / 5) * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3681 / 1000) + (81 / 25)
          * (s - (1 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile7q0Point s 3)
        (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (13 / 320) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((1 / 10) + ((81 / 50) * s)) := by
    have heq : (((1 / 10) + ((81 / 50) * s)) : ℝ) = ((643 / 4000) + (81 / 50) * (s - (3 / 80)) ^ 1)
        := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound19 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (13 / 320) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((427 / 400) + (9 / 5) * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((7443 / 2000) + (81 / 25)
          * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile7q0Point s 2)
        (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (13 / 320) - s) :
    len (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile7q0Point s 2) (profile7q0Point s
        3) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((91 / 100) + ((549 / 1000) * s) + ((13167 / 5000) * (s ^ 2))) := by
      have heq : (((91 / 100) + ((549 / 1000) * s) + ((13167 / 5000) * (s ^ 2))) : ℝ) = ((29897303 /
          32000000) + (149301 / 625) * (s - (3 / 80)) ^ 1 * ((13 / 320) - s) ^ 1 + (48303 / 200) *
          (s - (3 / 80)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-819 / 10000) + ((110009 / 50000) * s) + ((2548289 / 1000000) * (s ^ 2)) +
      ((7228683 / 2500000) * (s ^ 3)) + ((173369889 / 25000000) * (s ^ 4))) := by
      have heq : (((-819 / 10000) + ((110009 / 50000) * s) + ((2548289 / 1000000) * (s ^ 2)) +
          ((7228683 / 2500000) * (s ^ 3)) + ((173369889 / 25000000) * (s ^ 4))) : ℝ) =
          ((4461030673809 / 1024000000000000) + (30783524940812 / 390625) * (s - (3 / 80)) ^ 1 *
          ((13 / 320) - s) ^ 3 + (7397428680427 / 31250) * (s - (3 / 80)) ^ 2 * ((13 / 320) - s) ^ 2
          + (370342534599223 / 1562500) * (s - (3 / 80)) ^ 3 * ((13 / 320) - s) ^ 1 +
          (79107335153113 / 1000000) * (s - (3 / 80)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-819 / 10000) + ((110009 / 50000) * s) + ((2548289 / 1000000) * (s ^ 2)) +
        ((7228683 / 2500000) * (s ^ 3)) + ((173369889 / 25000000) * (s ^ 4))) = (supportNum (((9 /
        10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile7q0Point s 2)
        (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-157 / 100) * s)),
        ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound21 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (13 / 320) - s) :
    0 < cross (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((1 / 20) * s)) := by
    have heq : ((1 + ((1 / 20) * s)) : ℝ) = ((1603 / 1600) + (1 / 20) * (s - (3 / 80)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound22 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (13 / 320) - s) :
    len (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) +
        ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile7q0Point s 3) (profile7q0Point s
        1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) := by
      have heq : ((1 + ((-71 / 40) * s) + ((547 / 200) * (s ^ 2))) : ℝ) = ((19095643 / 20480000) +
          (3997 / 8) * ((13 / 320) - s) ^ 2 + (49689 / 100) * (s - (3 / 80)) ^ 1 * ((13 / 320) - s)
          ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
      40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 /
          40000) * (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) : ℝ) = ((1663855861849 /
          419430400000000) + (100510987967 / 1600) * ((13 / 320) - s) ^ 4 + (1879441786727 / 10000)
          * (s - (3 / 80)) ^ 1 * ((13 / 320) - s) ^ 3 + (149946396269 / 800) * (s - (3 / 80)) ^ 2 *
          ((13 / 320) - s) ^ 2 + (623081766627 / 10000) * (s - (3 / 80)) ^ 3 * ((13 / 320) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-38837 / 4000) * (s ^ 3)) + ((-2349 / 1000) * s) + ((242989 / 40000) *
        (s ^ 2)) + ((299209 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-157 / 100) * s)), ((1
        / 10) + ((81 / 50) * s))) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s 0))
        ^ 2 - normSq (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound23 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 80) ∧ 0 ≤ (13 / 320) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((427 / 400) + (9 / 5) * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((7443 / 2000) + (81 / 25)
          * (s - (3 / 80)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile7q0Point s 3)
        (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound24 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (13 / 320) ∧ 0 ≤ (7 / 160) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((19 / 5) * s) := by
    have heq : (((19 / 5) * s) : ℝ) = s ^ 1 * ((19 / 5)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound25 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (13 / 320) ∧ 0 ≤ (7 / 160) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((1717 / 1600) + (9 / 5) * (s - (13 / 320)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((29853 / 8000) + (81 /
          25) * (s - (13 / 320)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile7q0Point s 2)
        (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound26 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (13 / 320) ∧ 0 ≤ (7 / 160) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) : ℝ) = ((2153381 /
          2560000) + (34857 / 100) * ((7 / 160) - s) ^ 2 + (8557 / 25) * (s - (13 / 320)) ^ 1 * ((7
          / 160) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) +
      ((395641 / 10000) * (s ^ 4))) := by
      have heq : ((((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641
          / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((6193880223 / 40960000000) + (1382589813 / 10000) *
          ((7 / 160) - s) ^ 3 + (1407284353 / 5000) * (s - (13 / 320)) ^ 1 * ((7 / 160) - s) ^ 2 +
          (357895813 / 2500) * (s - (13 / 320)) ^ 2 * ((7 / 160) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641 /
        10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s))
        (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound27 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (13 / 320) ∧ 0 ≤ (7 / 160) - s) :
    0 < cross (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 10) + ((9 / 50) * s)) := by
    have heq : (((9 / 10) + ((9 / 50) * s)) : ℝ) = ((14517 / 16000) + (9 / 50) * (s - (13 / 320)) ^
        1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound28 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (13 / 320) ∧ 0 ≤ (7 / 160) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((81 / 100) + ((88 / 125) * s) + ((15471 / 2500) * (s ^ 2))) := by
      have heq : (((81 / 100) + ((88 / 125) * s) + ((15471 / 2500) * (s ^ 2))) : ℝ) = ((217296199 /
          256000000) + (482723 / 1250) * (s - (13 / 320)) ^ 1 * ((7 / 160) - s) ^ 1 + (980917 /
          2500) * (s - (13 / 320)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) +
      ((680724 / 78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) := by
      have heq : (((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) +
          ((680724 / 78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) : ℝ) = ((884915155847601
          / 65536000000000000) + (206049329069877 / 1562500) * (s - (13 / 320)) ^ 1 * ((7 / 160) -
          s) ^ 3 + (1235711518903449 / 3125000) * (s - (13 / 320)) ^ 2 * ((7 / 160) - s) ^ 2 +
          (617570999901351 / 1562500) * (s - (13 / 320)) ^ 3 * ((7 / 160) - s) ^ 1 +
          (164611703485971 / 1250000) * (s - (13 / 320)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) + ((680724 /
        78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 /
        50) * s)), ((19 / 5) * s)) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0)) ^ 2 - normSq (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound29 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (13 / 320) ∧ 0 ≤ (7 / 160) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((1717 / 1600) + (9 / 5) * (s - (13 / 320)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((29853 / 8000) + (81 /
          25) * (s - (13 / 320)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile7q0Point s 3)
        (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound30 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 160) ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((19 / 5) * s) := by
    have heq : (((19 / 5) * s) : ℝ) = s ^ 1 * ((19 / 5)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound31 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 160) ∧ 0 ≤ (1 / 20) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((863 / 800) + (9 / 5) * (s - (7 / 160)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((14967 / 4000) + (81 /
          25) * (s - (7 / 160)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile7q0Point s 2)
        (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound32 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 160) ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) : ℝ) = ((33389 / 40000) +
          (3297 / 20) * ((1 / 20) - s) ^ 2 + (3964 / 25) * (s - (7 / 160)) ^ 1 * ((1 / 20) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) +
      ((395641 / 10000) * (s ^ 4))) := by
      have heq : ((((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641
          / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((11351721 / 80000000) + (381799071 / 10000) * ((1 /
          20) - s) ^ 3 + (3937507 / 50) * (s - (7 / 160)) ^ 1 * ((1 / 20) - s) ^ 2 + (25331668 /
          625) * (s - (7 / 160)) ^ 2 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641 /
        10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s))
        (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound33 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 160) ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 10) + ((9 / 50) * s)) := by
    have heq : (((9 / 10) + ((9 / 50) * s)) : ℝ) = ((7263 / 8000) + (9 / 50) * (s - (7 / 160)) ^ 1)
        := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound34 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 160) ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((81 / 100) + ((88 / 125) * s) + ((15471 / 2500) * (s ^ 2))) := by
      have heq : (((81 / 100) + ((88 / 125) * s) + ((15471 / 2500) * (s ^ 2))) : ℝ) = ((54569279 /
          64000000) + (249097 / 1250) * (s - (7 / 160)) ^ 1 * ((1 / 20) - s) ^ 1 + (102733 / 500) *
          (s - (7 / 160)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) +
      ((680724 / 78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) := by
      have heq : (((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) +
          ((680724 / 78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) : ℝ) = ((106748354579841
          / 4096000000000000) + (25685939691063 / 1562500) * (s - (7 / 160)) ^ 1 * ((1 / 20) - s) ^
          3 + (30796181218521 / 625000) * (s - (7 / 160)) ^ 2 * ((1 / 20) - s) ^ 2 + (76926940799103
          / 1562500) * (s - (7 / 160)) ^ 3 * ((1 / 20) - s) ^ 1 + (20497989825459 / 1250000) * (s -
          (7 / 160)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) + ((680724 /
        78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 /
        50) * s)), ((19 / 5) * s)) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0)) ^ 2 - normSq (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound35 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 160) ∧ 0 ≤ (1 / 20) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((863 / 800) + (9 / 5) * (s - (7 / 160)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((14967 / 4000) + (81 /
          25) * (s - (7 / 160)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile7q0Point s 3)
        (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound36 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((19 / 5) * s) := by
    have heq : (((19 / 5) * s) : ℝ) = s ^ 1 * ((19 / 5)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound37 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile7q0Point s 2)
        (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound38 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-81 / 50) * s) + ((629 / 100) * (s ^ 2))) : ℝ) = ((8009 / 10000) +
          (1353 / 100) * ((1 / 10) - s) ^ 2 + (181 / 25) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1)
          := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) +
      ((395641 / 10000) * (s ^ 4))) := by
      have heq : ((((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641
          / 10000) * (s ^ 4))) : ℝ) = s ^ 1 * ((315681 / 10000000) + (8826273 / 10000) * ((1 / 10) -
          s) ^ 3 + (10072951 / 5000) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 2 + (2730997 / 2500) *
          (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-50949 / 2500) * (s ^ 3)) + ((9 / 50) * s) + ((79 / 500) * (s ^ 2)) + ((395641 /
        10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s))
        (profile7q0Point s 2) (profile7q0Point s 3) (profile7q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound39 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 10) + ((9 / 50) * s)) := by
    have heq : (((9 / 10) + ((9 / 50) * s)) : ℝ) = ((909 / 1000) + (9 / 50) * (s - (1 / 20)) ^ 1) :=
        by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound40 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) ≤ supportNum (((9 / 10) + ((-181 / 50) *
        s)), ((19 / 5) * s)) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((81 / 100) + ((88 / 125) * s) + ((15471 / 2500) * (s ^ 2))) := by
      have heq : (((81 / 100) + ((88 / 125) * s) + ((15471 / 2500) * (s ^ 2))) : ℝ) = ((860671 /
          1000000) + (33071 / 1250) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1 + (81613 / 2500) * (s
          - (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) +
      ((680724 / 78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) := by
      have heq : (((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) +
          ((680724 / 78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) : ℝ) = ((51083570241 /
          1000000000000) + (49927750641 / 1562500) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 3 +
          (297833826969 / 3125000) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 2 + (148562216487 /
          1562500) * (s - (1 / 20)) ^ 3 * ((1 / 10) - s) ^ 1 + (39706313283 / 1250000) * (s - (1 /
          20)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-1539 / 10000) + ((-408447 / 125000) * (s ^ 2)) + ((13239 / 3125) * s) + ((680724 /
        78125) * (s ^ 3)) + ((239351841 / 6250000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-181 /
        50) * s)), ((19 / 5) * s)) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0)) ^ 2 - normSq (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound41 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile7q0Point s 3) (profile7q0Point s 1) (profile7q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile7q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile7q0Point s 3)
        (profile7q0Point s 1) (profile7q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile7q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem profile7q0_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile7q0Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 20)
  · by_cases hsplit : s ≤ (1 / 40)
    · have hl : 0 ≤ s - 0 := by
        linarith
      have hh : 0 ≤ (1 / 40) - s := by
        linarith
      have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) :=
        ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 3, hpts 3, profile7q0Point s 0, hpts 0,
            hb0_0, hb0_1⟩
      have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (((9 / 10) + ((-157 /
          100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
        ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
            hb1_0, hb1_1⟩
      have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
      have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
      have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
      have hc2 : ConeBound Q (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1)
          :=
        ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
            hb2_0, hb2_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
            hb2_1⟩
      apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)), (((9 /
          10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
    · by_cases hsplit : s ≤ (3 / 80)
      · have hl : 0 ≤ s - (1 / 40) := by
          linarith
        have hh : 0 ≤ (3 / 80) - s := by
          linarith
        have hd0 := arithmeticBound9 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) :=
          ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 3, hpts 3, profile7q0Point s 0, hpts 0,
              hb0_0, hb0_1⟩
        have hd1 := arithmeticBound12 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (((9 / 10) + ((-157
            / 100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
          ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
              hb1_0, hb1_1⟩
        have hd2 := arithmeticBound15 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound16 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound17 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1,
            1) :=
          ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
              hb2_0, hb2_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
              hb2_1⟩
        apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)), (((9 /
            10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
      · by_cases hsplit : s ≤ (7 / 160)
        · by_cases hsplit : s ≤ (13 / 320)
          · have hl : 0 ≤ s - (3 / 80) := by
              linarith
            have hh : 0 ≤ (13 / 320) - s := by
              linarith
            have hd0 := arithmeticBound18 ⟨hs0, hl, hh⟩
            have hb0_0 := arithmeticBound19 ⟨hs0, hl, hh⟩
            have hb0_1 := arithmeticBound20 ⟨hs0, hl, hh⟩
            have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) *
                s))) :=
              ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 3, hpts 3, profile7q0Point s 0, hpts
                  0, hb0_0, hb0_1⟩
            have hd1 := arithmeticBound21 ⟨hs0, hl, hh⟩
            have hb1_0 := arithmeticBound22 ⟨hs0, hl, hh⟩
            have hb1_1 := arithmeticBound23 ⟨hs0, hl, hh⟩
            have hc1 : ConeBound Q (((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 / 50) * s)))
                (-1, 1) :=
              ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts
                  0, hb1_0, hb1_1⟩
            have hend : SupportBound Q (-1, 1) :=
              ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts
                  0, hb1_1⟩
            apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-157 / 100) * s)), ((1 / 10) + ((81 /
                50) * s))), (-1, 1)])
            exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩
          · have hl : 0 ≤ s - (13 / 320) := by
              linarith
            have hh : 0 ≤ (7 / 160) - s := by
              linarith
            have hd0 := arithmeticBound24 ⟨hs0, hl, hh⟩
            have hb0_0 := arithmeticBound25 ⟨hs0, hl, hh⟩
            have hb0_1 := arithmeticBound26 ⟨hs0, hl, hh⟩
            have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) :=
              ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 3, hpts 3, profile7q0Point s 0, hpts
                  0, hb0_0, hb0_1⟩
            have hd1 := arithmeticBound27 ⟨hs0, hl, hh⟩
            have hb1_0 := arithmeticBound28 ⟨hs0, hl, hh⟩
            have hb1_1 := arithmeticBound29 ⟨hs0, hl, hh⟩
            have hc1 : ConeBound Q (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (-1, 1) :=
              ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts
                  0, hb1_0, hb1_1⟩
            have hend : SupportBound Q (-1, 1) :=
              ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts
                  0, hb1_1⟩
            apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)),
                (-1, 1)])
            exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩
        · have hl : 0 ≤ s - (7 / 160) := by
            linarith
          have hh : 0 ≤ (1 / 20) - s := by
            linarith
          have hd0 := arithmeticBound30 ⟨hs0, hl, hh⟩
          have hb0_0 := arithmeticBound31 ⟨hs0, hl, hh⟩
          have hb0_1 := arithmeticBound32 ⟨hs0, hl, hh⟩
          have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) :=
            ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 3, hpts 3, profile7q0Point s 0, hpts 0,
                hb0_0, hb0_1⟩
          have hd1 := arithmeticBound33 ⟨hs0, hl, hh⟩
          have hb1_0 := arithmeticBound34 ⟨hs0, hl, hh⟩
          have hb1_1 := arithmeticBound35 ⟨hs0, hl, hh⟩
          have hc1 : ConeBound Q (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (-1, 1) :=
            ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
                hb1_0, hb1_1⟩
          have hend : SupportBound Q (-1, 1) :=
            ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0,
                hb1_1⟩
          apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)), (-1,
              1)])
          exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩
  · have hl : 0 ≤ s - (1 / 20) := by
      linarith
    have hh : 0 ≤ (1 / 10) - s := by
      linarith
    have hd0 := arithmeticBound36 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound37 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound38 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) :=
      ⟨profile7q0Point s 2, hpts 2, profile7q0Point s 3, hpts 3, profile7q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound39 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound40 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound41 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)) (-1, 1) :=
      ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile7q0Point s 3, hpts 3, profile7q0Point s 1, hpts 1, profile7q0Point s 0, hpts 0, hb1_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-181 / 50) * s)), ((19 / 5) * s)), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
