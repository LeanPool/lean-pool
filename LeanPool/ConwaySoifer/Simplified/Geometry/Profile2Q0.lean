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

/-- The four-point configuration for profile 2, owner 0, parameterized by the minimal section. -/
def profile2q0Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, ((3 / 4) * s)), ((1 + ((-1 / 2) * s)), 1), (((1 / 10) + ((-9 / 50) * s)), ((9 / 10)
      + ((-81 / 50) * s)))]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((51 / 20) * s) := by
    have heq : (((51 / 20) * s) : ℝ) = s ^ 1 * ((51 / 20)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile2q0Point s 2) (profile2q0Point s 3) (profile2q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile2q0Point s 2)
        (profile2q0Point s 3) (profile2q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s)) ≤ supportNum (((9 / 10) + ((-237 / 100) *
        s)), ((51 / 20) * s)) (profile2q0Point s 2) (profile2q0Point s 3) (profile2q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-99 / 200) * s) + ((57 / 50) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-99 / 200) * s) + ((57 / 50) * (s ^ 2))) : ℝ) = ((8781 / 10000) +
          (219 / 25) * ((1 / 20) - s) ^ 2 + (381 / 50) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-30231 / 8000) * (s ^ 2)) + ((-5643 / 5000) * (s ^ 3)) + ((27 / 25) * s)
      + ((3249 / 2500) * (s ^ 4))) := by
      have heq : ((((-30231 / 8000) * (s ^ 2)) + ((-5643 / 5000) * (s ^ 3)) + ((27 / 25) * s) +
          ((3249 / 2500) * (s ^ 4))) : ℝ) = s ^ 1 * ((2220993 / 2500000) + (958014 / 625) * ((1 /
          20) - s) ^ 3 + (7717293 / 2500) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 2 + (970497 / 625) * (s -
          0) ^ 2 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-30231 / 8000) * (s ^ 2)) + ((-5643 / 5000) * (s ^ 3)) + ((27 / 25) * s) + ((3249
        / 2500) * (s ^ 4))) = (supportNum (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s))
        (profile2q0Point s 2) (profile2q0Point s 3) (profile2q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-237 / 100) * s)), ((51 / 20) * s)) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s)) (((9 / 10) + ((-8 / 25) * s)), ((1
        / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-15117 / 5000) * (s ^ 2)) + ((-537 / 500) * s)) := by
    have heq : (((9 / 100) + ((-15117 / 5000) * (s ^ 2)) + ((-537 / 500) * s)) : ℝ) = ((57483 /
        2000000) + (122517 / 5000) * ((1 / 20) - s) ^ 2 + (68817 / 2500) * (s - 0) ^ 1 * ((1 / 20) -
        s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s)) ≤ supportNum (((9 / 10) + ((-237 / 100) *
        s)), ((51 / 20) * s)) (profile2q0Point s 2) (profile2q0Point s 1) (profile2q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-99 / 200) * s) + ((57 / 50) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-99 / 200) * s) + ((57 / 50) * (s ^ 2))) : ℝ) = ((8781 / 10000) +
          (219 / 25) * ((1 / 20) - s) ^ 2 + (381 / 50) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-30231 / 8000) * (s ^ 2)) + ((-5643 / 5000) * (s ^ 3)) + ((27 / 25) * s)
      + ((3249 / 2500) * (s ^ 4))) := by
      have heq : ((((-30231 / 8000) * (s ^ 2)) + ((-5643 / 5000) * (s ^ 3)) + ((27 / 25) * s) +
          ((3249 / 2500) * (s ^ 4))) : ℝ) = s ^ 1 * ((2220993 / 2500000) + (958014 / 625) * ((1 /
          20) - s) ^ 3 + (7717293 / 2500) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 2 + (970497 / 625) * (s -
          0) ^ 2 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-30231 / 8000) * (s ^ 2)) + ((-5643 / 5000) * (s ^ 3)) + ((27 / 25) * s) + ((3249
        / 2500) * (s ^ 4))) = (supportNum (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s))
        (profile2q0Point s 2) (profile2q0Point s 1) (profile2q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-237 / 100) * s)), ((51 / 20) * s)) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-8
        / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile2q0Point s 2) (profile2q0Point s 1)
        (profile2q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 200) * (s ^ 2)) + ((3 / 5) * s)) := by
      have heq : ((1 + ((-33 / 200) * (s ^ 2)) + ((3 / 5) * s)) : ℝ) = (1 + 12 * (s - 0) ^ 1 * ((1 /
          20) - s) ^ 1 + (2367 / 200) * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 /
      500) * s) + ((1089 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 / 500) *
          s) + ((1089 / 40000) * (s ^ 4))) : ℝ) = ((549308289 / 6400000000) + (26691711 / 40000) *
          ((1 / 20) - s) ^ 4 + (28771711 / 10000) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 3 + (75127933 /
          20000) * (s - 0) ^ 2 * ((1 / 20) - s) ^ 2 + (15464911 / 10000) * (s - 0) ^ 3 * ((1 / 20) -
          s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 / 500) * s)
        + ((1089 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81
        / 50) * s))) (profile2q0Point s 2) (profile2q0Point s 1) (profile2q0Point s 0)) ^ 2 - normSq
        (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((13 / 10) * s)) := by
    have heq : ((1 + ((13 / 10) * s)) : ℝ) = (1 + (13 / 10) * (s - 0) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-8
        / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile2q0Point s 3) (profile2q0Point s 1)
        (profile2q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 200) * (s ^ 2)) + ((3 / 5) * s)) := by
      have heq : ((1 + ((-33 / 200) * (s ^ 2)) + ((3 / 5) * s)) : ℝ) = (1 + 12 * (s - 0) ^ 1 * ((1 /
          20) - s) ^ 1 + (2367 / 200) * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 /
      500) * s) + ((1089 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 / 500) *
          s) + ((1089 / 40000) * (s ^ 4))) : ℝ) = ((549308289 / 6400000000) + (26691711 / 40000) *
          ((1 / 20) - s) ^ 4 + (28771711 / 10000) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 3 + (75127933 /
          20000) * (s - 0) ^ 2 * ((1 / 20) - s) ^ 2 + (15464911 / 10000) * (s - 0) ^ 3 * ((1 / 20) -
          s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 / 500) * s)
        + ((1089 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81
        / 50) * s))) (profile2q0Point s 3) (profile2q0Point s 1) (profile2q0Point s 0)) ^ 2 - normSq
        (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile2q0Point s 3) (profile2q0Point s 1) (profile2q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile2q0Point s 3)
        (profile2q0Point s 1) (profile2q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
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
    len (1, 0) ≤ supportNum (1, 0) (profile2q0Point s 2) (profile2q0Point s 3) (profile2q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile2q0Point s 2)
        (profile2q0Point s 3) (profile2q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-8
        / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile2q0Point s 2) (profile2q0Point s 3)
        (profile2q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((91 / 100) + ((837 / 500) * s) + ((3573 / 1250) * (s ^ 2))) := by
      have heq : (((91 / 100) + ((837 / 500) * s) + ((3573 / 1250) * (s ^ 2))) : ℝ) = ((500423 /
          500000) + (24498 / 625) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1 + (52569 / 1250) * (s -
          (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-819 / 10000) + ((46817 / 25000) * s) + ((1449041 / 250000) * (s ^ 2)) +
      ((2990601 / 312500) * (s ^ 3)) + ((12766329 / 1562500) * (s ^ 4))) := by
      have heq : (((-819 / 10000) + ((46817 / 25000) * s) + ((1449041 / 250000) * (s ^ 2)) +
          ((2990601 / 312500) * (s ^ 3)) + ((12766329 / 1562500) * (s ^ 4))) : ℝ) = ((6867928929 /
          250000000000) + (7900487654 / 390625) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 3 +
          (49701116311 / 781250) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 2 + (26087184703 / 390625)
          * (s - (1 / 20)) ^ 3 * ((1 / 10) - s) ^ 1 + (7312244627 / 312500) * (s - (1 / 20)) ^ 4) :=
          by
        ring
      rw [heq]
      positivity
    have heq : ((-819 / 10000) + ((46817 / 25000) * s) + ((1449041 / 250000) * (s ^ 2)) + ((2990601
        / 312500) * (s ^ 3)) + ((12766329 / 1562500) * (s ^ 4))) = (supportNum (((9 / 10) + ((-8 /
        25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile2q0Point s 2) (profile2q0Point s 3)
        (profile2q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) *
        s))) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((13 / 10) * s)) := by
    have heq : ((1 + ((13 / 10) * s)) : ℝ) = ((213 / 200) + (13 / 10) * (s - (1 / 20)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-8
        / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (profile2q0Point s 3) (profile2q0Point s 1)
        (profile2q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-33 / 200) * (s ^ 2)) + ((3 / 5) * s)) := by
      have heq : ((1 + ((-33 / 200) * (s ^ 2)) + ((3 / 5) * s)) : ℝ) = ((82367 / 80000) + (1167 /
          100) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 1 + (2301 / 200) * (s - (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 /
      500) * s) + ((1089 / 40000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 / 500) *
          s) + ((1089 / 40000) * (s ^ 4))) : ℝ) = ((28248289 / 400000000) + (19467133 / 8000) * ((1
          / 10) - s) ^ 4 + (40935377 / 5000) * (s - (1 / 20)) ^ 1 * ((1 / 10) - s) ^ 3 + (45388999 /
          5000) * (s - (1 / 20)) ^ 2 * ((1 / 10) - s) ^ 2 + (4155111 / 1250) * (s - (1 / 20)) ^ 3 *
          ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-2723 / 1250) * (s ^ 2)) + ((-99 / 500) * (s ^ 3)) + ((13 / 500) * s)
        + ((1089 / 40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81
        / 50) * s))) (profile2q0Point s 3) (profile2q0Point s 1) (profile2q0Point s 0)) ^ 2 - normSq
        (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (1 / 10) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile2q0Point s 3) (profile2q0Point s 1) (profile2q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile2q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile2q0Point s 3)
        (profile2q0Point s 1) (profile2q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile2q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem profile2q0_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile2q0Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 20)
  · have hl : 0 ≤ s - 0 := by
      linarith
    have hh : 0 ≤ (1 / 20) - s := by
      linarith
    have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s)) :=
      ⟨profile2q0Point s 2, hpts 2, profile2q0Point s 3, hpts 3, profile2q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s)) (((9 / 10) + ((-8 /
        25) * s)), ((1 / 10) + ((81 / 50) * s))) :=
      ⟨profile2q0Point s 2, hpts 2, profile2q0Point s 1, hpts 1, profile2q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
    have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
    have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
    have hc2 : ConeBound Q (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) :=
      ⟨profile2q0Point s 3, hpts 3, profile2q0Point s 1, hpts 1, profile2q0Point s 0, hpts 0, hb2_0,
          hb2_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile2q0Point s 3, hpts 3, profile2q0Point s 1, hpts 1, profile2q0Point s 0, hpts 0, hb2_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-237 / 100) * s)), ((51 / 20) * s)), (((9 /
        10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
  · have hl : 0 ≤ s - (1 / 20) := by
      linarith
    have hh : 0 ≤ (1 / 10) - s := by
      linarith
    have hd0 := arithmeticBound9 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) :=
      ⟨profile2q0Point s 2, hpts 2, profile2q0Point s 3, hpts 3, profile2q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound12 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) :=
      ⟨profile2q0Point s 3, hpts 3, profile2q0Point s 1, hpts 1, profile2q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile2q0Point s 3, hpts 3, profile2q0Point s 1, hpts 1, profile2q0Point s 0, hpts 0, hb1_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-8 / 25) * s)), ((1 / 10) + ((81 / 50) *
        s))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
