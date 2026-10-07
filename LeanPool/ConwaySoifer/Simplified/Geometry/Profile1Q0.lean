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

/-- The four-point configuration for profile 1, owner 0, parameterized by the minimal section. -/
def profile1q0Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, ((1 / 2) * s)), ((1 + ((-1 / 4) * s)), 1), (((1 / 10) + ((-9 / 50) * s)), ((9 / 10)
      + ((-81 / 50) * s)))]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((23 / 10) * s) := by
    have heq : (((23 / 10) * s) : ℝ) = s ^ 1 * ((23 / 10)) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile1q0Point s 2) (profile1q0Point s 3) (profile1q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile1q0Point s 2)
        (profile1q0Point s 3) (profile1q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s)) ≤ supportNum (((9 / 10) + ((-53 / 25) *
        s)), ((23 / 10) * s)) (profile1q0Point s 2) (profile1q0Point s 3) (profile1q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-27 / 100) * s) + ((97 / 200) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-27 / 100) * s) + ((97 / 200) * (s ^ 2))) : ℝ) = ((71017 / 80000) +
          (983 / 200) * ((1 / 20) - s) ^ 2 + (443 / 100) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-2619 / 10000) * (s ^ 3)) + ((-317 / 80) * (s ^ 2)) + ((63 / 50) * s) +
      ((9409 / 40000) * (s ^ 4))) := by
      have heq : ((((-2619 / 10000) * (s ^ 3)) + ((-317 / 80) * (s ^ 2)) + ((63 / 50) * s) + ((9409
          / 40000) * (s ^ 4))) : ℝ) = s ^ 1 * ((339599889 / 320000000) + (63600111 / 40000) * ((1 /
          20) - s) ^ 3 + (127400333 / 40000) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 2 + (63790813 / 40000)
          * (s - 0) ^ 2 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-2619 / 10000) * (s ^ 3)) + ((-317 / 80) * (s ^ 2)) + ((63 / 50) * s) + ((9409 /
        40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s))
        (profile1q0Point s 2) (profile1q0Point s 3) (profile1q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-53 / 25) * s)), ((23 / 10) * s)) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s)) (((9 / 10) + ((-7 / 100) * s)), ((1 /
        10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((9 / 100) + ((-16367 / 5000) * (s ^ 2)) + ((-103 / 125) * s)) := by
    have heq : (((9 / 100) + ((-16367 / 5000) * (s ^ 2)) + ((-103 / 125) * s)) : ℝ) = ((81233 /
        2000000) + (98767 / 5000) * ((1 / 20) - s) ^ 2 + (57567 / 2500) * (s - 0) ^ 1 * ((1 / 20) -
        s) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s)) ≤ supportNum (((9 / 10) + ((-53 / 25) *
        s)), ((23 / 10) * s)) (profile1q0Point s 2) (profile1q0Point s 1) (profile1q0Point s 0) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((9 / 10) + ((-27 / 100) * s) + ((97 / 200) * (s ^ 2))) := by
      have heq : (((9 / 10) + ((-27 / 100) * s) + ((97 / 200) * (s ^ 2))) : ℝ) = ((71017 / 80000) +
          (983 / 200) * ((1 / 20) - s) ^ 2 + (443 / 100) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((-2619 / 10000) * (s ^ 3)) + ((-317 / 80) * (s ^ 2)) + ((63 / 50) * s) +
      ((9409 / 40000) * (s ^ 4))) := by
      have heq : ((((-2619 / 10000) * (s ^ 3)) + ((-317 / 80) * (s ^ 2)) + ((63 / 50) * s) + ((9409
          / 40000) * (s ^ 4))) : ℝ) = s ^ 1 * ((339599889 / 320000000) + (63600111 / 40000) * ((1 /
          20) - s) ^ 3 + (127400333 / 40000) * (s - 0) ^ 1 * ((1 / 20) - s) ^ 2 + (63790813 / 40000)
          * (s - 0) ^ 2 * ((1 / 20) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((-2619 / 10000) * (s ^ 3)) + ((-317 / 80) * (s ^ 2)) + ((63 / 50) * s) + ((9409 /
        40000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s))
        (profile1q0Point s 2) (profile1q0Point s 1) (profile1q0Point s 0)) ^ 2 - normSq (((9 / 10) +
        ((-53 / 25) * s)), ((23 / 10) * s)) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-7
        / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 2) (profile1q0Point s 1)
        (profile1q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) := by
      have heq : ((1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) : ℝ) = (1 + (43 / 2) * (s - 0) ^ 1
          * ((1 / 20) - s) ^ 1 + (2113 / 100) * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) +
      ((501 / 1000) * s) + ((1369 / 10000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
          1000) * s) + ((1369 / 10000) * (s ^ 4))) : ℝ) = ((9 / 100) + 4008 * (s - 0) ^ 1 * ((1 /
          20) - s) ^ 3 + (1118389 / 100) * (s - 0) ^ 2 * ((1 / 20) - s) ^ 2 + (1032787 / 100) * (s -
          0) ^ 3 * ((1 / 20) - s) ^ 1 + (31521169 / 10000) * (s - 0) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
        1000) * s) + ((1369 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-7 / 100) * s)), ((1 /
        10) + ((81 / 50) * s))) (profile1q0Point s 2) (profile1q0Point s 1) (profile1q0Point s 0)) ^
        2 - normSq (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    0 < cross (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((31 / 20) * s)) := by
    have heq : ((1 + ((31 / 20) * s)) : ℝ) = (1 + (31 / 20) * (s - 0) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-7
        / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 3) (profile1q0Point s 1)
        (profile1q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) := by
      have heq : ((1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) : ℝ) = (1 + (43 / 2) * (s - 0) ^ 1
          * ((1 / 20) - s) ^ 1 + (2113 / 100) * (s - 0) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) +
      ((501 / 1000) * s) + ((1369 / 10000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
          1000) * s) + ((1369 / 10000) * (s ^ 4))) : ℝ) = ((9 / 100) + 4008 * (s - 0) ^ 1 * ((1 /
          20) - s) ^ 3 + (1118389 / 100) * (s - 0) ^ 2 * ((1 / 20) - s) ^ 2 + (1032787 / 100) * (s -
          0) ^ 3 * ((1 / 20) - s) ^ 1 + (31521169 / 10000) * (s - 0) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
        1000) * s) + ((1369 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-7 / 100) * s)), ((1 /
        10) + ((81 / 50) * s))) (profile1q0Point s 3) (profile1q0Point s 1) (profile1q0Point s 0)) ^
        2 - normSq (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 20) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile1q0Point s 3) (profile1q0Point s 1) (profile1q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = (1 + (9 / 5) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((18 / 5) + (81 / 25) * (s
          - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile1q0Point s 3)
        (profile1q0Point s 1) (profile1q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (3 / 40) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((1 / 10) + ((81 / 50) * s)) := by
    have heq : (((1 / 10) + ((81 / 50) * s)) : ℝ) = ((181 / 1000) + (81 / 50) * (s - (1 / 20)) ^ 1)
        := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (3 / 40) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile1q0Point s 2) (profile1q0Point s 3) (profile1q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile1q0Point s 2)
        (profile1q0Point s 3) (profile1q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (3 / 40) - s) :
    len (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-7
        / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 2) (profile1q0Point s 3)
        (profile1q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((91 / 100) + ((1899 / 1000) * s) + ((14517 / 5000) * (s ^ 2))) := by
      have heq : (((91 / 100) + ((1899 / 1000) * s) + ((14517 / 5000) * (s ^ 2))) : ℝ) = ((2024417 /
          2000000) + (109467 / 1250) * (s - (1 / 20)) ^ 1 * ((3 / 40) - s) ^ 1 + (90477 / 1000) * (s
          - (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-819 / 10000) + ((90359 / 50000) * s) + ((6374489 / 1000000) * (s ^ 2)) +
      ((27567783 / 2500000) * (s ^ 3)) + ((210743289 / 25000000) * (s ^ 4))) := by
      have heq : (((-819 / 10000) + ((90359 / 50000) * s) + ((6374489 / 1000000) * (s ^ 2)) +
          ((27567783 / 2500000) * (s ^ 3)) + ((210743289 / 25000000) * (s ^ 4))) : ℝ) =
          ((103305189889 / 4000000000000) + (126577355739 / 781250) * (s - (1 / 20)) ^ 1 * ((3 / 40)
          - s) ^ 3 + (311940655727 / 625000) * (s - (1 / 20)) ^ 2 * ((3 / 40) - s) ^ 2 +
          (1602067420841 / 3125000) * (s - (1 / 20)) ^ 3 * ((3 / 40) - s) ^ 1 + (877919852917 /
          5000000) * (s - (1 / 20)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-819 / 10000) + ((90359 / 50000) * s) + ((6374489 / 1000000) * (s ^ 2)) +
        ((27567783 / 2500000) * (s ^ 3)) + ((210743289 / 25000000) * (s ^ 4))) = (supportNum (((9 /
        10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 2)
        (profile1q0Point s 3) (profile1q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-7 / 100) * s)),
        ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (3 / 40) - s) :
    0 < cross (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((31 / 20) * s)) := by
    have heq : ((1 + ((31 / 20) * s)) : ℝ) = ((431 / 400) + (31 / 20) * (s - (1 / 20)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (3 / 40) - s) :
    len (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-7
        / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 3) (profile1q0Point s 1)
        (profile1q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) := by
      have heq : ((1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) : ℝ) = ((42113 / 40000) + (1038 /
          25) * (s - (1 / 20)) ^ 1 * ((3 / 40) - s) ^ 1 + (823 / 20) * (s - (1 / 20)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) +
      ((501 / 1000) * s) + ((1369 / 10000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
          1000) * s) + ((1369 / 10000) * (s ^ 4))) : ℝ) = ((175521169 / 1600000000) + (11402988 /
          625) * (s - (1 / 20)) ^ 1 * ((3 / 40) - s) ^ 3 + (12796567 / 250) * (s - (1 / 20)) ^ 2 *
          ((3 / 40) - s) ^ 2 + (29754668 / 625) * (s - (1 / 20)) ^ 3 * ((3 / 40) - s) ^ 1 +
          (29332237 / 2000) * (s - (1 / 20)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
        1000) * s) + ((1369 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-7 / 100) * s)), ((1 /
        10) + ((81 / 50) * s))) (profile1q0Point s 3) (profile1q0Point s 1) (profile1q0Point s 0)) ^
        2 - normSq (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 20) ∧ 0 ≤ (3 / 40) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile1q0Point s 3) (profile1q0Point s 1) (profile1q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((109 / 100) + (9 / 5) * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((1881 / 500) + (81 / 25)
          * (s - (1 / 20)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile1q0Point s 3)
        (profile1q0Point s 1) (profile1q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 40) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (1, 0) (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < ((1 / 10) + ((81 / 50) * s)) := by
    have heq : (((1 / 10) + ((81 / 50) * s)) : ℝ) = ((443 / 2000) + (81 / 50) * (s - (3 / 40)) ^ 1)
        := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]

private theorem arithmeticBound16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 40) ∧ 0 ≤ (1 / 10) - s) :
    len (1, 0) ≤ supportNum (1, 0) (profile1q0Point s 2) (profile1q0Point s 3) (profile1q0Point s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((227 / 200) + (9 / 5) * (s - (3 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3843 / 1000) + (81 / 25)
          * (s - (3 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (1, 0) (profile1q0Point s 2)
        (profile1q0Point s 3) (profile1q0Point s 0)) ^ 2 - normSq (1, 0) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 40) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-7
        / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 2) (profile1q0Point s 3)
        (profile1q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ ((91 / 100) + ((1899 / 1000) * s) + ((14517 / 5000) * (s ^ 2))) := by
      have heq : (((91 / 100) + ((1899 / 1000) * s) + ((14517 / 5000) * (s ^ 2))) : ℝ) = ((8550053 /
          8000000) + (233451 / 2500) * (s - (3 / 40)) ^ 1 * ((1 / 10) - s) ^ 1 + (481419 / 5000) *
          (s - (3 / 40)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((-819 / 10000) + ((90359 / 50000) * s) + ((6374489 / 1000000) * (s ^ 2)) +
      ((27567783 / 2500000) * (s ^ 3)) + ((210743289 / 25000000) * (s ^ 4))) := by
      have heq : (((-819 / 10000) + ((90359 / 50000) * s) + ((6374489 / 1000000) * (s ^ 2)) +
          ((27567783 / 2500000) * (s ^ 3)) + ((210743289 / 25000000) * (s ^ 4))) : ℝ) =
          ((6042482302809 / 64000000000000) + (1185464422903 / 6250000) * (s - (3 / 40)) ^ 1 * ((1 /
          10) - s) ^ 3 + (7295588395621 / 12500000) * (s - (3 / 40)) ^ 2 * ((1 / 10) - s) ^ 2 +
          (3742584135079 / 6250000) * (s - (3 / 40)) ^ 3 * ((1 / 10) - s) ^ 1 + (204849127359 /
          1000000) * (s - (3 / 40)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((-819 / 10000) + ((90359 / 50000) * s) + ((6374489 / 1000000) * (s ^ 2)) +
        ((27567783 / 2500000) * (s ^ 3)) + ((210743289 / 25000000) * (s ^ 4))) = (supportNum (((9 /
        10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 2)
        (profile1q0Point s 3) (profile1q0Point s 0)) ^ 2 - normSq (((9 / 10) + ((-7 / 100) * s)),
        ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 40) ∧ 0 ≤ (1 / 10) - s) :
    0 < cross (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp : (0 : ℝ) < (1 + ((31 / 20) * s)) := by
    have heq : ((1 + ((31 / 20) * s)) : ℝ) = ((893 / 800) + (31 / 20) * (s - (3 / 40)) ^ 1) := by
      ring
    rw [heq]
    positivity
  convert hp using 1; simp [cross]; ring

private theorem arithmeticBound19 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 40) ∧ 0 ≤ (1 / 10) - s) :
    len (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) ≤ supportNum (((9 / 10) + ((-7
        / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (profile1q0Point s 3) (profile1q0Point s 1)
        (profile1q0Point s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) := by
      have heq : ((1 + ((-37 / 100) * (s ^ 2)) + ((43 / 40) * s)) : ℝ) = ((172567 / 160000) + (2039
          / 50) * (s - (3 / 40)) ^ 1 * ((1 / 10) - s) ^ 1 + (4041 / 100) * (s - (3 / 40)) ^ 2) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) +
      ((501 / 1000) * s) + ((1369 / 10000) * (s ^ 4))) := by
      have heq : (((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
          1000) * s) + ((1369 / 10000) * (s ^ 4))) : ℝ) = ((2954999889 / 25600000000) + (27642513 /
          2500) * (s - (3 / 40)) ^ 1 * ((1 / 10) - s) ^ 3 + (147657941 / 5000) * (s - (3 / 40)) ^ 2
          * ((1 / 10) - s) ^ 2 + (64654959 / 2500) * (s - (3 / 40)) ^ 3 * ((1 / 10) - s) ^ 1 +
          (591003 / 80) * (s - (3 / 40)) ^ 4) := by
        ring
      rw [heq]
      positivity
    have heq : ((9 / 100) + ((-84011 / 40000) * (s ^ 2)) + ((-1591 / 2000) * (s ^ 3)) + ((501 /
        1000) * s) + ((1369 / 10000) * (s ^ 4))) = (supportNum (((9 / 10) + ((-7 / 100) * s)), ((1 /
        10) + ((81 / 50) * s))) (profile1q0Point s 3) (profile1q0Point s 1) (profile1q0Point s 0)) ^
        2 - normSq (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

private theorem arithmeticBound20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 40) ∧ 0 ≤ (1 / 10) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (profile1q0Point s 3) (profile1q0Point s 1) (profile1q0Point s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp : (0 : ℝ) ≤ (1 + ((9 / 5) * s)) := by
      have heq : ((1 + ((9 / 5) * s)) : ℝ) = ((227 / 200) + (9 / 5) * (s - (3 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [profile1q0Point, supportNum, cross, rot]; ring
  · have hp : (0 : ℝ) ≤ (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) := by
      have heq : ((((18 / 5) * s) + ((81 / 25) * (s ^ 2))) : ℝ) = s ^ 1 * ((3843 / 1000) + (81 / 25)
          * (s - (3 / 40)) ^ 1) := by
        ring
      rw [heq]
      positivity
    have heq : (((18 / 5) * s) + ((81 / 25) * (s ^ 2))) = (supportNum (-1, 1) (profile1q0Point s 3)
        (profile1q0Point s 1) (profile1q0Point s 0)) ^ 2 - normSq (-1, 1) := by
      simp [profile1q0Point, supportNum, cross, rot, normSq]; ring
    rw [heq] at hp
    linarith

theorem profile1q0_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile1q0Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 20)
  · have hl : 0 ≤ s - 0 := by
      linarith
    have hh : 0 ≤ (1 / 20) - s := by
      linarith
    have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s)) :=
      ⟨profile1q0Point s 2, hpts 2, profile1q0Point s 3, hpts 3, profile1q0Point s 0, hpts 0, hb0_0,
          hb0_1⟩
    have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q (((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s)) (((9 / 10) + ((-7 / 100)
        * s)), ((1 / 10) + ((81 / 50) * s))) :=
      ⟨profile1q0Point s 2, hpts 2, profile1q0Point s 1, hpts 1, profile1q0Point s 0, hpts 0, hb1_0,
          hb1_1⟩
    have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
    have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
    have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
    have hc2 : ConeBound Q (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1) :=
      ⟨profile1q0Point s 3, hpts 3, profile1q0Point s 1, hpts 1, profile1q0Point s 0, hpts 0, hb2_0,
          hb2_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨profile1q0Point s 3, hpts 3, profile1q0Point s 1, hpts 1, profile1q0Point s 0, hpts 0, hb2_1⟩
    apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-53 / 25) * s)), ((23 / 10) * s)), (((9 / 10)
        + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩
  · by_cases hsplit : s ≤ (3 / 40)
    · have hl : 0 ≤ s - (1 / 20) := by
        linarith
      have hh : 0 ≤ (3 / 40) - s := by
        linarith
      have hd0 := arithmeticBound9 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
        ⟨profile1q0Point s 2, hpts 2, profile1q0Point s 3, hpts 3, profile1q0Point s 0, hpts 0,
            hb0_0, hb0_1⟩
      have hd1 := arithmeticBound12 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1)
          :=
        ⟨profile1q0Point s 3, hpts 3, profile1q0Point s 1, hpts 1, profile1q0Point s 0, hpts 0,
            hb1_0, hb1_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨profile1q0Point s 3, hpts 3, profile1q0Point s 1, hpts 1, profile1q0Point s 0, hpts 0,
            hb1_1⟩
      apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) *
          s))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩
    · have hl : 0 ≤ s - (3 / 40) := by
        linarith
      have hh : 0 ≤ (1 / 10) - s := by
        linarith
      have hd0 := arithmeticBound15 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound16 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound17 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) :=
        ⟨profile1q0Point s 2, hpts 2, profile1q0Point s 3, hpts 3, profile1q0Point s 0, hpts 0,
            hb0_0, hb0_1⟩
      have hd1 := arithmeticBound18 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound19 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound20 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q (((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) * s))) (-1, 1)
          :=
        ⟨profile1q0Point s 3, hpts 3, profile1q0Point s 1, hpts 1, profile1q0Point s 0, hpts 0,
            hb1_0, hb1_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨profile1q0Point s 3, hpts 3, profile1q0Point s 1, hpts 1, profile1q0Point s 0, hpts 0,
            hb1_1⟩
      apply one_le_side_of_fan hq (vs := [(((9 / 10) + ((-7 / 100) * s)), ((1 / 10) + ((81 / 50) *
          s))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
