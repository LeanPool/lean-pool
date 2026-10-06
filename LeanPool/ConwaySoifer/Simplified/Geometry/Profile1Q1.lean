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

/-- The four-point configuration for profile 1, owner 1, parameterized by the minimal section. -/
def profile1q1Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, ((1 / 2) * s)), ((1 + ((-1 / 4) * s)), 1), (((3 / 5) + ((-3 / 5) * s)), ((2 / 5) +
      ((-2 / 5) * s)))]

theorem profile1q1_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile1q1Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  have hl : 0 ≤ s - 0 := by
    linarith
  have hh : 0 ≤ (1 / 10) - s := by
    linarith
  have hd0 : 0 < cross (1, 0) (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) := by
    have hp : (0 : ℝ) < ((3 / 2) * s) := by
      have heq : (((3 / 2) * s) : ℝ) = s ^ 1 * ((3 / 2)) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]
  have hb0_0 : len (1, 0) ≤ supportNum (1, 0) (profile1q1Point s 2) (profile1q1Point s 3)
      (profile1q1Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + s) := by
        have heq : ((1 + s) : ℝ) = (1 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile1q1Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 2) + (2 * s)) := by
        have heq : (((s ^ 2) + (2 * s)) : ℝ) = s ^ 1 * (2 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 2) + (2 * s)) = (supportNum (1, 0) (profile1q1Point s 2) (profile1q1Point s
          3) (profile1q1Point s 0)) ^ 2 - normSq (1, 0) := by
        simp [profile1q1Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb0_1 : len (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) ≤ supportNum (((2 / 5) + ((-9 / 10)
      * s)), ((3 / 2) * s)) (profile1q1Point s 2) (profile1q1Point s 3) (profile1q1Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ ((2 / 5) + ((2 / 5) * s) + ((3 / 40) * (s ^ 2))) := by
        have heq : (((2 / 5) + ((2 / 5) * s) + ((3 / 40) * (s ^ 2))) : ℝ) = ((2 / 5) + 4 * (s - 0) ^
            1 * ((1 / 10) - s) ^ 1 + (163 / 40) * (s - 0) ^ 2) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile1q1Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ (((-149 / 100) * (s ^ 2)) + ((3 / 50) * (s ^ 3)) + ((9 / 1600) * (s ^ 4))
        + ((11 / 25) * s)) := by
        have heq : ((((-149 / 100) * (s ^ 2)) + ((3 / 50) * (s ^ 3)) + ((9 / 1600) * (s ^ 4)) + ((11
            / 25) * s)) : ℝ) = s ^ 1 * ((466569 / 1600000) + (237431 / 1600) * ((1 / 10) - s) ^ 3 +
            (473893 / 1600) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 2 + (236453 / 1600) * (s - 0) ^ 2 * ((1
            / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : (((-149 / 100) * (s ^ 2)) + ((3 / 50) * (s ^ 3)) + ((9 / 1600) * (s ^ 4)) + ((11 /
          25) * s)) = (supportNum (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) (profile1q1Point s 2)
          (profile1q1Point s 3) (profile1q1Point s 0)) ^ 2 - normSq (((2 / 5) + ((-9 / 10) * s)),
          ((3 / 2) * s)) := by
        simp [profile1q1Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc0 : ConeBound Q (1, 0) (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) :=
    ⟨profile1q1Point s 2, hpts 2, profile1q1Point s 3, hpts 3, profile1q1Point s 0, hpts 0, hb0_0,
        hb0_1⟩
  have hd1 : 0 < cross (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) (((2 / 5) + ((7 / 20) * s)), ((3
      / 5) + ((2 / 5) * s))) := by
    have hp : (0 : ℝ) < ((6 / 25) + ((-177 / 200) * (s ^ 2)) + ((-49 / 50) * s)) := by
      have heq : (((6 / 25) + ((-177 / 200) * (s ^ 2)) + ((-49 / 50) * s)) : ℝ) = ((2663 / 20000) +
          (2137 / 200) * ((1 / 10) - s) ^ 2 + (1157 / 100) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]; ring
  have hb1_0 : len (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) ≤ supportNum (((2 / 5) + ((-9 / 10)
      * s)), ((3 / 2) * s)) (profile1q1Point s 2) (profile1q1Point s 1) (profile1q1Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ ((2 / 5) + ((2 / 5) * s) + ((3 / 40) * (s ^ 2))) := by
        have heq : (((2 / 5) + ((2 / 5) * s) + ((3 / 40) * (s ^ 2))) : ℝ) = ((2 / 5) + 4 * (s - 0) ^
            1 * ((1 / 10) - s) ^ 1 + (163 / 40) * (s - 0) ^ 2) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile1q1Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ (((-149 / 100) * (s ^ 2)) + ((3 / 50) * (s ^ 3)) + ((9 / 1600) * (s ^ 4))
        + ((11 / 25) * s)) := by
        have heq : ((((-149 / 100) * (s ^ 2)) + ((3 / 50) * (s ^ 3)) + ((9 / 1600) * (s ^ 4)) + ((11
            / 25) * s)) : ℝ) = s ^ 1 * ((466569 / 1600000) + (237431 / 1600) * ((1 / 10) - s) ^ 3 +
            (473893 / 1600) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 2 + (236453 / 1600) * (s - 0) ^ 2 * ((1
            / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : (((-149 / 100) * (s ^ 2)) + ((3 / 50) * (s ^ 3)) + ((9 / 1600) * (s ^ 4)) + ((11 /
          25) * s)) = (supportNum (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) (profile1q1Point s 2)
          (profile1q1Point s 1) (profile1q1Point s 0)) ^ 2 - normSq (((2 / 5) + ((-9 / 10) * s)),
          ((3 / 2) * s)) := by
        simp [profile1q1Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb1_1 : len (((2 / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) ≤ supportNum (((2 / 5) +
      ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) (profile1q1Point s 2) (profile1q1Point s 1)
      (profile1q1Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + ((-11 / 40) * (s ^ 2)) + ((2 / 5) * s)) := by
        have heq : ((1 + ((-11 / 40) * (s ^ 2)) + ((2 / 5) * s)) : ℝ) = (1 + 4 * (s - 0) ^ 1 * ((1 /
            10) - s) ^ 1 + (149 / 40) * (s - 0) ^ 2) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile1q1Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((6 / 25) + ((-33 / 100) * s) + ((-13 / 16) * (s ^ 2)) + ((-11 / 50) * (s
        ^ 3)) + ((121 / 1600) * (s ^ 4))) := by
        have heq : (((6 / 25) + ((-33 / 100) * s) + ((-13 / 16) * (s ^ 2)) + ((-11 / 50) * (s ^ 3))
            + ((121 / 1600) * (s ^ 4))) : ℝ) = ((3178601 / 16000000) + (661399 / 1600) * ((1 / 10) -
            s) ^ 4 + (529399 / 400) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 3 + (1127197 / 800) * (s - 0) ^
            2 * ((1 / 10) - s) ^ 2 + (199519 / 400) * (s - 0) ^ 3 * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((6 / 25) + ((-33 / 100) * s) + ((-13 / 16) * (s ^ 2)) + ((-11 / 50) * (s ^ 3)) +
          ((121 / 1600) * (s ^ 4))) = (supportNum (((2 / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) *
          s))) (profile1q1Point s 2) (profile1q1Point s 1) (profile1q1Point s 0)) ^ 2 - normSq (((2
          / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) := by
        simp [profile1q1Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc1 : ConeBound Q (((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)) (((2 / 5) + ((7 / 20) * s)),
      ((3 / 5) + ((2 / 5) * s))) :=
    ⟨profile1q1Point s 2, hpts 2, profile1q1Point s 1, hpts 1, profile1q1Point s 0, hpts 0, hb1_0,
        hb1_1⟩
  have hd2 : 0 < cross (((2 / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) (-1, 1) := by
    have hp : (0 : ℝ) < (1 + ((3 / 4) * s)) := by
      have heq : ((1 + ((3 / 4) * s)) : ℝ) = (1 + (3 / 4) * (s - 0) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]; ring
  have hb2_0 : len (((2 / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) ≤ supportNum (((2 / 5) +
      ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) (profile1q1Point s 3) (profile1q1Point s 1)
      (profile1q1Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + ((-11 / 40) * (s ^ 2)) + ((2 / 5) * s)) := by
        have heq : ((1 + ((-11 / 40) * (s ^ 2)) + ((2 / 5) * s)) : ℝ) = (1 + 4 * (s - 0) ^ 1 * ((1 /
            10) - s) ^ 1 + (149 / 40) * (s - 0) ^ 2) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile1q1Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((6 / 25) + ((-33 / 100) * s) + ((-13 / 16) * (s ^ 2)) + ((-11 / 50) * (s
        ^ 3)) + ((121 / 1600) * (s ^ 4))) := by
        have heq : (((6 / 25) + ((-33 / 100) * s) + ((-13 / 16) * (s ^ 2)) + ((-11 / 50) * (s ^ 3))
            + ((121 / 1600) * (s ^ 4))) : ℝ) = ((3178601 / 16000000) + (661399 / 1600) * ((1 / 10) -
            s) ^ 4 + (529399 / 400) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 3 + (1127197 / 800) * (s - 0) ^
            2 * ((1 / 10) - s) ^ 2 + (199519 / 400) * (s - 0) ^ 3 * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((6 / 25) + ((-33 / 100) * s) + ((-13 / 16) * (s ^ 2)) + ((-11 / 50) * (s ^ 3)) +
          ((121 / 1600) * (s ^ 4))) = (supportNum (((2 / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) *
          s))) (profile1q1Point s 3) (profile1q1Point s 1) (profile1q1Point s 0)) ^ 2 - normSq (((2
          / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) := by
        simp [profile1q1Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb2_1 : len (-1, 1) ≤ supportNum (-1, 1) (profile1q1Point s 3) (profile1q1Point s 1)
      (profile1q1Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + s) := by
        have heq : ((1 + s) : ℝ) = (1 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile1q1Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 2) + (2 * s)) := by
        have heq : (((s ^ 2) + (2 * s)) : ℝ) = s ^ 1 * (2 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 2) + (2 * s)) = (supportNum (-1, 1) (profile1q1Point s 3) (profile1q1Point s
          1) (profile1q1Point s 0)) ^ 2 - normSq (-1, 1) := by
        simp [profile1q1Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc2 : ConeBound Q (((2 / 5) + ((7 / 20) * s)), ((3 / 5) + ((2 / 5) * s))) (-1, 1) :=
    ⟨profile1q1Point s 3, hpts 3, profile1q1Point s 1, hpts 1, profile1q1Point s 0, hpts 0, hb2_0,
        hb2_1⟩
  have hend : SupportBound Q (-1, 1) :=
    ⟨profile1q1Point s 3, hpts 3, profile1q1Point s 1, hpts 1, profile1q1Point s 0, hpts 0, hb2_1⟩
  apply one_le_side_of_fan hq (vs := [(((2 / 5) + ((-9 / 10) * s)), ((3 / 2) * s)), (((2 / 5) + ((7
      / 20) * s)), ((3 / 5) + ((2 / 5) * s))), (-1, 1)])
  exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
