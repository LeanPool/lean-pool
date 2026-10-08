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

/-- The four-point configuration for profile 4, owner 2, parameterized by the minimal section. -/
def profile4q2Point (s : ℝ) : Fin 4 → Point :=
  ![(1, 1), (1, ((5 / 4) * s)), ((1 + (-1 * s)), 1), (((1 / 2) + (-1 * s)), (1 / 2))]

theorem profile4q2_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 10)) (hq : 0 < Q.side)
    (hpts : ∀ i, profile4q2Point s i ∈ Q.carrier) : 1 ≤ Q.side := by
  have hl : 0 ≤ s - 0 := by
    linarith
  have hh : 0 ≤ (1 / 10) - s := by
    linarith
  have hd0 : 0 < cross (1, 0) (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) := by
    have hp : (0 : ℝ) < ((9 / 4) * s) := by
      have heq : (((9 / 4) * s) : ℝ) = s ^ 1 * ((9 / 4)) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]
  have hb0_0 : len (1, 0) ≤ supportNum (1, 0) (profile4q2Point s 2) (profile4q2Point s 3)
      (profile4q2Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + s) := by
        have heq : ((1 + s) : ℝ) = (1 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile4q2Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 2) + (2 * s)) := by
        have heq : (((s ^ 2) + (2 * s)) : ℝ) = s ^ 1 * (2 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 2) + (2 * s)) = (supportNum (1, 0) (profile4q2Point s 2) (profile4q2Point s
          3) (profile4q2Point s 0)) ^ 2 - normSq (1, 0) := by
        simp [profile4q2Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb0_1 : len (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) ≤ supportNum (((1 / 2) + ((-5 / 4) *
      s)), ((9 / 4) * s)) (profile4q2Point s 2) (profile4q2Point s 3) (profile4q2Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ ((1 / 2) + (s ^ 2) + ((3 / 8) * s)) := by
        have heq : (((1 / 2) + (s ^ 2) + ((3 / 8) * s)) : ℝ) = ((1 / 2) + (15 / 4) * (s - 0) ^ 1 *
            ((1 / 10) - s) ^ 1 + (19 / 4) * (s - 0) ^ 2) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile4q2Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 4) + ((1 / 2) * s) + ((-171 / 64) * (s ^ 2)) + ((3 / 4) * (s ^ 3)))
        := by
        have heq : (((s ^ 4) + ((1 / 2) * s) + ((-171 / 64) * (s ^ 2)) + ((3 / 4) * (s ^ 3))) : ℝ) =
            s ^ 1 * ((3861 / 16000) + (4139 / 16) * ((1 / 10) - s) ^ 3 + (4071 / 8) * (s - 0) ^ 1 *
            ((1 / 10) - s) ^ 2 + (3987 / 16) * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 4) + ((1 / 2) * s) + ((-171 / 64) * (s ^ 2)) + ((3 / 4) * (s ^ 3))) =
          (supportNum (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) (profile4q2Point s 2)
          (profile4q2Point s 3) (profile4q2Point s 0)) ^ 2 - normSq (((1 / 2) + ((-5 / 4) * s)), ((9
          / 4) * s)) := by
        simp [profile4q2Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc0 : ConeBound Q (1, 0) (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) :=
    ⟨profile4q2Point s 2, hpts 2, profile4q2Point s 3, hpts 3, profile4q2Point s 0, hpts 0, hb0_0,
        hb0_1⟩
  have hd1 : 0 < cross (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) ((1 / 2), (1 / 2)) := by
    have hp : (0 : ℝ) < ((1 / 4) + ((-7 / 4) * s)) := by
      have heq : (((1 / 4) + ((-7 / 4) * s)) : ℝ) = ((3 / 40) + (7 / 4) * ((1 / 10) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]; ring
  have hb1_0 : len (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) ≤ supportNum (((1 / 2) + ((-5 / 4) *
      s)), ((9 / 4) * s)) (profile4q2Point s 2) (profile4q2Point s 1) (profile4q2Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ ((1 / 2) + (s ^ 2) + ((3 / 8) * s)) := by
        have heq : (((1 / 2) + (s ^ 2) + ((3 / 8) * s)) : ℝ) = ((1 / 2) + (15 / 4) * (s - 0) ^ 1 *
            ((1 / 10) - s) ^ 1 + (19 / 4) * (s - 0) ^ 2) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile4q2Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 4) + ((1 / 2) * s) + ((-171 / 64) * (s ^ 2)) + ((3 / 4) * (s ^ 3)))
        := by
        have heq : (((s ^ 4) + ((1 / 2) * s) + ((-171 / 64) * (s ^ 2)) + ((3 / 4) * (s ^ 3))) : ℝ) =
            s ^ 1 * ((3861 / 16000) + (4139 / 16) * ((1 / 10) - s) ^ 3 + (4071 / 8) * (s - 0) ^ 1 *
            ((1 / 10) - s) ^ 2 + (3987 / 16) * (s - 0) ^ 2 * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 4) + ((1 / 2) * s) + ((-171 / 64) * (s ^ 2)) + ((3 / 4) * (s ^ 3))) =
          (supportNum (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) (profile4q2Point s 2)
          (profile4q2Point s 1) (profile4q2Point s 0)) ^ 2 - normSq (((1 / 2) + ((-5 / 4) * s)), ((9
          / 4) * s)) := by
        simp [profile4q2Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb1_1 : len ((1 / 2), (1 / 2)) ≤ supportNum ((1 / 2), (1 / 2)) (profile4q2Point s 2)
      (profile4q2Point s 1) (profile4q2Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + ((-3 / 4) * s)) := by
        have heq : ((1 + ((-3 / 4) * s)) : ℝ) = ((37 / 40) + (3 / 4) * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile4q2Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((1 / 4) + ((-3 / 2) * s) + ((9 / 16) * (s ^ 2))) := by
        have heq : (((1 / 4) + ((-3 / 2) * s) + ((9 / 16) * (s ^ 2))) : ℝ) = ((169 / 1600) + (231 /
            16) * ((1 / 10) - s) ^ 2 + (111 / 8) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((1 / 4) + ((-3 / 2) * s) + ((9 / 16) * (s ^ 2))) = (supportNum ((1 / 2), (1 / 2))
          (profile4q2Point s 2) (profile4q2Point s 1) (profile4q2Point s 0)) ^ 2 - normSq ((1 / 2),
          (1 / 2)) := by
        simp [profile4q2Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc1 : ConeBound Q (((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)) ((1 / 2), (1 / 2)) :=
    ⟨profile4q2Point s 2, hpts 2, profile4q2Point s 1, hpts 1, profile4q2Point s 0, hpts 0, hb1_0,
        hb1_1⟩
  have hd2 : 0 < cross ((1 / 2), (1 / 2)) (-1, 1) := by
    have hp : (0 : ℝ) < 1 := by
      have heq : (1 : ℝ) = (1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]; ring
  have hb2_0 : len ((1 / 2), (1 / 2)) ≤ supportNum ((1 / 2), (1 / 2)) (profile4q2Point s 3)
      (profile4q2Point s 1) (profile4q2Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + ((-3 / 4) * s)) := by
        have heq : ((1 + ((-3 / 4) * s)) : ℝ) = ((37 / 40) + (3 / 4) * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile4q2Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((1 / 4) + ((-3 / 2) * s) + ((9 / 16) * (s ^ 2))) := by
        have heq : (((1 / 4) + ((-3 / 2) * s) + ((9 / 16) * (s ^ 2))) : ℝ) = ((169 / 1600) + (231 /
            16) * ((1 / 10) - s) ^ 2 + (111 / 8) * (s - 0) ^ 1 * ((1 / 10) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((1 / 4) + ((-3 / 2) * s) + ((9 / 16) * (s ^ 2))) = (supportNum ((1 / 2), (1 / 2))
          (profile4q2Point s 3) (profile4q2Point s 1) (profile4q2Point s 0)) ^ 2 - normSq ((1 / 2),
          (1 / 2)) := by
        simp [profile4q2Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb2_1 : len (-1, 1) ≤ supportNum (-1, 1) (profile4q2Point s 3) (profile4q2Point s 1)
      (profile4q2Point s 0) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + s) := by
        have heq : ((1 + s) : ℝ) = (1 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [profile4q2Point, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 2) + (2 * s)) := by
        have heq : (((s ^ 2) + (2 * s)) : ℝ) = s ^ 1 * (2 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 2) + (2 * s)) = (supportNum (-1, 1) (profile4q2Point s 3) (profile4q2Point s
          1) (profile4q2Point s 0)) ^ 2 - normSq (-1, 1) := by
        simp [profile4q2Point, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc2 : ConeBound Q ((1 / 2), (1 / 2)) (-1, 1) :=
    ⟨profile4q2Point s 3, hpts 3, profile4q2Point s 1, hpts 1, profile4q2Point s 0, hpts 0, hb2_0,
        hb2_1⟩
  have hend : SupportBound Q (-1, 1) :=
    ⟨profile4q2Point s 3, hpts 3, profile4q2Point s 1, hpts 1, profile4q2Point s 0, hpts 0, hb2_1⟩
  apply one_le_side_of_fan hq (vs := [(((1 / 2) + ((-5 / 4) * s)), ((9 / 4) * s)), ((1 / 2), (1 /
      2)), (-1, 1)])
  exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
