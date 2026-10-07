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

/-- The four-point configuration used by the Across local obstruction. -/
def acrossFourPoint (s : ℝ) : Fin 4 → Point :=
  ![((-1 * s), 1), (0, 1), (1, (1 / 2)), (1, (12 * s))]

theorem acrossFour_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 80)) (hq : 0 < Q.side)
    (hpts : ∀ i, acrossFourPoint s i ∈ Q.carrier) : 1 ≤ Q.side := by
  have hl : 0 ≤ s - 0 := by
    linarith
  have hh : 0 ≤ (1 / 80) - s := by
    linarith
  have hd0 : 0 < cross (1, 0) ((1 + (-12 * s)), (13 * s)) := by
    have hp : (0 : ℝ) < (13 * s) := by
      have heq : ((13 * s) : ℝ) = s ^ 1 * (13) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]
  have hb0_0 : len (1, 0) ≤ supportNum (1, 0) (acrossFourPoint s 0) (acrossFourPoint s 0)
      (acrossFourPoint s 2) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + s) := by
        have heq : ((1 + s) : ℝ) = (1 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [acrossFourPoint, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 2) + (2 * s)) := by
        have heq : (((s ^ 2) + (2 * s)) : ℝ) = s ^ 1 * (2 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 2) + (2 * s)) = (supportNum (1, 0) (acrossFourPoint s 0) (acrossFourPoint s
          0) (acrossFourPoint s 2)) ^ 2 - normSq (1, 0) := by
        simp [acrossFourPoint, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb0_1 : len ((1 + (-12 * s)), (13 * s)) ≤ supportNum ((1 + (-12 * s)), (13 * s))
      (acrossFourPoint s 0) (acrossFourPoint s 0) (acrossFourPoint s 2) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + ((-9 / 2) * s)) := by
        have heq : ((1 + (s ^ 2) + ((-9 / 2) * s)) : ℝ) = ((6041 / 6400) + 359 * ((1 / 80) - s) ^ 2
            + 358 * (s - 0) ^ 1 * ((1 / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [acrossFourPoint, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 4) + (-9 * (s ^ 3)) + (2 * s) + ((-539 / 4) * (s ^ 2))) := by
        have heq : (((s ^ 4) + (-9 * (s ^ 3)) + (2 * s) + ((-539 / 4) * (s ^ 2))) : ℝ) = s ^ 1 *
            ((160881 / 512000) + 863119 * ((1 / 80) - s) ^ 3 + 1726957 * (s - 0) ^ 1 * ((1 / 80) -
            s) ^ 2 + 863837 * (s - 0) ^ 2 * ((1 / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 4) + (-9 * (s ^ 3)) + (2 * s) + ((-539 / 4) * (s ^ 2))) = (supportNum ((1 +
          (-12 * s)), (13 * s)) (acrossFourPoint s 0) (acrossFourPoint s 0) (acrossFourPoint s 2)) ^
          2 - normSq ((1 + (-12 * s)), (13 * s)) := by
        simp [acrossFourPoint, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc0 : ConeBound Q (1, 0) ((1 + (-12 * s)), (13 * s)) :=
    ⟨acrossFourPoint s 0, hpts 0, acrossFourPoint s 0, hpts 0, acrossFourPoint s 2, hpts 2, hb0_0,
        hb0_1⟩
  have hd1 : 0 < cross ((1 + (-12 * s)), (13 * s)) (((-1 / 2) + (-1 * s)), (1 + s)) := by
    have hp : (0 : ℝ) < (1 + (s ^ 2) + ((-9 / 2) * s)) := by
      have heq : ((1 + (s ^ 2) + ((-9 / 2) * s)) : ℝ) = ((6041 / 6400) + 359 * ((1 / 80) - s) ^ 2 +
          358 * (s - 0) ^ 1 * ((1 / 80) - s) ^ 1) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]; ring
  have hb1_0 : len ((1 + (-12 * s)), (13 * s)) ≤ supportNum ((1 + (-12 * s)), (13 * s))
      (acrossFourPoint s 0) (acrossFourPoint s 3) (acrossFourPoint s 2) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + ((-9 / 2) * s)) := by
        have heq : ((1 + (s ^ 2) + ((-9 / 2) * s)) : ℝ) = ((6041 / 6400) + 359 * ((1 / 80) - s) ^ 2
            + 358 * (s - 0) ^ 1 * ((1 / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [acrossFourPoint, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 4) + (-9 * (s ^ 3)) + (2 * s) + ((-539 / 4) * (s ^ 2))) := by
        have heq : (((s ^ 4) + (-9 * (s ^ 3)) + (2 * s) + ((-539 / 4) * (s ^ 2))) : ℝ) = s ^ 1 *
            ((160881 / 512000) + 863119 * ((1 / 80) - s) ^ 3 + 1726957 * (s - 0) ^ 1 * ((1 / 80) -
            s) ^ 2 + 863837 * (s - 0) ^ 2 * ((1 / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 4) + (-9 * (s ^ 3)) + (2 * s) + ((-539 / 4) * (s ^ 2))) = (supportNum ((1 +
          (-12 * s)), (13 * s)) (acrossFourPoint s 0) (acrossFourPoint s 3) (acrossFourPoint s 2)) ^
          2 - normSq ((1 + (-12 * s)), (13 * s)) := by
        simp [acrossFourPoint, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb1_1 : len (((-1 / 2) + (-1 * s)), (1 + s)) ≤ supportNum (((-1 / 2) + (-1 * s)), (1 + s))
      (acrossFourPoint s 0) (acrossFourPoint s 3) (acrossFourPoint s 2) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + ((-9 / 2) * s)) := by
        have heq : ((1 + (s ^ 2) + ((-9 / 2) * s)) : ℝ) = ((6041 / 6400) + 359 * ((1 / 80) - s) ^ 2
            + 358 * (s - 0) ^ 1 * ((1 / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [acrossFourPoint, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((1 / 4) + (s ^ 4) + (-9 * (s ^ 3)) + ((-21 / 2) * s) + ((85 / 4) * (s ^
        2))) := by
        have heq : (((1 / 4) + (s ^ 4) + (-9 * (s ^ 3)) + ((-21 / 2) * s) + ((85 / 4) * (s ^ 2))) :
            ℝ) = ((4999281 / 40960000) + 5240719 * ((1 / 80) - s) ^ 4 + 15586876 * (s - 0) ^ 1 * ((1
            / 80) - s) ^ 3 + 15452314 * (s - 0) ^ 2 * ((1 / 80) - s) ^ 2 + 5106156 * (s - 0) ^ 3 *
            ((1 / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((1 / 4) + (s ^ 4) + (-9 * (s ^ 3)) + ((-21 / 2) * s) + ((85 / 4) * (s ^ 2))) =
          (supportNum (((-1 / 2) + (-1 * s)), (1 + s)) (acrossFourPoint s 0) (acrossFourPoint s 3)
          (acrossFourPoint s 2)) ^ 2 - normSq (((-1 / 2) + (-1 * s)), (1 + s)) := by
        simp [acrossFourPoint, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc1 : ConeBound Q ((1 + (-12 * s)), (13 * s)) (((-1 / 2) + (-1 * s)), (1 + s)) :=
    ⟨acrossFourPoint s 0, hpts 0, acrossFourPoint s 3, hpts 3, acrossFourPoint s 2, hpts 2, hb1_0,
        hb1_1⟩
  have hd2 : 0 < cross (((-1 / 2) + (-1 * s)), (1 + s)) (-1, 1) := by
    have hp : (0 : ℝ) < (1 / 2) := by
      have heq : ((1 / 2) : ℝ) = ((1 / 2)) := by
        ring
      rw [heq]
      positivity
    convert hp using 1; simp [cross]; ring
  have hb2_0 : len (((-1 / 2) + (-1 * s)), (1 + s)) ≤ supportNum (((-1 / 2) + (-1 * s)), (1 + s))
      (acrossFourPoint s 0) (acrossFourPoint s 3) (acrossFourPoint s 1) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + (s ^ 2) + (-4 * s)) := by
        have heq : ((1 + (s ^ 2) + (-4 * s)) : ℝ) = ((6081 / 6400) + 319 * ((1 / 80) - s) ^ 2 + 318
            * (s - 0) ^ 1 * ((1 / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [acrossFourPoint, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((1 / 4) + (s ^ 4) + (-8 * (s ^ 3)) + (17 * (s ^ 2)) + ((-19 / 2) * s)) :=
        by
        have heq : (((1 / 4) + (s ^ 4) + (-8 * (s ^ 3)) + (17 * (s ^ 2)) + ((-19 / 2) * s)) : ℝ) =
            ((5484161 / 40960000) + 4755839 * ((1 / 80) - s) ^ 4 + 14159356 * (s - 0) ^ 1 * ((1 /
            80) - s) ^ 3 + 14051834 * (s - 0) ^ 2 * ((1 / 80) - s) ^ 2 + 4648316 * (s - 0) ^ 3 * ((1
            / 80) - s) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((1 / 4) + (s ^ 4) + (-8 * (s ^ 3)) + (17 * (s ^ 2)) + ((-19 / 2) * s)) =
          (supportNum (((-1 / 2) + (-1 * s)), (1 + s)) (acrossFourPoint s 0) (acrossFourPoint s 3)
          (acrossFourPoint s 1)) ^ 2 - normSq (((-1 / 2) + (-1 * s)), (1 + s)) := by
        simp [acrossFourPoint, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hb2_1 : len (-1, 1) ≤ supportNum (-1, 1) (acrossFourPoint s 0) (acrossFourPoint s 3)
      (acrossFourPoint s 1) := by
    apply support_of_sq
    · have hp : (0 : ℝ) ≤ (1 + s) := by
        have heq : ((1 + s) : ℝ) = (1 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      convert hp using 1; simp [acrossFourPoint, supportNum, cross, rot]; ring
    · have hp : (0 : ℝ) ≤ ((s ^ 2) + (2 * s)) := by
        have heq : (((s ^ 2) + (2 * s)) : ℝ) = s ^ 1 * (2 + 1 * (s - 0) ^ 1) := by
          ring
        rw [heq]
        positivity
      have heq : ((s ^ 2) + (2 * s)) = (supportNum (-1, 1) (acrossFourPoint s 0) (acrossFourPoint s
          3) (acrossFourPoint s 1)) ^ 2 - normSq (-1, 1) := by
        simp [acrossFourPoint, supportNum, cross, rot, normSq]; ring
      rw [heq] at hp
      linarith
  have hc2 : ConeBound Q (((-1 / 2) + (-1 * s)), (1 + s)) (-1, 1) :=
    ⟨acrossFourPoint s 0, hpts 0, acrossFourPoint s 3, hpts 3, acrossFourPoint s 1, hpts 1, hb2_0,
        hb2_1⟩
  have hend : SupportBound Q (-1, 1) :=
    ⟨acrossFourPoint s 0, hpts 0, acrossFourPoint s 3, hpts 3, acrossFourPoint s 1, hpts 1, hb2_1⟩
  apply one_le_side_of_fan hq (vs := [((1 + (-12 * s)), (13 * s)), (((-1 / 2) + (-1 * s)), (1 + s)),
      (-1, 1)])
  exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
