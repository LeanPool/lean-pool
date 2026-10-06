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

/-- The four mandatory side-owner points in the large-parameter Across obstruction. -/
def acrossLargeSidePoint : Fin 4 → Point :=
  ![((-3 / 25), 1), (0, (9 / 10)), (1, (1 / 2)), (0, 1)]

theorem acrossLargeSide_obstruction {Q : EquilateralTriangle} (hq : 0 < Q.side)
    (hpts : ∀ i, acrossLargeSidePoint i ∈ Q.carrier) : 1 ≤ Q.side := by
  have hd0 : 0 < cross (1, 0) ((2 / 5), (3 / 5)) := by
    norm_num [cross]
  have hb0_0 : len (1, 0) ≤ supportNum (1, 0) (acrossLargeSidePoint 0) (acrossLargeSidePoint 1)
      (acrossLargeSidePoint 2) := by
    apply support_of_sq <;>
      norm_num [acrossLargeSidePoint, supportNum, cross, rot, normSq]
  have hb0_1 : len ((2 / 5), (3 / 5)) ≤ supportNum ((2 / 5), (3 / 5)) (acrossLargeSidePoint 0)
      (acrossLargeSidePoint 1) (acrossLargeSidePoint 2) := by
    apply support_of_sq <;>
      norm_num [acrossLargeSidePoint, supportNum, cross, rot, normSq]
  have hc0 : ConeBound Q (1, 0) ((2 / 5), (3 / 5)) :=
    ⟨acrossLargeSidePoint 0, hpts 0, acrossLargeSidePoint 1, hpts 1, acrossLargeSidePoint 2,
        hpts 2, hb0_0, hb0_1⟩
  have hd1 : 0 < cross ((2 / 5), (3 / 5)) ((-1 / 2), 1) := by
    norm_num [cross]
  have hb1_0 : len ((2 / 5), (3 / 5)) ≤ supportNum ((2 / 5), (3 / 5)) (acrossLargeSidePoint 0)
      (acrossLargeSidePoint 2) (acrossLargeSidePoint 2) := by
    apply support_of_sq <;>
      norm_num [acrossLargeSidePoint, supportNum, cross, rot, normSq]
  have hb1_1 : len ((-1 / 2), 1) ≤ supportNum ((-1 / 2), 1) (acrossLargeSidePoint 0)
      (acrossLargeSidePoint 2) (acrossLargeSidePoint 2) := by
    apply support_of_sq <;>
      norm_num [acrossLargeSidePoint, supportNum, cross, rot, normSq]
  have hc1 : ConeBound Q ((2 / 5), (3 / 5)) ((-1 / 2), 1) :=
    ⟨acrossLargeSidePoint 0, hpts 0, acrossLargeSidePoint 2, hpts 2, acrossLargeSidePoint 2,
        hpts 2, hb1_0, hb1_1⟩
  have hd2 : 0 < cross ((-1 / 2), 1) (-1, 1) := by
    norm_num [cross]
  have hb2_0 : len ((-1 / 2), 1) ≤ supportNum ((-1 / 2), 1) (acrossLargeSidePoint 0)
      (acrossLargeSidePoint 2) (acrossLargeSidePoint 3) := by
    apply support_of_sq <;>
      norm_num [acrossLargeSidePoint, supportNum, cross, rot, normSq]
  have hb2_1 : len (-1, 1) ≤ supportNum (-1, 1) (acrossLargeSidePoint 0) (acrossLargeSidePoint
      2) (acrossLargeSidePoint 3) := by
    apply support_of_sq <;>
      norm_num [acrossLargeSidePoint, supportNum, cross, rot, normSq]
  have hc2 : ConeBound Q ((-1 / 2), 1) (-1, 1) :=
    ⟨acrossLargeSidePoint 0, hpts 0, acrossLargeSidePoint 2, hpts 2, acrossLargeSidePoint 3,
        hpts 3, hb2_0, hb2_1⟩
  have hend : SupportBound Q (-1, 1) :=
    ⟨acrossLargeSidePoint 0, hpts 0, acrossLargeSidePoint 2, hpts 2, acrossLargeSidePoint 3,
        hpts 3, hb2_1⟩
  apply one_le_side_of_fan hq (vs := [((2 / 5), (3 / 5)), ((-1 / 2), 1), (-1, 1)])
  exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
