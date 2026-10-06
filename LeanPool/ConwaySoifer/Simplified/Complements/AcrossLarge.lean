/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.AcrossLargeSide
public import LeanPool.ConwaySoifer.Simplified.Geometry.AcrossLargeCentre
public import LeanPool.ConwaySoifer.Geometry.SideFacts
import Mathlib.Tactic

/-!
# AcrossLarge

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
-/

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

/-- The fixed witness `(0, 9/10)` excludes the expanded large-Across regime. -/
theorem across_large {T : Configuration} {r s : ℝ} (H : Canonical .Across T r s)
    (hs : 3 / 25 ≤ s) : False := by
  have hq : (0, 9 / 10) ∈ target := by
    norm_num [target]
  have side (i : Fin 6) (d : Bool) :
      linePoint (vertex i) (sideDirection i d) (3 / 25) ∈ (T (sideIndex i)).carrier :=
    H.toMinAt.sidePt_mem i d (by norm_num) hs
  have noS1 : (0, 9 / 10) ∉ (T 2).carrier := by
    intro hp
    have hge : 1 ≤ (T 2).side := by
      apply acrossLargeSide_obstruction (H.toMinAt.side_pos' 2)
      intro i
      fin_cases i
      · convert side 1 true using 1 <;>
          dsimp [acrossLargeSidePoint, linePoint, vertex, sideDirection, neighbor, sideIndex];
              norm_num
      · simpa [acrossLargeSidePoint] using hp
      · simpa [acrossLargeSidePoint, extMid0] using H.contact.2.2
      · simpa [acrossLargeSidePoint, vertex, sideIndex] using H.toMinAt.vertex_mem 1
    exact (not_le.mpr (H.toMinAt.side_lt' 2)) hge
  have noC : (0, 9 / 10) ∉ (T 0).carrier := by
    intro hp
    have hsp := H.s_pos
    have hs1 : 0 < 1 - s := by
      linarith [H.s_lt]
    have hk : 0 < s * (1 - s) / 3 := by
      positivity
    have hlow : 1 / 29 ≤ s * (1 - s) / 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs)
        (show 0 ≤ 22 / 25 - s by linarith [H.s_lt])]
    have hinner (j : Fin 6) : (1 / 29 : ℝ) • coreDir j ∈ (T 0).carrier := by
      have ht : (1 / 29) / (s * (1 - s) / 3) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by norm_num) hk.le, (div_le_one hk).mpr hlow⟩
      have hm := (T 0).convex_carrier.smul_mem_of_zero_mem H.toMinAt.zero_mem (H.core j) ht
      convert hm using 1
      rw [coreVertex, smul_smul, div_mul_cancel₀ _ hk.ne']
    have hge : 1 ≤ (T 0).side := by
      apply acrossLargeCentre_obstruction (H.toMinAt.side_pos'
          0)
      intro i
      fin_cases i
      · convert hinner 2 using 1; dsimp [acrossLargeCentrePoint, coreDir]; norm_num
      · convert hinner 3 using 1; dsimp [acrossLargeCentrePoint, coreDir]; norm_num
      · convert hinner 4 using 1; dsimp [acrossLargeCentrePoint, coreDir]; norm_num
      · convert hinner 5 using 1; dsimp [acrossLargeCentrePoint, coreDir]; norm_num
      · simpa [acrossLargeCentrePoint] using hp
    exact (not_le.mpr (H.toMinAt.side_lt' 0)) hge
  obtain ⟨k, hk⟩ := H.covers _ hq
  fin_cases k
  · exact noC hk
  · apply (T 1).cannot_contain_unit_chord (H.toMinAt.side_lt' 1) _ (side 0 false) hk
    dsimp [linePoint, vertex, sideDirection, neighbor, sqDist]
    norm_num
  · exact noS1 hk
  · apply (T 3).cannot_contain_unit_chord (H.toMinAt.side_lt' 3) _ (side 2 true) hk
    dsimp [linePoint, vertex, sideDirection, neighbor, sqDist]
    norm_num
  all_goals
    apply (T _).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _ (H.anchored _) hk
    dsimp [anchor, sqDist]
    norm_num

end ConwaySoifer.Simplified
