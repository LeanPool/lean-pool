/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.AownCut
public import LeanPool.ConwaySoifer.Simplified.Geometry.Midpoint
public import LeanPool.ConwaySoifer.Geometry.AownFacts
import Mathlib.Tactic

/-!
# AownLarge

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

/-- The large-Aown complement from the forbidden corner section and the
full-endpoint cone restriction. -/
theorem aown_large {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : 7 / 20 ≤ s) : False := by
  let c := aownCut s
  obtain ⟨hsc, hc1⟩ := aownCut_bounds H.s_lt.le
  change s < c at hsc
  change c < 1 at hc1
  have hc0 : 0 < c := by
    linarith [H.s_pos]
  have hd : 0 < 2 - s := by
    linarith [H.s_lt]
  have heq : c * (2 - s) + s ^ 2 = 1 := by
    dsimp [c, aownCut]
    field_simp [hd.ne']; ring
  have noA : (1, c) ∉ (T 7).carrier := by
    intro hq
    let Q' := (T 7).mapAffineIso cornerCoordinates cornerCoordinates_isometry
    have mem {p : Point} (h : p ∈ (T 7).carrier) : cornerCoordinates p ∈ Q'.carrier :=
      (T 7).mem_mapAffineIso _ _ h
    have hf : linePoint (corner 0) (cornerDirection 0 1) s ∈ (T 7).carrier :=
      (linePoint_mem_iff_le_rayLen _ (H.toMinAt.corner_mem 0)
        (cornerDirection_unit 0 1) H.s_pos.le).mpr (H.corner_min 0 1)
    have hge : 1 ≤ Q'.side := by
      refine forbidden_corner_section (Q := Q') H.s_pos.le hsc.le hc1.le heq.le
        (H.toMinAt.side_pos' 7) ?_ ?_ ?_ ?_
      · simpa [cornerCoordinates_apply, corner] using mem (H.toMinAt.corner_mem 0)
      · simpa [cornerCoordinates_apply] using mem hq
      · simpa [cornerCoordinates_apply, linePoint, corner, cornerDirection, vertex] using mem hf
      · simpa [cornerCoordinates_apply, minEndpoint, ContactCase.right, linePoint,
          sideDirection, neighbor, vertex] using mem H.contact.1
    exact (not_le.mpr (H.toMinAt.side_lt' 7)) hge
  have noS1 : (1, c) ∉ (T 2).carrier := by
    intro hq
    have hp := H.toMinAt.sidePt_mem 1 true H.s_pos.le le_rfl
    apply (T 2).cannot_contain_unit_chord (H.toMinAt.side_lt' 2) _ hp hq
    simp [linePoint, vertex, sideDirection, neighbor, sqDist]
    nlinarith [sq_nonneg (c - 1 + (1 + s) / 2), H.s_pos]
  have hcS : (1, c) ∈ (T 1).carrier := by
    have hpt : linePoint (corner 0) (cornerDirection 0 0) (1 - c) = (1, c) := by
      ext <;> simp [linePoint, corner, cornerDirection, vertex]
    have ht0 : 0 ≤ 1 - c := by
      linarith
    have ht1 : 1 - c ≤ 1 := by
      linarith
    obtain ⟨k, hk⟩ := H.covers _ (cornerSeg_mem_target 0 0 ht0 ht1)
    have ha := cornerSeg_owner_allowed H.common H.r_lt H.anchored 0 0 ht0 ht1 hk
    rw [hpt] at hk
    rcases cornerAllowed_cases 0 k ha with rfl | rfl | rfl
    · exact (noA hk).elim
    · exact hk
    · exact (noS1 hk).elim
  have hu : (1, -s) ∈ (T 1).carrier := by
    simpa [linePoint, vertex, sideDirection, neighbor, sideIndex] using
      H.toMinAt.sidePt_mem 0 false H.s_pos.le le_rfl
  obtain ⟨hhi, hlo⟩ := aownCut_support hs H.s_lt.le
  have hge := full_own_obstruction H.s_pos hsc (H.toMinAt.side_pos' 1)
    (H.toMinAt.vertex_mem 0) hu hcS H.endpoint hlo hhi
  exact (not_le.mpr (H.toMinAt.side_lt' 1)) hge

end ConwaySoifer.Simplified
