/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.AcrossArea
public import LeanPool.ConwaySoifer.Simplified.Geometry.AcrossFour
import Mathlib.Tactic

/-!
# AcrossSmall

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

theorem across_small {T : Configuration} {r s : ℝ} (H : Canonical .Across T r s)
    (hs : s ≤ 1 / 80) : False := by
  set c := rayLen (T 1) (vertex 0) upDir with hc
  have hc0 : 0 < c := H.ext_pos
  have hc1 : c < 1 := lt_of_le_of_lt H.ext_le H.r_lt
  have hc12 : c < 12 * s := across_ext_small H hs
  have hv := H.across_v0_mem
  -- the point `(1, c)` is reached by `A₀` or `S₁`
  have hcov : ∀ t ∈ Set.Ioo c 1, linePoint (vertex 0) upDir t ∈ (T 7).carrier ∪ (T 2).carrier := by
    intro t ht
    have hmem : linePoint (vertex 0) upDir t ∈ target := by
      rw [upPt_eq_cornerSeg]
      exact cornerSeg_mem_target 0 0 (by linarith [ht.2]) (by linarith [ht.1, hc0])
    obtain ⟨k, hk⟩ := H.covers _ hmem
    have hallow : cornerAllowed 0 k = true := by
      rw [upPt_eq_cornerSeg] at hk
      exact cornerSeg_owner_allowed H.common H.r_lt H.anchored 0 0 (by linarith [ht.2])
        (by linarith [ht.1, hc0]) hk
    rcases cornerAllowed_cases 0 k hallow with rfl | rfl | rfl
    · exact Or.inl hk
    · exact absurd hk (not_mem_after_rayLen (T 1) hv upDir_unit ht.1)
    · exact Or.inr hk
  have hend := closed_cover_endpoint ((T 7).isClosed_carrier.union (T 2).isClosed_carrier)
    (continuous_linePoint _ _) hc1 hcov
  -- `(1, c) ∉ A₀`
  have hnot7 : linePoint (vertex 0) upDir c ∉ (T 7).carrier := by
    intro h7
    apply H.toMinAt.mid_not_corner_of_geometry midpoint_exclusion H.contact.1
    have hw : corner 0 ∈ (T 7).carrier := by
      have := H.anchored 7; simpa [anchor, corner] using this
    have hlam : (1 / 2 - c) / (1 - c) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
    have h1c : (1 : ℝ) - c ≠ 0 := by
      linarith
    have := (T 7).convex_carrier.add_smul_sub_mem h7 hw hlam
    convert this using 1
    rw [upPt_eq]
    apply Prod.ext <;> simp [extMid0, corner]; field_simp; ring
  have h2 : linePoint (vertex 0) upDir c ∈ (T 2).carrier := by
    rcases hend with h | h
    · exact absurd h hnot7
    · exact h
  -- `(1, 12 s) ∈ S₁`
  have hM := H.contact.2.2
  have h12 : ((1 : ℝ), 12 * s) ∈ (T 2).carrier := by
    have hlam : (12 * s - c) / (1 / 2 - c) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
    have h2c : (1 : ℝ) / 2 - c ≠ 0 := by
      linarith
    have key : (12 * s - c) / (1 / 2 - c) * (1 / 2 - c) = 12 * s - c := div_mul_cancel₀ _ h2c
    have := (T 2).convex_carrier.add_smul_sub_mem h2 hM hlam
    convert this using 1
    rw [upPt_eq]
    apply Prod.ext
    · simp [extMid0]
    · simp only [extMid0, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      linarith [key]
  have hv1 : vertex 1 ∈ (T 2).carrier := by
    have := H.anchored 2; simpa [anchor, vertex] using this
  have ha : linePoint (vertex 1) (sideDirection 1 true) s ∈ (T 2).carrier :=
    H.toMinAt.sidePt_mem 1 true H.s_pos.le le_rfl
  apply (not_le.mpr (H.toMinAt.side_lt' 2))
  apply acrossFour_obstruction H.s_pos hs (H.toMinAt.side_pos' 2)
  intro i
  fin_cases i
  · simpa [acrossFourPoint, linePoint, vertex, sideDirection, neighbor] using ha
  · simpa [acrossFourPoint, vertex] using hv1
  · exact hM
  · exact h12

end ConwaySoifer.Simplified
