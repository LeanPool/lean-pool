/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.AownChains
public import LeanPool.ConwaySoifer.Simplified.Geometry.AownCentral
import Mathlib.Tactic

/-!
# AownSmall

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
variable {T : Configuration} {r s : ℝ}

/-- Four vertices of the doubled adaptive core are forced into the centre. -/
theorem aown_double_core (H : Canonical .Aown T r s) (hs : s ≤ 1 / 10)
    (j : Fin 6) (hj : j ≠ 0) (hj5 : j ≠ 5) : coreVertex (2 * s) j ∈ (T 0).carrier := by
  have hk0 : 0 ≤ 2 * s * (1 - 2 * s) := mul_nonneg (by linarith [H.s_pos]) (by linarith)
  have hk1 : 2 * s * (1 - 2 * s) ≤ 1 / 5 := by
    nlinarith [H.s_pos]
  have hhex : coreVertex (2 * s) j ∈ hexagon := by
    fin_cases j <;> simp only [hexagon, abs_le, coreVertex, coreDir, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, Prod.smul_mk, smul_eq_mul, mul_one, Set.mem_ofPred_eq, and_self_left,
        Fin.mk_one, Matrix.cons_val_one, mul_neg, neg_le_neg_iff, le_neg_add_iff_add_le,
        add_neg_le_iff_le_add, neg_add_le_iff_le_add, Fin.reduceFinMk, Matrix.cons_val,
        le_add_neg_iff_add_le] <;>
      (repeat' constructor) <;> nlinarith
  obtain ⟨k, hk⟩ := H.covers _ (hexagon_subset_target hhex)
  rcases owner_cases k with rfl | ⟨i, rfl⟩ | ⟨m, rfl⟩
  · exact hk
  · by_cases hi : i = 0
    · subst i
      apply False.elim
      apply (T (sideIndex 0)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
          (H.toMinAt.vertex_mem 0) hk
      fin_cases j <;> first | exact (hj rfl).elim | exact (hj5 rfl).elim |
        (simp [coreVertex, coreDir, vertex, sqDist]; nlinarith [sq_nonneg (2 * s * (1 - 2 * s))])
    · exact (core_exclusion (by linarith [H.s_pos]) (by linarith) i j
        (H.toMinAt.side_pos' _) (H.toMinAt.side_lt' _) (H.toMinAt.vertex_mem i)
        ((linePoint_mem_iff_le_rayLen _ (H.toMinAt.vertex_mem _) (sideDirection_unit _ _)
          (by linarith [H.s_pos])).mpr (aown_double H hs i hi false))
        ((linePoint_mem_iff_le_rayLen _ (H.toMinAt.vertex_mem _) (sideDirection_unit _ _)
          (by linarith [H.s_pos])).mpr (aown_double H hs i hi true)) hk).elim
  · apply False.elim
    apply (T (cornerIndex m)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
        (H.toMinAt.corner_mem m) hk
    fin_cases m <;> fin_cases j <;> simp [corner, coreVertex, coreDir, sqDist] <;>
      nlinarith [sq_nonneg (2 * s * (1 - 2 * s))]

theorem aown_half_core (H : Canonical .Aown T r s) (hs : s ≤ 1 / 10)
    (j : Fin 6) (hj : j ≠ 0) (hj5 : j ≠ 5) : (s / 2) • coreDir j ∈ (T 0).carrier := by
  have hp := aown_double_core H hs j hj hj5
  have he : coreVertex (2 * s) j = linePoint 0 (coreDir j) (2 * s * (1 - 2 * s) / 3) := by
    simp [coreVertex, linePoint]
  rw [he] at hp
  have hh := linePoint_between (T 0).convex_carrier H.toMinAt.zero_mem hp
    (show 0 ≤ s / 2 by linarith [H.s_pos]) (show s / 2 ≤ 2 * s * (1 - 2 * s) / 3 by nlinarith
        [H.s_pos])
  simpa [linePoint] using hh

theorem aown_last_point (H : Canonical .Aown T r s) (hs : s ≤ 1 / 10) :
    (1 - 4 * s / 3, 0) ∈ (T 0).carrier := by
  have hhex : (1 - 4 * s / 3, 0) ∈ hexagon := by
    simp [hexagon, abs_le]; constructor <;> linarith [H.s_pos]
  obtain ⟨k, hk⟩ := H.covers _ (hexagon_subset_target hhex)
  rcases owner_cases k with rfl | ⟨i, rfl⟩ | ⟨m, rfl⟩
  · exact hk
  · fin_cases i
    · obtain ⟨_, _, _, hx⟩ := H.aown_subset hs ⟨hk, hhex⟩
      simp [locX, locY] at hx
      have hp := mul_pos H.s_pos (show 0 < 1 / 10 - s + 1 / 100 by linarith)
      nlinarith [H.s_pos]
    · have hp := (linePoint_mem_iff_le_rayLen _ (H.toMinAt.vertex_mem 1) (sideDirection_unit 1 true)
        (show 0 ≤ 2 * s by linarith [H.s_pos])).mpr (aown_double H hs 1 (by decide) true)
      apply False.elim
      apply (T (sideIndex 1)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _ hp hk
      simp [linePoint, vertex, sideDirection, neighbor, sqDist]; nlinarith [H.s_pos]
    · apply False.elim
      apply (T (sideIndex 2)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
          (H.toMinAt.vertex_mem 2) hk
      dsimp [vertex, sqDist]; nlinarith [H.s_pos]
    · apply False.elim
      apply (T (sideIndex 3)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
          (H.toMinAt.vertex_mem 3) hk
      dsimp [vertex, sqDist]; nlinarith [H.s_pos]
    · apply False.elim
      apply (T (sideIndex 4)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
          (H.toMinAt.vertex_mem 4) hk
      dsimp [vertex, sqDist]; nlinarith [H.s_pos]
    · have hp := (linePoint_mem_iff_le_rayLen _ (H.toMinAt.vertex_mem 5) (sideDirection_unit 5
        false)
        (show 0 ≤ 2 * s by linarith [H.s_pos])).mpr (aown_double H hs 5 (by decide) false)
      apply False.elim
      apply (T (sideIndex 5)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _ hp hk
      simp [linePoint, vertex, sideDirection, neighbor, sqDist]; nlinarith [H.s_pos]
  · by_cases hm : m = 0
    · subst m
      apply False.elim
      apply (T (cornerIndex 0)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
          (H.toMinAt.corner_mem 0) hk
      simp [corner, sqDist]; nlinarith [H.s_pos]
    · exact (aown_absent H hs m hm _ hhex hk).elim

/-- The small own-midpoint case uses the new cap, doubled sections and five-point geometry. -/
theorem aown_small (H : Canonical .Aown T r s) (hs : s ≤ 1 / 10) : False := by
  apply (not_le.mpr (H.toMinAt.side_lt' 0))
  apply aownCentral_obstruction H.s_pos hs (H.toMinAt.side_pos' 0)
  intro i
  fin_cases i
  · convert aown_half_core H hs 2 (by decide) (by decide) using 1; ext <;>
      simp [aownCentralPoint, coreDir]; ring
  · convert aown_half_core H hs 3 (by decide) (by decide) using 1; ext <;>
      simp [aownCentralPoint, coreDir] <;> ring
  · convert aown_half_core H hs 4 (by decide) (by decide) using 1; ext <;>
      simp [aownCentralPoint, coreDir]; ring
  · convert aown_last_point H hs using 1; ext <;> simp [aownCentralPoint]; ring
  · convert aown_half_core H hs 1 (by decide) (by decide) using 1; ext <;>
      simp [aownCentralPoint, coreDir]; ring

end ConwaySoifer.Simplified
