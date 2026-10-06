/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.SideChains
public import LeanPool.ConwaySoifer.Simplified.Geometry.ProfileWitness
import Mathlib.Tactic

/-!
# SintCorner

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
namespace ConwaySoifer
variable {T : Configuration} {r s : ℝ}

theorem Canonical.sint_corner_simplified (H : Canonical .Sint T r s) (hs : s ≤ 1 / 10)
    (hlong0 : 1 - rayLen (T (sideIndex 1)) (vertex 1) (sideDirection 1 true) <
      rayLen (T (sideIndex 0)) (vertex 0) (sideDirection 0 false))
    (hlong0' : 1 - 2 * s < rayLen (T (sideIndex 0)) (vertex 0) (sideDirection 0 false))
    (n : Fin 3) : ((Simplified.witness s n).2, (Simplified.witness s n).1) ∉ (T (cornerIndex
        0)).carrier := by
  intro hq
  set M := rayLen (T (sideIndex 1)) (vertex 1) (sideDirection 1 true) with hMdef
  set R0 := rayLen (T (sideIndex 0)) (vertex 0) (sideDirection 0 false) with hR0def
  have hv0 : vertex 0 ∈ (T (sideIndex 0)).carrier := H.toMinAt.vertex_mem 0
  have hv1 : vertex 1 ∈ (T (sideIndex 1)).carrier := H.toMinAt.vertex_mem 1
  have hw : corner 0 ∈ (T (cornerIndex 0)).carrier := H.toMinAt.corner_mem 0
  have hR0 : 0 ≤ R0 := rayLen_nonneg _ hv0 (sideDirection_unit 0 false)
  have hσ1 : (T (sideIndex 0)).side < 1 := H.toMinAt.side_lt' _
  have hσ2 : (T (sideIndex 1)).side < 1 := H.toMinAt.side_lt' _
  -- the section of `S₀` towards the corner
  set cS := rayLen (T (sideIndex 0)) (vertex 0) upDir with hcSdef
  have hc0 : 0 ≤ cS := rayLen_nonneg _ hv0 upDir_unit
  have hcR : cS + R0 ≤ r := by
    have h1 := rayLen_endpoint_mem (T (sideIndex 0)) hv0 upDir_unit
    have h2 := rayLen_endpoint_mem (T (sideIndex 0)) hv0 (sideDirection_unit 0 false)
    have hd := (T (sideIndex 0)).sqDist_le h1 h2
    rw [H.common] at hd
    have e : sqDist (linePoint (vertex 0) upDir cS) (linePoint (vertex 0) (sideDirection 0 false)
        R0) =
        (cS + R0) ^ 2 := by
      simp [linePoint, upDir, sideDirection, neighbor, vertex, sqDist]; try ring
    rw [e] at hd
    by_contra hcon
    push Not at hcon
    nlinarith [H.r_pos]
  have hcM : cS < M := by
    linarith [H.r_lt]
  have hc2s : cS < 2 * s := by
    linarith [H.r_lt]
  -- `(1, cS) ∈ A₀`
  have hpM : linePoint (vertex 1) (sideDirection 1 true) M ∈ (T (sideIndex 1)).carrier :=
    rayLen_endpoint_mem _ hv1 (sideDirection_unit 1 true)
  have hcA : linePoint (vertex 0) upDir cS ∈ (T (cornerIndex 0)).carrier := by
    obtain ⟨k, hk1, hk⟩ := rayLen_transfers T H.covers (sideIndex 0) hv0 upDir_unit (b := 1)
      (by linarith [H.s_lt]) (fun t ht => by
        rw [upPt_eq_cornerSeg]
        exact cornerSeg_mem_target 0 0 (by linarith [ht.2]) (by linarith [ht.1]))
    rw [upPt_eq_cornerSeg] at hk
    have hallow := cornerSeg_owner_allowed H.common H.r_lt H.anchored 0 0 (t := 1 - cS)
      (by linarith) (by linarith) hk
    rcases cornerAllowed_cases 0 k hallow with rfl | rfl | rfl
    · rw [← upPt_eq_cornerSeg] at hk; exact hk
    · exact (hk1 (by decide)).elim
    · exfalso
      rw [← upPt_eq_cornerSeg] at hk
      refine (T (sideIndex 1)).cannot_contain_unit_chord hσ2 ?_ hpM hk
      have e : sqDist (linePoint (vertex 1) (sideDirection 1 true) M) (linePoint (vertex 0) upDir
          cS) =
          (1 + M) ^ 2 - (1 + M) * (1 - cS) + (1 - cS) ^ 2 := by
        simp [linePoint, sideDirection, neighbor, vertex, upDir, sqDist]; ring
      rw [e]; nlinarith [hcM, hc0]
  -- the section of `A₀` towards `v₁` exceeds `M`
  set lam := rayLen (T (cornerIndex 0)) (corner 0) (cornerDirection 0 1) with hlamdef
  have hl0 : 0 ≤ lam := rayLen_nonneg _ hw (cornerDirection_unit 0 1)
  have hlamM : M < lam := by
    by_contra hcon
    push Not at hcon
    have hcov : ∀ t ∈ Set.Ioo lam 1,
        linePoint (corner 0) (cornerDirection 0 1) t ∈ (T (sideIndex 1)).carrier := by
      intro t ht
      obtain ⟨k, hk⟩ := H.covers _ (cornerSeg_mem_target 0 1 (by linarith [ht.1]) ht.2.le)
      have hallow := cornerSeg_owner_allowed H.common H.r_lt H.anchored 0 1 (by linarith [ht.1])
        ht.2.le hk
      rcases cornerAllowed_cases 0 k hallow with rfl | rfl | rfl
      · exact absurd hk (not_mem_after_rayLen _ hw (cornerDirection_unit 0 1) ht.1)
      · exfalso
        have hpR : linePoint (vertex 0) (sideDirection 0 false) R0 ∈ (T (sideIndex 0)).carrier :=
          rayLen_endpoint_mem _ hv0 (sideDirection_unit 0 false)
        refine (T (sideIndex 0)).cannot_contain_unit_chord hσ1 ?_ hpR hk
        simp [linePoint, sideDirection, neighbor, vertex, corner, cornerDirection, sqDist]
        nlinarith [sq_nonneg (t - (1 + R0) / 2), hlong0', hs]
      · exact hk
    have hlam1 : lam < 1 := by
      have := rayLen_le_side _ hw (cornerDirection_unit 0 1)
      linarith [H.toMinAt.side_lt' (cornerIndex 0)]
    have hend := closed_cover_endpoint (T (sideIndex 1)).isClosed_carrier
      (continuous_linePoint _ _) hlam1 hcov
    refine (T (sideIndex 1)).cannot_contain_unit_chord hσ2 ?_ hend hpM
    have e : sqDist (linePoint (corner 0) (cornerDirection 0 1) lam)
        (linePoint (vertex 1) (sideDirection 1 true) M) = (1 - lam + M) ^ 2 := by
      simp [linePoint, sideDirection, neighbor, vertex, corner, cornerDirection, sqDist]; ring
    rw [e]; nlinarith [hcon, hl0]
  -- the piece of the profile containing `cS`
  have hpt : ∀ k : Fin 8, (k.val : ℝ) * s / 4 ≤ cS → cS ≤ ((k.val : ℝ) + 1) * s / 4 → False := by
    intro k hk1 hk2
    have hk4 : (k.val : ℝ) ≤ 7 := by
      have := k.isLt; exact_mod_cast Nat.lt_succ_iff.mp this
    have he : ((1 : ℝ), ((k.val : ℝ) + 1) * s / 4) ∈ (T (cornerIndex 0)).carrier := by
      have hmem := linePoint_between (T (cornerIndex 0)).convex_carrier hw (d := cornerDirection 0
          0)
        (u := 1 - cS) (t := 1 - ((k.val : ℝ) + 1) * s / 4)
        (by rw [← upPt_eq_cornerSeg]; exact hcA) (by nlinarith [H.s_pos]) (by linarith)
      convert hmem using 1
      apply Prod.ext <;> simp [linePoint, corner, cornerDirection, vertex]
    have hf : (1 - (k.val : ℝ) * s / 4, (1 : ℝ)) ∈ (T (cornerIndex 0)).carrier := by
      have hmem := (linePoint_mem_iff_le_rayLen (T (cornerIndex 0)) hw (cornerDirection_unit 0 1)
        (t := (k.val : ℝ) * s / 4) (by have := H.s_pos; positivity)).mpr (by linarith)
      convert hmem using 1
      apply Prod.ext <;> simp [linePoint, corner, cornerDirection, vertex]; ring
    exact (not_le.mpr (H.toMinAt.side_lt' _)) (Simplified.profile_witness H.s_pos hs
      (H.toMinAt.side_pos' _) k n hw he hf hq)
  by_cases h0 : cS ≤ 1 * s / 4
  · exact hpt 0 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h1 : cS ≤ 2 * s / 4
  · exact hpt 1 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h2 : cS ≤ 3 * s / 4
  · exact hpt 2 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h3 : cS ≤ 4 * s / 4
  · exact hpt 3 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h4 : cS ≤ 5 * s / 4
  · exact hpt 4 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h5 : cS ≤ 6 * s / 4
  · exact hpt 5 (by norm_num; linarith) (by norm_num; linarith)
  by_cases h6 : cS ≤ 7 * s / 4
  · exact hpt 6 (by norm_num; linarith) (by norm_num; linarith)
  exact hpt 7 (by norm_num; linarith) (by norm_num; linarith)

end ConwaySoifer
