/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.Charging
public import LeanPool.ConwaySoifer.Simplified.Geometry.Bridge
import Mathlib.Tactic

/-!
# SideChains

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
variable {c : ContactCase} {T : Configuration} {r s : ℝ}

theorem Canonical.s_nonOverfull_simplified (H : Canonical c T r s) (hS : c.isS)
    (hs : s ≤ 1 / 10) (i : Fin 6) (hi : i ≠ recvOf c) :
    rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r := by
  by_contra hover
  push Not at hover
  exact (not_le.mpr (Simplified.small_side_no_cost H hS hs i hi)) (H.loss_overfull i hover)

theorem Canonical.s_noMid_simplified (H : Canonical c T r s) (hS : c.isS)
    (hs : s ≤ 1 / 10) (i : Fin 6) (hi : i ≠ recvOf c) (j : Fin 3) (m : Fin 2) :
    cornerMid j m ∉ (T (sideIndex i)).carrier := by
  intro hm
  exact (not_le.mpr (Simplified.small_side_no_cost H hS hs i hi)) (H.loss_mid i j m hm)

theorem Canonical.s_corner_mids_simplified (H : Canonical c T r s) (hS : c.isS) (hs : s ≤ 1 / 10) (j
    : Fin 3)
    (hj : c = .Sint → j ≠ 0) (m : Fin 2) : cornerMid j m ∈ (T (cornerIndex j)).carrier := by
  refine H.corner_mids j m ?_ ?_
  · refine H.s_noMid_simplified hS hs _ ?_ j m
    cases c
    · rw [recvOf_Sext]; fin_cases j <;> decide
    · rw [recvOf_Sint]; fin_cases j <;> decide
    · exact hS.elim
    · exact hS.elim
  · cases c
    · fin_cases j
      · exact H.s_noMid_simplified hS hs _ (by rw [recvOf_Sext]; decide) 0 m
      · exact H.s_noMid_simplified hS hs _ (by rw [recvOf_Sext]; decide) 1 m
      · exact H.sext_recv_noMid m
    · fin_cases j
      · exact absurd rfl (hj rfl)
      · exact H.s_noMid_simplified hS hs _ (by rw [recvOf_Sint]; decide) 1 m
      · exact H.s_noMid_simplified hS hs _ (by rw [recvOf_Sint]; decide) 2 m
    · exact hS.elim
    · exact hS.elim

theorem Canonical.centre_far_simplified (H : Canonical c T r s)
    (hs : s ≤ 1 / 3) (i : Fin 6) (dir : Bool) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 2 * s) :
    linePoint (vertex i) (sideDirection i dir) t ∉ (T 0).carrier := by
  intro hp
  have hs2 : s ≤ 1 / 2 := by
    linarith
  refine Simplified.bridge_all_exclusion (u := t / 2) (by linarith) (by linarith) i dir
      (H.toMinAt.side_pos' 0)
    (H.toMinAt.side_lt' 0) ?_ ?_
  · intro j
    exact coreVertex_mem_of_le (T 0).convex_carrier H.toMinAt.zero_mem H.core H.s_pos hs2
      (by linarith) (by linarith) j
  · rwa [show 2 * (t / 2) = t by ring]

theorem Canonical.chain_step_simplified (H : Canonical c T r s)
    (hs : s ≤ 1 / 3) (i : Fin 6) (dir : Bool)
    (hM : rayLen (T (sideIndex i)) (vertex i) (sideDirection i dir) < 2 * s)
    (hA : ∀ j : Fin 3, sideAllowed (sideOf i dir) (cornerIndex j) = true →
      ∀ p ∈ hexagon, p ∉ (T (cornerIndex j)).carrier) :
    1 - rayLen (T (sideIndex i)) (vertex i) (sideDirection i dir) ≤
      rayLen (T (sideIndex (neighbor i dir))) (vertex (neighbor i dir))
        (sideDirection (neighbor i dir) (!dir)) := by
  have hv := H.toMinAt.vertex_mem i
  set M := rayLen (T (sideIndex i)) (vertex i) (sideDirection i dir) with hMdef
  have hM0 : 0 ≤ M := rayLen_nonneg _ hv (sideDirection_unit i dir)
  have h2s : 2 * s < 1 := by
    linarith [H.s_lt]
  have hcov : ∀ t ∈ Set.Ioo M (2 * s), linePoint (vertex i) (sideDirection i dir) t ∈
      (T (sideIndex (neighbor i dir))).carrier := by
    intro t ht
    have ht0 : 0 ≤ t := by
      linarith [ht.1]
    have ht1 : t ≤ 1 := by
      linarith [ht.2]
    obtain ⟨k, hk⟩ := H.covers _ (sidePoint_mem_target i dir ⟨ht0, ht1⟩)
    rcases sideAllowed_cases i dir k (H.sidePoint_allowed i dir ht0 ht1 hk) with
      rfl | rfl | rfl | ⟨j, rfl, hj⟩
    · exact absurd hk (H.centre_far_simplified hs i dir (by linarith [ht.1]) ht.2.le)
    · exact absurd hk (not_mem_after_rayLen _ hv (sideDirection_unit i dir) ht.1)
    · exact hk
    · exact absurd hk (hA j hj _ (sidePoint_mem_hexagon i dir ht0 ht1))
  have hend := closed_cover_endpoint (T (sideIndex (neighbor i dir))).isClosed_carrier
    (continuous_linePoint _ _) hM hcov
  rw [sidePoint_flip] at hend
  exact (linePoint_mem_iff_le_rayLen _ (H.toMinAt.vertex_mem _) (sideDirection_unit _ _)
    (by linarith)).mp hend

/-- One step of the chain: the next owner receives at least `1 - M` and its own short section
is below `M`. -/
theorem Canonical.chain_next_simplified (H : Canonical c T r s)
    (hs : s ≤ 1 / 3) (i : Fin 6) (dir : Bool) (nb : Fin 6) (hnb : neighbor i dir = nb)
    (hM : rayLen (T (sideIndex i)) (vertex i) (sideDirection i dir) < 2 * s)
    (hA : ∀ j : Fin 3, sideAllowed (sideOf i dir) (cornerIndex j) = true →
      ∀ p ∈ hexagon, p ∉ (T (cornerIndex j)).carrier)
    (hno : rayLen (T (sideIndex nb)) (vertex nb) (sideDirection nb false) +
      rayLen (T (sideIndex nb)) (vertex nb) (sideDirection nb true) ≤ r) :
    1 - rayLen (T (sideIndex i)) (vertex i) (sideDirection i dir) ≤
        rayLen (T (sideIndex nb)) (vertex nb) (sideDirection nb (!dir)) ∧
      rayLen (T (sideIndex nb)) (vertex nb) (sideDirection nb dir) <
        rayLen (T (sideIndex i)) (vertex i) (sideDirection i dir) := by
  have h1 := H.chain_step_simplified hs i dir hM hA
  rw [hnb] at h1
  refine ⟨h1, ?_⟩
  cases dir
  · simp only [Bool.not_false] at h1 ⊢; linarith [H.r_lt]
  · simp only [Bool.not_true] at h1 ⊢; linarith [H.r_lt]

theorem Canonical.sint_chain_simplified (H : Canonical .Sint T r s)
    (hs : s ≤ 1 / 10)
    (hno : ∀ i : Fin 6, i ≠ 1 → rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r)
    (hA1 : ∀ p ∈ hexagon, p ∉ (T (cornerIndex 1)).carrier)
    (hA2 : ∀ p ∈ hexagon, p ∉ (T (cornerIndex 2)).carrier) :
    (∀ i : Fin 6, i ≠ 1 →
        1 - 2 * s < rayLen (T (sideIndex i)) (vertex i) (sideDirection i false)) ∧
      1 - rayLen (T (sideIndex 1)) (vertex 1) (sideDirection 1 true) <
        rayLen (T (sideIndex 0)) (vertex 0) (sideDirection 0 false) := by
  have hs3 : s ≤ 1 / 3 := by
    linarith
  have hM1 : rayLen (T (sideIndex 1)) (vertex 1) (sideDirection 1 true) < 2 * s := by
    have := H.recv_short_lt trivial
    rwa [recvOf_Sint, show ContactCase.right .Sint = true from rfl] at this
  obtain ⟨h2, hM2⟩ := H.chain_next_simplified hs3 1 true 2 (by decide) hM1
    (by intro j hj; exfalso; revert hj; fin_cases j <;> decide) (hno 2 (by decide))
  obtain ⟨h3, hM3⟩ := H.chain_next_simplified hs3 2 true 3 (by decide) (hM2.trans hM1)
    (by intro j hj; fin_cases j <;> first | exact absurd hj (by decide) | exact hA1)
    (hno 3 (by decide))
  obtain ⟨h4, hM4⟩ := H.chain_next_simplified hs3 3 true 4 (by decide) (by linarith)
    (by intro j hj; exfalso; revert hj; fin_cases j <;> decide) (hno 4 (by decide))
  obtain ⟨h5, hM5⟩ := H.chain_next_simplified hs3 4 true 5 (by decide) (by linarith)
    (by intro j hj; fin_cases j <;> first | exact absurd hj (by decide) | exact hA2)
    (hno 5 (by decide))
  obtain ⟨h0, hM0⟩ := H.chain_next_simplified hs3 5 true 0 (by decide) (by linarith)
    (by intro j hj; exfalso; revert hj; fin_cases j <;> decide) (hno 0 (by decide))
  simp only [Bool.not_true] at h2 h3 h4 h5 h0
  refine ⟨?_, by linarith⟩
  intro i hi
  have hcases : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    revert hi; revert i; decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> linarith

theorem Canonical.sext_chain_simplified (H : Canonical .Sext T r s)
    (hs : s ≤ 1 / 10)
    (hno : ∀ i : Fin 6, i ≠ 5 → rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r)
    (hA0 : ∀ p ∈ hexagon, p ∉ (T (cornerIndex 0)).carrier)
    (hA1 : ∀ p ∈ hexagon, p ∉ (T (cornerIndex 1)).carrier)
    (hA2 : ∀ p ∈ hexagon, p ∉ (T (cornerIndex 2)).carrier) :
    ∀ i : Fin 6, i ≠ 5 →
      1 - 2 * s < rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) := by
  have hs3 : s ≤ 1 / 3 := by
    linarith
  have hM5 : rayLen (T (sideIndex 5)) (vertex 5) (sideDirection 5 false) < 2 * s := by
    have := H.recv_short_lt trivial
    rwa [recvOf_Sext, show ContactCase.right .Sext = false from rfl] at this
  obtain ⟨h4, hM4⟩ := H.chain_next_simplified hs3 5 false 4 (by decide) hM5
    (by intro j hj; fin_cases j <;> first | exact absurd hj (by decide) | exact hA2)
    (hno 4 (by decide))
  obtain ⟨h3, hM3⟩ := H.chain_next_simplified hs3 4 false 3 (by decide) (hM4.trans hM5)
    (by intro j hj; exfalso; revert hj; fin_cases j <;> decide) (hno 3 (by decide))
  obtain ⟨h2, hM2⟩ := H.chain_next_simplified hs3 3 false 2 (by decide) (by linarith)
    (by intro j hj; fin_cases j <;> first | exact absurd hj (by decide) | exact hA1)
    (hno 2 (by decide))
  obtain ⟨h1, hM1⟩ := H.chain_next_simplified hs3 2 false 1 (by decide) (by linarith)
    (by intro j hj; exfalso; revert hj; fin_cases j <;> decide) (hno 1 (by decide))
  obtain ⟨h0, hM0⟩ := H.chain_next_simplified hs3 1 false 0 (by decide) (by linarith)
    (by intro j hj; fin_cases j <;> first | exact absurd hj (by decide) | exact hA0)
    (hno 0 (by decide))
  simp only [Bool.not_false] at h4 h3 h2 h1 h0
  intro i hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    revert hi; revert i; decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> linarith

end ConwaySoifer
