/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.CornerAbsent
import Mathlib.Tactic

/-!
# Charging

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
open MeasureTheory
namespace ConwaySoifer.Simplified

variable {c : ContactCase} {T : Configuration} {r s : ℝ}

/-- A corner cap is paid by a side owner with loss at least `r²/4`. -/
def penalty (T : Configuration) (r : ℝ) (i : Fin 6) : ℝ :=
  if r ^ 2 / 4 ≤ sideLoss T i then r ^ 2 / 23 else 0

/-- Abstract charging: each corner chooses a missing midpoint; locality assigns
it to one of that corner's two side owners. Summing counts each side once. -/
theorem cornerHelp_le_charges (H : Canonical c T r s) (charge : Fin 6 → ℝ)
    (hnonneg : ∀ i, 0 ≤ charge i)
    (hpay : ∀ (j : Fin 3) (m : Fin 2) (i : Fin 6),
      cornerMid j m ∈ (T (sideIndex i)).carrier → r ^ 2 / 23 ≤ charge i) :
    (∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j) ≤ ∑ i : Fin 6, charge i := by
  have hj (j : Fin 3) : H.toMinAt.toAnchored.cornerHelp j ≤
      charge ⟨2 * j.val, by omega⟩ + charge ⟨2 * j.val + 1, by omega⟩ := by
    by_cases hm : ∀ m, cornerMid j m ∈ (T (cornerIndex j)).carrier
    · have he : (T (cornerIndex j)).carrier ∩ hexagon = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro p ⟨hp, hhex⟩
        exact H.corner_absent_simplified j hm hhex hp
      change 2 * (volume ((T (cornerIndex j)).carrier ∩ hexagon)).toReal ≤ _
      rw [he, measure_empty, ENNReal.toReal_zero, mul_zero]
      exact add_nonneg (hnonneg _) (hnonneg _)
    · push Not at hm
      obtain ⟨m, hm⟩ := hm
      obtain ⟨k, hk⟩ := H.covers _ (cornerSeg_mem_target j m (t := 1 / 2)
        (by norm_num) (by norm_num))
      have ha := cornerSeg_owner_allowed H.common H.r_lt H.anchored j m
        (t := 1 / 2) (by norm_num) (by norm_num) hk
      rcases cornerAllowed_cases j k ha with rfl | rfl | rfl
      · exact (hm hk).elim
      · have hp := hpay j m _ hk
        have hc := H.toMinAt.cornerHelp_lt j
        linarith [hnonneg ⟨2 * j.val + 1, by omega⟩]
      · have hp := hpay j m _ hk
        have hc := H.toMinAt.cornerHelp_lt j
        linarith [hnonneg ⟨2 * j.val, by omega⟩]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hj j)
  convert hh using 1
  simp [Fin.sum_univ_three, Fin.sum_univ_six]
  ring

theorem charged_budget (H : Canonical c T r s) :
    (∑ i : Fin 6, (sideLoss T i - penalty T r i)) ≤ 7 * r ^ 2 - 6 := by
  have hh := cornerHelp_le_charges H (penalty T r)
    (fun i => by unfold penalty; split_ifs <;> positivity)
    (fun j m i hm => by rw [penalty, ite_eq_left (H.loss_mid i j m hm)])
  have hb := H.toMinAt.toAnchored.area_budget
  have hb' : (∑ i : Fin 6, sideLoss T i) ≤
      7 * r ^ 2 - 6 + ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j := hb
  rw [Finset.sum_sub_distrib]
  linarith

theorem section_sq_lt (H : Canonical c T r s) : s ^ 2 < 13 * r ^ 2 / 69 := by
  have hb := H.toMinAt.toAnchored.area_budget
  have ho : 6 * s ^ 2 ≤ ∑ i : Fin 6, H.toMinAt.toAnchored.outside i := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) =>
      H.toMinAt.outside_ge i)
  have hh : (∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j) < 3 * (r ^ 2 / 23) := by
    simpa using Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => H.toMinAt.cornerHelp_lt j)
  have hr : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  linarith

theorem effective_loss_ge (H : Canonical c T r s) (i : Fin 6) :
    s ^ 2 ≤ sideLoss T i - penalty T r i := by
  have hg := section_sq_lt H
  have hr : 0 ≤ r ^ 2 := sq_nonneg r
  unfold penalty
  split_ifs with hi
  · linarith
  · simpa using H.loss_ge_sq i

theorem penalty_le (i : Fin 6) : penalty T r i ≤ r ^ 2 / 23 := by
  unfold penalty
  split_ifs <;> nlinarith [sq_nonneg r]

/-- The strengthened upper endpoint for internal transfer. -/
theorem sint_upper (H : Canonical .Sint T r s) : s < 9 / 25 := by
  have hb := charged_budget H
  have hrecv := H.loss_recv trivial
  have hp := penalty_le (T := T) (r := r) (recvOf .Sint)
  have hlo (i : Fin 6) : (if i = recvOf .Sint then (1 - s) ^ 2 - r ^ 2 / 23 else s ^ 2) ≤
      sideLoss T i - penalty T r i := by
    split_ifs with hi
    · subst i; linarith
    · exact effective_loss_ge H i
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hlo i)
  have he : (∑ i : Fin 6, if i = recvOf .Sint then (1 - s) ^ 2 - r ^ 2 / 23 else s ^ 2) =
      (1 - s) ^ 2 - r ^ 2 / 23 + 5 * s ^ 2 := by
    simp [recvOf_Sint, Fin.sum_univ_six]; ring
  rw [he] at hh
  have hr : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  by_contra hs
  push Not at hs
  nlinarith [sq_nonneg (s - 9 / 25)]

/-- In the small side cases no nonreceiver can have midpoint-sized loss. -/
theorem small_side_no_cost (H : Canonical c T r s) (hS : c.isS) (hs : s ≤ 1 / 10)
    (i : Fin 6) (hi : i ≠ recvOf c) : sideLoss T i < r ^ 2 / 4 := by
  by_contra hcost
  push Not at hcost
  have hb := charged_budget H
  have hr : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  have hrecv := H.loss_recv hS
  have hp := penalty_le (T := T) (r := r) (recvOf c)
  have hlo (k : Fin 6) :
      (if k = i then r ^ 2 / 4 - r ^ 2 / 23 else
        if k = recvOf c then (1 - s) ^ 2 - r ^ 2 / 23 else s ^ 2) ≤
      sideLoss T k - penalty T r k := by
    split_ifs with hki hkr
    · subst k; rw [penalty, ite_eq_left hcost]; linarith
    · subst k; linarith
    · exact effective_loss_ge H k
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 6))) => hlo k)
  have he : (∑ k : Fin 6, if k = i then r ^ 2 / 4 - r ^ 2 / 23 else
        if k = recvOf c then (1 - s) ^ 2 - r ^ 2 / 23 else s ^ 2) =
      r ^ 2 / 4 - 2 * r ^ 2 / 23 + (1 - s) ^ 2 + 4 * s ^ 2 := by
    rcases H.recv_cases hS with he | he <;> rw [he] at hi ⊢ <;>
      fin_cases i <;> simp [Fin.sum_univ_six] at hi ⊢ <;> ring
  rw [he] at hh
  have hm : 0 ≤ (1 / 10 - s) * (3 / 2 - 5 * s) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The external receiver cannot pay for any corner midpoint. -/
theorem sext_receiver_no_mid (H : Canonical .Sext T r s) (j : Fin 3) (m : Fin 2) :
    cornerMid j m ∉ (T (sideIndex 5)).carrier := by
  fin_cases j
  · intro hm
    apply (T (sideIndex 5)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
      (H.toMinAt.vertex_mem 5) hm
    fin_cases m <;> dsimp [vertex, cornerMid, cornerDirection, corner, sqDist] <;> norm_num
  · intro hm
    apply (T (sideIndex 5)).cannot_contain_unit_chord (H.toMinAt.side_lt' _) _
      (H.toMinAt.vertex_mem 5) hm
    fin_cases m <;> dsimp [vertex, cornerMid, cornerDirection, corner, sqDist] <;> norm_num
  · exact H.sext_recv_noMid m

/-- The side-owner penalty with the Sext receiver's contribution set to zero. -/
def sextPenalty (T : Configuration) (r : ℝ) (i : Fin 6) : ℝ :=
  if i = 5 then 0 else penalty T r i

theorem sext_charged_budget (H : Canonical .Sext T r s) :
    (∑ i : Fin 6, (sideLoss T i - sextPenalty T r i)) ≤ 7 * r ^ 2 - 6 := by
  have hh := cornerHelp_le_charges H (sextPenalty T r)
    (fun i => by unfold sextPenalty penalty; split_ifs <;> positivity)
    (fun j m i hm => by
      by_cases hi : i = 5
      · subst i; exact (sext_receiver_no_mid H j m hm).elim
      · rw [sextPenalty, ite_eq_right hi, penalty, ite_eq_left (H.loss_mid i j m hm)])
  have hb : (∑ i : Fin 6, sideLoss T i) ≤
      7 * r ^ 2 - 6 + ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j :=
    H.toMinAt.toAnchored.area_budget
  rw [Finset.sum_sub_distrib]
  linarith

theorem sext_effective_ge (H : Canonical .Sext T r s) (i : Fin 6) :
    s ^ 2 ≤ sideLoss T i - sextPenalty T r i := by
  unfold sextPenalty
  split_ifs
  · simpa using H.loss_ge_sq i
  · exact effective_loss_ge H i

theorem sext_no_cost (H : Canonical .Sext T r s) (i : Fin 6) (hi : i ≠ 5) :
    sideLoss T i < r ^ 2 / 4 := by
  by_contra hcost
  push Not at hcost
  have hb := sext_charged_budget H
  have hr : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  have hrecv : (1 - s) ^ 2 ≤ sideLoss T 5 := by
    simpa [recvOf_Sext] using H.loss_recv trivial
  have hlo (k : Fin 6) :
      (if k = i then r ^ 2 / 4 - r ^ 2 / 23 else if k = 5 then (1 - s) ^ 2 else s ^ 2) ≤
      sideLoss T k - sextPenalty T r k := by
    split_ifs with hki hkr
    · subst k; rw [sextPenalty, ite_eq_right hi, penalty, ite_eq_left hcost]; linarith
    · subst k; simpa [sextPenalty] using hrecv
    · exact sext_effective_ge H k
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 6))) => hlo k)
  have he : (∑ k : Fin 6, if k = i then r ^ 2 / 4 - r ^ 2 / 23 else
      if k = 5 then (1 - s) ^ 2 else s ^ 2) =
      r ^ 2 / 4 - r ^ 2 / 23 + (1 - s) ^ 2 + 4 * s ^ 2 := by
    fin_cases i <;> simp [Fin.sum_univ_six] at hi ⊢ <;> ring
  rw [he] at hh
  nlinarith [sq_nonneg (s - 1 / 5)]

/-- External transfer is impossible at and above `1/3`. -/
theorem sext_upper (H : Canonical .Sext T r s) : s < 1 / 3 := by
  have hb := sext_charged_budget H
  have hzero (i : Fin 6) : sextPenalty T r i = 0 := by
    unfold sextPenalty
    split_ifs with hi
    · rfl
    · exact ite_eq_right (not_le.mpr (sext_no_cost H i hi))
  simp_rw [hzero, sub_zero] at hb
  have hrecv : (1 - s) ^ 2 ≤ sideLoss T 5 := by
    simpa [recvOf_Sext] using H.loss_recv trivial
  have hlo (i : Fin 6) : (if i = 5 then (1 - s) ^ 2 else s ^ 2) ≤ sideLoss T i := by
    split_ifs with hi
    · subst i; exact hrecv
    · exact H.loss_ge_sq i
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hlo i)
  have he : (∑ i : Fin 6, if i = 5 then (1 - s) ^ 2 else s ^ 2) = (1 - s) ^ 2 + 5 * s ^ 2 := by
    simp [Fin.sum_univ_six]; ring
  rw [he] at hh
  have hr : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  by_contra hs
  push Not at hs
  nlinarith [mul_nonneg H.s_pos.le (sub_nonneg.mpr hs)]

end ConwaySoifer.Simplified
