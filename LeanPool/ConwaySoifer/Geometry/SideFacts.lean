/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.AcrossFacts
public import LeanPool.ConwaySoifer.Geometry.ReceiverFacts
import Mathlib.Tactic

/-! Shared geometric facts for both small-case proofs; no certificate evaluations. -/

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
namespace ConwaySoifer
variable {c : ContactCase} {T : Configuration} {r s : ℝ}

/-! ### The receiver -/

theorem minEndpoint_eq_recv (c : ContactCase) (s : ℝ) :
    minEndpoint c s =
      linePoint (vertex (recvOf c)) (sideDirection (recvOf c) (!c.right)) (1 - s) := by
  cases c <;> apply Prod.ext <;>
    simp [minEndpoint, linePoint, sideDirection, neighbor, vertex, recvOf, ContactCase.right] <;>
    ring

theorem Canonical.recv_mem (H : Canonical c T r s) (hS : c.isS) :
    minEndpoint c s ∈ (T (sideIndex (recvOf c))).carrier := by
  cases c
  · have e : sideIndex (recvOf .Sext) = 6 := by
      decide
    rw [e]; exact H.contact
  · have e : sideIndex (recvOf .Sint) = 2 := by
      decide
    rw [e]; exact H.contact
  · exact hS.elim
  · exact hS.elim

theorem Canonical.recv_long (H : Canonical c T r s) (hS : c.isS) :
    1 - s ≤ rayLen (T (sideIndex (recvOf c))) (vertex (recvOf c))
      (sideDirection (recvOf c) (!c.right)) := by
  have hv := H.toMinAt.vertex_mem (recvOf c)
  rw [← linePoint_mem_iff_le_rayLen _ hv (sideDirection_unit _ _) (by linarith [H.s_lt]),
    ← minEndpoint_eq_recv]
  exact H.recv_mem hS

theorem sqDist_sidePts (i : Fin 6) (dir : Bool) (a b : ℝ) :
    sqDist (linePoint (vertex i) (sideDirection i dir) a)
      (linePoint (vertex i) (sideDirection i (!dir)) b) = a ^ 2 + a * b + b ^ 2 := by
  cases dir <;> fin_cases i <;> simp [linePoint, sideDirection, neighbor, vertex, sqDist] <;> ring

/-- The short section of the receiver is below `2s`. -/
theorem Canonical.recv_short_lt (H : Canonical c T r s) (hS : c.isS) :
    rayLen (T (sideIndex (recvOf c))) (vertex (recvOf c)) (sideDirection (recvOf c) c.right) <
      2 * s := by
  set i := recvOf c
  have hv := H.toMinAt.vertex_mem i
  have hlong := H.recv_long hS
  set M := rayLen (T (sideIndex i)) (vertex i) (sideDirection i c.right) with hM
  have hM0 : 0 ≤ M := rayLen_nonneg _ hv (sideDirection_unit _ _)
  have hpM : linePoint (vertex i) (sideDirection i c.right) M ∈ (T (sideIndex i)).carrier :=
    rayLen_endpoint_mem _ hv (sideDirection_unit _ _)
  have hpL : linePoint (vertex i) (sideDirection i (!c.right)) (1 - s) ∈
      (T (sideIndex i)).carrier :=
    (linePoint_mem_iff_le_rayLen _ hv (sideDirection_unit _ _) (by linarith [H.s_lt])).mpr hlong
  have hd := (T (sideIndex i)).sqDist_le hpM hpL
  rw [H.common, sqDist_sidePts] at hd
  have hr2 : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg (sub_nonneg.2 hcon) (by linarith [H.s_pos] : (0 : ℝ) ≤ M + s + 1)]

/-! ### The budget -/

theorem Canonical.loss_recv (H : Canonical c T r s) (hS : c.isS) :
    (1 - s) ^ 2 ≤ sideLoss T (recvOf c) := by
  set i := recvOf c
  have hv := H.toMinAt.vertex_mem i
  set L := rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) with hL
  set R := rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) with hR
  have hL0 : 0 ≤ L := rayLen_nonneg _ hv (sideDirection_unit i false)
  have hR0 : 0 ≤ R := rayLen_nonneg _ hv (sideDirection_unit i true)
  have hLs : s ≤ L := H.side_min i false
  have hRs : s ≤ R := H.side_min i true
  have hlong := H.recv_long hS
  have hbig : 1 - s ≤ L ∨ 1 - s ≤ R := by
    rcases Bool.eq_false_or_eq_true c.right with hr | hr
    · rw [hr] at hlong; simp only [Bool.not_true] at hlong; left; exact hlong
    · rw [hr] at hlong; simp only [Bool.not_false] at hlong; right; exact hlong
  have hs1 : 0 ≤ 1 - s := by
    linarith [H.s_lt]
  have hw := wedge_area_strong i (T (sideIndex i)) (by rw [H.common]; exact H.r_pos) hL0 hR0 hv
    (rayLen_endpoint_mem _ hv (sideDirection_unit i false))
    (rayLen_endpoint_mem _ hv (sideDirection_unit i true))
    (by rw [H.common]; rcases hbig with h | h <;> linarith [H.r_lt])
  have hmax : (1 - s) ^ 2 ≤ max (L ^ 2) (R ^ 2) := by
    rcases hbig with h | h
    · exact le_max_of_le_left (by nlinarith [mul_self_le_mul_self hs1 h])
    · exact le_max_of_le_right (by nlinarith [mul_self_le_mul_self hs1 h])
  unfold sideLoss; linarith

theorem Canonical.recv_cases (H : Canonical c T r s) (hS : c.isS) :
    recvOf c = 5 ∨ recvOf c = 1 := by
  cases c
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact hS.elim
  · exact hS.elim

/-- The budget of an `S` cover with `s ≤ 1/14`: no other side owner can lose `r²/4`. -/
theorem Canonical.s_budget (H : Canonical c T r s) (hS : c.isS) (hs : s ≤ 1 / 14) (i : Fin 6)
    (hi : i ≠ recvOf c) (hD : r ^ 2 / 4 ≤ sideLoss T i) : False := by
  have hbudget := H.toMinAt.toAnchored.area_budget
  have hout : ∀ k, H.toMinAt.toAnchored.outside k = sideLoss T k := fun k => rfl
  have hhelp : ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j < 3 * (r ^ 2 / 23) := by
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => H.toMinAt.cornerHelp_lt j)
    simpa using this
  have h0 := H.loss_recv hS
  have hsq := H.loss_ge_sq
  have hlow : ∀ k : Fin 6,
      (if k = i then r ^ 2 / 4 else if k = recvOf c then (1 - s) ^ 2 else s ^ 2) ≤
        sideLoss T k := by
    intro k
    split_ifs with hki hk0
    · subst hki; exact hD
    · subst hk0; exact h0
    · exact hsq k
  have hsum' := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 6))) => hlow k)
  have hval : ∑ k : Fin 6,
      (if k = i then r ^ 2 / 4 else if k = recvOf c then (1 - s) ^ 2 else s ^ 2) =
        r ^ 2 / 4 + (1 - s) ^ 2 + 4 * s ^ 2 := by
    rcases H.recv_cases hS with hr | hr <;> rw [hr] at hi ⊢ <;>
      fin_cases i <;> simp [Fin.sum_univ_six] at hi ⊢ <;> ring
  rw [hval] at hsum'
  have hsum : ∑ k : Fin 6, sideLoss T k ≥ r ^ 2 / 4 + (1 - s) ^ 2 + 4 * s ^ 2 := hsum'
  have hbudget' : ∑ k : Fin 6, sideLoss T k ≤
      7 * r ^ 2 - 6 + ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j := hbudget
  have hr2 : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  have hkey : 0 ≤ (1 / 14 - s) * (23 / 14 - 5 * s) := mul_nonneg (by linarith) (by linarith)
  have hkey' : 0 ≤ 5 * s ^ 2 - 2 * s + 11 / 92 := by
    nlinarith [hkey]
  linarith

theorem Canonical.s_nonOverfull (H : Canonical c T r s) (hS : c.isS) (hs : s ≤ 1 / 14) (i : Fin 6)
    (hi : i ≠ recvOf c) :
    rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r := by
  by_contra hover
  push Not at hover
  exact H.s_budget hS hs i hi (H.loss_overfull i hover)

theorem Canonical.s_noMid (H : Canonical c T r s) (hS : c.isS) (hs : s ≤ 1 / 14) (i : Fin 6)
    (hi : i ≠ recvOf c) (j : Fin 3) (m : Fin 2) : cornerMid j m ∉ (T (sideIndex i)).carrier :=
  fun hm => H.s_budget hS hs i hi (H.loss_mid i j m hm)

/-! ### Corner owners -/

/-- In `Sext` the receiver `S₅` is far from the midpoints of its own cell. -/
theorem Canonical.sext_recv_noMid (H : Canonical .Sext T r s) (m : Fin 2) :
    cornerMid 2 m ∉ (T 6).carrier := by
  intro hm
  have hp : minEndpoint .Sext s ∈ (T 6).carrier := H.contact
  refine (T 6).cannot_contain_unit_chord (by rw [H.common]; exact H.r_lt) ?_ hp hm
  have := H.s_pos
  have := H.s_lt
  fin_cases m
  · change 1 ≤ sqDist (minEndpoint .Sext s) (cornerMid 2 0)
    have e : sqDist (minEndpoint .Sext s) (cornerMid 2 0) = 1 / 4 + (3 / 2 - s) / 2 + (3 / 2 - s) ^
        2 := by
      simp [minEndpoint, linePoint, sideDirection, neighbor, vertex, cornerMid, corner,
        cornerDirection, sqDist, ContactCase.right]; ring
    rw [e]; nlinarith
  · change 1 ≤ sqDist (minEndpoint .Sext s) (cornerMid 2 1)
    have e : sqDist (minEndpoint .Sext s) (cornerMid 2 1) = (3 / 2 - s) ^ 2 := by
      simp [minEndpoint, linePoint, sideDirection, neighbor, vertex, cornerMid, corner,
        cornerDirection, sqDist, ContactCase.right]; ring
    rw [e]; nlinarith

/-- A corner midpoint not in either adjacent side owner belongs to the corner owner. -/
theorem Canonical.corner_mids (H : Canonical c T r s) (j : Fin 3) (m : Fin 2)
    (h0 : cornerMid j m ∉ (T (sideIndex ⟨2 * j.val, by omega⟩)).carrier)
    (h1 : cornerMid j m ∉ (T (sideIndex ⟨2 * j.val + 1, by omega⟩)).carrier) :
    cornerMid j m ∈ (T (cornerIndex j)).carrier := by
  have hmem : cornerMid j m ∈ target :=
    cornerSeg_mem_target j m (t := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨k, hk⟩ := H.covers _ hmem
  have hallow := cornerSeg_owner_allowed H.common H.r_lt H.anchored j m (t := 1 / 2) (by norm_num)
    (by norm_num) hk
  rcases cornerAllowed_cases j k hallow with rfl | rfl | rfl
  · exact hk
  · exact absurd hk h0
  · exact absurd hk h1

/-- Every corner owner except `A₀` of `Sint` contains both its external midpoints. -/
theorem Canonical.s_corner_mids (H : Canonical c T r s) (hS : c.isS) (hs : s ≤ 1 / 14) (j : Fin 3)
    (hj : c = .Sint → j ≠ 0) (m : Fin 2) : cornerMid j m ∈ (T (cornerIndex j)).carrier := by
  refine H.corner_mids j m ?_ ?_
  · refine H.s_noMid hS hs _ ?_ j m
    cases c
    · rw [recvOf_Sext]; fin_cases j <;> decide
    · rw [recvOf_Sint]; fin_cases j <;> decide
    · exact hS.elim
    · exact hS.elim
  · cases c
    · fin_cases j
      · exact H.s_noMid hS hs _ (by rw [recvOf_Sext]; decide) 0 m
      · exact H.s_noMid hS hs _ (by rw [recvOf_Sext]; decide) 1 m
      · exact H.sext_recv_noMid m
    · fin_cases j
      · exact absurd rfl (hj rfl)
      · exact H.s_noMid hS hs _ (by rw [recvOf_Sint]; decide) 1 m
      · exact H.s_noMid hS hs _ (by rw [recvOf_Sint]; decide) 2 m
    · exact hS.elim
    · exact hS.elim

/-- The segment from the corner to a hexagon point crosses the base of the cell. -/
theorem hexagon_cross_base (j : Fin 3) {p : Point} (hp : p ∈ hexagon) :
    ∃ u lam : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ lam ∧ lam ≤ 1 ∧
      corner j + lam • (p - corner j) =
        linePoint (vertex ⟨2 * j.val, by omega⟩) (sideDirection ⟨2 * j.val, by omega⟩ true) u := by
  obtain ⟨h1, h2, h3⟩ := hp
  rw [abs_le] at h1 h2 h3
  rcases p with ⟨a, b⟩
  simp only at h1 h2 h3
  fin_cases j
  · have hd : 0 < 2 - a - b := by
      linarith
    refine ⟨(1 - a) / (2 - a - b), 1 / (2 - a - b), div_nonneg (by linarith) hd.le, ?_,
      div_nonneg zero_le_one hd.le, ?_, ?_⟩
    · rw [div_le_one hd]; linarith
    · rw [div_le_one hd]; linarith
    · apply Prod.ext <;> simp [corner, vertex, sideDirection, neighbor, linePoint] <;>
        field_simp <;> ring
  · have hd : 0 < a + 2 := by
      linarith
    refine ⟨(1 - b) / (a + 2), 1 / (a + 2), div_nonneg (by linarith) hd.le, ?_,
      div_nonneg zero_le_one hd.le, ?_, ?_⟩
    · rw [div_le_one hd]; linarith
    · rw [div_le_one hd]; linarith
    · apply Prod.ext <;> simp [corner, vertex, sideDirection, neighbor, linePoint] <;>
        field_simp <;> ring
  · have hd : 0 < b + 2 := by
      linarith
    refine ⟨(a + b + 1) / (b + 2), 1 / (b + 2), div_nonneg (by linarith) hd.le, ?_,
      div_nonneg zero_le_one hd.le, ?_, ?_⟩
    · rw [div_le_one hd]; linarith
    · rw [div_le_one hd]; linarith
    · apply Prod.ext <;> simp [corner, vertex, sideDirection, neighbor, linePoint] <;>
        field_simp <;> ring

/-- Every smaller central core vertex lies in a convex set containing the original core and zero. -/
theorem coreVertex_mem_of_le {C : Set Point} (hC : Convex ℝ C) (h0 : (0 : Point) ∈ C)
    (hK : ∀ j, coreVertex s j ∈ C) (hs0 : 0 < s) (hs : s ≤ 1 / 2) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ s) (j : Fin 6) : coreVertex u j ∈ C := by
  have hpos : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
  have hlam : (u * (1 - u)) / (s * (1 - s)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (mul_nonneg hu0 (by linarith)) hpos.le
    · rw [div_le_one hpos]
      nlinarith [mul_nonneg (sub_nonneg.2 hu) (by linarith : (0 : ℝ) ≤ 1 - s - u)]
  have := hC.smul_mem_of_zero_mem h0 (hK j) hlam
  convert this using 1
  rw [coreVertex, coreVertex, smul_smul]
  congr 1
  have h1 : (1 - s) ≠ 0 := by
    linarith
  have h2 : s ≠ 0 := hs0.ne'
  field_simp

theorem sidePoint_flip (i : Fin 6) (dir : Bool) (t : ℝ) :
    linePoint (vertex i) (sideDirection i dir) t =
      linePoint (vertex (neighbor i dir)) (sideDirection (neighbor i dir) (!dir)) (1 - t) := by
  cases dir <;> fin_cases i <;> apply Prod.ext <;>
    simp [linePoint, sideDirection, neighbor, vertex] <;> ring

theorem sidePoint_mem_hexagon (i : Fin 6) (dir : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    linePoint (vertex i) (sideDirection i dir) t ∈ hexagon := by
  cases dir <;> fin_cases i <;>
    simp only [hexagon, abs_le, linePoint, vertex, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        sideDirection, neighbor, Bool.false_eq_true, ↓reduceIte, zero_add, Matrix.cons_val,
        Prod.mk_sub_mk, sub_self, sub_zero, Prod.smul_mk, smul_eq_mul, mul_zero, mul_neg, mul_one,
        Prod.mk_add_mk, add_zero, Set.mem_ofPred_eq, neg_le_self_iff, zero_le_one, Std.le_refl,
        and_self, neg_le_neg_iff, le_add_neg_iff_add_le, neg_add_le_iff_le_add,
        add_le_iff_nonpos_right, Left.neg_nonpos_iff, true_and, Fin.mk_one, Matrix.cons_val_one,
        Fin.reduceAdd, zero_sub, add_neg_cancel_comm_assoc, and_true, Fin.reduceFinMk,
        sub_neg_eq_add, le_add_iff_nonneg_right, neg_add_cancel_comm, neg_add_cancel_comm_assoc,
        add_neg_cancel_comm, neg_add_cancel_right, le_neg_add_iff_add_le, add_neg_le_iff_le_add,
        add_le_iff_nonpos_left, neg_add_cancel_left, add_neg_cancel_right, le_add_iff_nonneg_left,
        add_neg_cancel_left] <;>
    (repeat' constructor) <;> linarith

/-- The hexagon side containing the ray from `vertex i` in direction `dir`. -/
def sideOf (i : Fin 6) (dir : Bool) : Fin 6 := if dir then i else i + 5

theorem Canonical.sidePoint_allowed (H : Canonical c T r s) (i : Fin 6) (dir : Bool) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {k : Fin 10}
    (hk : linePoint (vertex i) (sideDirection i dir) t ∈ (T k).carrier) :
    sideAllowed (sideOf i dir) k = true := by
  cases dir
  · rw [sidePoint_flip] at hk
    simp only [neighbor, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hk
    simp only [sideOf, Bool.false_eq_true, ↓reduceIte]
    exact side_owner_allowed H.common H.r_lt H.anchored (i + 5) (by linarith) (by linarith) hk
  · simp only [sideOf, ↓reduceIte]
    exact side_owner_allowed H.common H.r_lt H.anchored i ht0 ht1 hk

theorem sideAllowed_cases (i : Fin 6) (dir : Bool) (k : Fin 10)
    (hk : sideAllowed (sideOf i dir) k = true) :
    k = 0 ∨ k = sideIndex i ∨ k = sideIndex (neighbor i dir) ∨
      ∃ j : Fin 3, k = cornerIndex j ∧ sideAllowed (sideOf i dir) (cornerIndex j) = true := by
  revert hk; revert k; revert i; revert dir; decide

/-! ### The backward transfer -/

end ConwaySoifer
