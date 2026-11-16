/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakChunk
public import LeanPool.OrderMaintenance.Impl.Background


/-!
# Theorem W, option (A), stage A2: queue adjustment, filtering, chunk sizes, element insertion

* `pqAdjust_pk`: the bucket `p` chosen by a 0/1 flag (`ifz alone a + ifz (!alone) b`).
* `filter_pk`: the write index `w` stays below the loop index.
* `csP_pk`: a chunk's size plus one, below `2^K` (a hypothesis: it is below the queue's bucket
  capacity, `InsCaps.cB`).
* `insertElem_pk`: the label after its guard, and the group size and count plus one
  (hypotheses on the state before the insertion); the handle at width `KH`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

theorem Exp.ev_mul_inv {a b : Exp} {s : Core} {L : Loc} {w : Nat} (h : (Exp.bin .mul a b).ev κ s
  L = some w) :
    ∃ x y, a.ev κ s L = some x ∧ b.ev κ s L = some y ∧ w = x * y := by
  simp only [Exp.ev, Option.bind_eq_some_iff, Machine.BinOp.eval,
    Option.some.injEq] at h
  obtain ⟨x, hx, y, hy, rfl⟩ := h; exact ⟨x, y, hx, hy, rfl⟩

section core2
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **`pqAdjust`**. -/
theorem pqAdjust_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W pqAdjustP.body s L := by
  simp only [pqAdjustP]
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG (fun s1 L1 _ _ hG1 => ?_)
  refine PK.ite_ok ‹_› hC (by proveSafe) (fun _ _ _ => PK.of_safe hC (by omega) (by omega)
    (by
      simp only [pqInsertScanP, pqAddP, pqLinkAfterP]
      proveSafe) ‹_›) (fun _ => ?_)
  refine PK.ite_ok ‹_› hC (by proveSafe) (fun _ _ _ => PK.of_safe hC (by omega) (by omega)
    (by
      simp only [pqDelP]
      proveSafe) ‹_›) (fun _ => ?_)
  refine PK.ite_ok ‹_› hC (by proveSafe) (fun _ _ _ => ?_) (fun _ => PK.skip ‹_›)
  refine PK.ite_ok ‹_› hC (by proveSafe) (fun _ _ _ => ?_) (fun _ => PK.of_safe hC (by omega) (by
    omega)
    (by
      simp only [pqDelP, pqAddP, pqLinkAfterP, pqInsertScanP]
      proveSafe) ‹_›)
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG1 (fun s2 L2 n2 h2 hG2 => ?_)
  obtain ⟨a, ha, e1, e2⟩ := evalF_assign_inv h2
  subst e1 e2
  have ha1 : a ≤ 1 := Exp.isCmp_le (by rfl) ha
  intro hnb
  cases hv : (Exp.ifz "alone" (.ar .nbPrev "old") + Exp.ifz (!ₑ "alone") "old").ev κ s1
      (Machine.State.upd L1 "alone" a) with
  | none => simp only [Exp.add_def] at hv; simp [evalF, hv, Res.bind] at hnb
  | some w =>
    have hw : w < 2 ^ K := by
      simp only [Exp.ifz, Exp.add_def, Exp.mul_def] at hv
      obtain ⟨x, y, hx, hy, rfl⟩ := Exp.ev_add_inv hv
      obtain ⟨x1, xb, hx1, hxb, rfl⟩ := Exp.ev_mul_inv hx
      obtain ⟨y1, yb, hy1, hyb, rfl⟩ := Exp.ev_mul_inv hy
      simp only [Exp.ev, Option.some.injEq, upd_eq, Option.map_eq_some_iff,
        Machine.UnOp.eval] at hx1 hy1
      obtain ⟨u, hu, rfl⟩ := hy1
      subst hx1 hu
      have h1 := hG2.valN hC (e := .ar .nbPrev "old") rfl (w := K) (by proveSafe) hxb
      have h2 := hG2.valN hC (e := .var "old") rfl (w := K) (by proveSafe) hyb
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha1 with rfl | rfl <;> simp <;> omega
    refine PK.assign_seq hG2 hv (hG2.pk hC (by proveSafe) hv) (by simpa using hw)
      (fun hG3 => ?_) hnb
    exact PK.of_safe hC (by omega) (by omega) (by
      simp only [pqDelP, pqAddP, pqLinkAfterP]
      proveSafe) hG3

end core2

section core3
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **`filter`**: the write index stays at most the loop index. -/
theorem filter_pk (k : LK) (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W (filterP k).body s L
  := by
  simp only [filterP]
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨N, hN, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  have hNK : N < 2 ^ K := hG.valN hC rfl (by proveSafe) hN
  refine PK.safe_assign_seq hC hG1 (by proveSafe) (by proveSafe) (v := 0) rfl (fun hG2 => ?_)
  set L2 := Machine.State.upd (Machine.State.upd L "n" N) "w" 0
  have hn2 : (Exp.var "n").ev κ s L2 = some N := by simp [Exp.ev, L2, Machine.State.upd]
  have hLoop : PK K KH κ (ΓK K) W (.loop "j" "n" (filterBody k)) s L2 := by
    refine PK.loop hn2 (hG2.pk hC (by proveSafe) hn2)
      (fun j S L' => Gd K KH κ (ΓK K) S L' ∧ L' "w" ≤ j ∧ L' "n" = N)
      ⟨hG2, by simp [L2, Machine.State.upd], by simp [L2, Machine.State.upd]⟩ (fun _ _ _ h =>
        h.1) ?_
    intro j S L' hj ⟨hGS, hw, hn⟩
    have hG3 : Gd K KH κ (ΓK K) S (Machine.State.upd L' "j" j) :=
      ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (lt_trans hj hNK)⟩
    have hw3 : Machine.State.upd L' "j" j "w" ≤ j := by rw [upd_ne _ _ (by decide)]; exact hw
    have hn3 : Machine.State.upd L' "j" j "n" = N := by rw [upd_ne _ _ (by decide)]; exact hn
    have hmv : ∀ s4 L4, Gd K KH κ (ΓK K) s4 L4 → L4 "w" ≤ j →
        PK K KH κ (ΓK K) W ("w" ::= "w" + 1) s4 L4 := fun s4 L4 hG4 hw4 =>
      PK.assign hG4 (v := L4 "w" + 1) (by simp [Exp.ev, Machine.BinOp.eval])
        (hG4.pk hC (by proveSafe) (show ((Exp.var "w") + 1).ev κ s4 L4 = some (L4 "w" + 1) by
          simp [Exp.ev, Machine.BinOp.eval])) (by
            simp only [ΓK]
            omega)
    refine ⟨PK.ite_ok hG3 hC (by proveSafe) (fun _ _ _ => PK.skip hG3) (fun _ => PK.safe_seq' hC
      (by omega)
      (by omega) (by
        simp only [mvS]
        proveSafe) hG3 (fun s4 L4 n4 h4 hG4 => hmv s4 L4 hG4
        (by rw [evalF_frame_loc (by simp [Stm.asg, mvS]) h4]; exact hw3))), ?_⟩
    intro s' L'' c he
    obtain ⟨v, hv, m, hm⟩ := evalF_ite_inv he
    have hG' : Gd K KH κ (ΓK K) s' L'' :=
      (PK.ite_ok hG3 hC (by proveSafe) (fun _ _ _ => PK.skip hG3)
      (fun _ => PK.safe_seq' hC (by omega) (by omega) (by
        simp only [mvS]
        proveSafe) hG3
        (fun s4 L4 n4 h4 hG4 => hmv s4 L4 hG4 (by
          rw [evalF_frame_loc (by simp [Stm.asg, mvS]) h4]
          exact hw3)))).post he
    refine ⟨hG', ?_, by rw [evalF_frame_loc (by simp [Stm.asg, mvS, filterBody]) he, hn3]⟩
    split at hm
    · simp only [evalF, Res.ok.injEq] at hm; obtain ⟨-, rfl, -⟩ := hm; omega
    · obtain ⟨s4, L4, n4, n5, h4, h5⟩ := evalF_seq_inv hm
      obtain ⟨u, hu, -, rfl⟩ := evalF_assign_inv h5
      have hu' : L4 "w" + 1 = u := by
        simpa only [Exp.add_def, Exp.ofNat_def, Exp.ev, Machine.BinOp.eval, Option.bind_some,
          Option.some.injEq] using hu
      rw [upd_eq, ← hu', evalF_frame_loc (by simp [Stm.asg, mvS]) h4]
      omega
  exact PK.seq_g hLoop (fun _ _ _ _ hG5 => PK.of_safe hC (by omega) (by omega) (by proveSafe) hG5)

end core3

/-- Run a safe first statement of a sequence, passing on the end-state bound. -/
macro "peelf" : tactic => `(tactic| refine PKok.safe_seq_fin (by assumption) (by omega) (by
  omega) (by proveSafe)
  (by assumption) (by assumption) (fun _ _ _ _ _ _ => ?_))

theorem guard_ok {c : Exp} {s s' : Core} {L L' : Loc} {n : Nat} (h : evalF κ (.ite c .fail
  .skip) s L = .ok s' L' n) :
    c.ev κ s L = some 0 ∧ s = s' ∧ L = L' := by
  obtain ⟨v, hv, m, hm⟩ := evalF_ite_inv h
  split at hm
  · simp [evalF] at hm
  · next h0 =>
    simp only [ne_eq, Decidable.not_not] at h0
    subst h0
    simp only [evalF, Res.ok.injEq] at hm
    exact ⟨hv, hm.1, hm.2.1⟩

section core4
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **A chunk's size plus one** (below `2^K` by hypothesis), then the queue adjustment. -/
theorem csP_pk (hG : Gd K KH κ (ΓK K) s L) (hsz : (s.C.getX (L "c")).size + 1 < 2 ^ K) :
    PK K KH κ (ΓK K) W csP.body s L := by
  simp only [csP]
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨o, ho, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  obtain ⟨j, hj, -, rfl⟩ := Exp.ev_rd_inv ho
  simp only [Exp.ev, Option.some.injEq] at hj; subst hj
  have hv : (("old" : Exp) + 1).ev κ s (Machine.State.upd L "old" (Fld.get s (L "c") (.c .size))) =
      some (Fld.get s (L "c") (.c .size) + 1) := by simp [Exp.ev, Machine.BinOp.eval]
  refine PK.assign_seq hG1 hv (hG1.pk hC (by proveSafe) hv) (by simpa [Fld.get, CF.get] using hsz)
    (fun hG2 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG2 (fun s3 L3 n3 h3 hG3 => ?_)
  refine PK.ite_ok hG3 hC (by proveSafe) (fun _ _ _ => ?_) (fun _ => PK.skip hG3)
  exact PK.callS (Γe := ΓK K) hC hG3 (by proveSafe) (fun _ => le_refl K)
    (fun vs _ hG0 => pqAdjust_pk hC hK hW hG0) (by simp [pqAdjustP]) (by simp)

/-- **The label of a new element**, after its guard. -/
theorem insertElemPre_pk (hG : Gd K KH κ (ΓH K KH) s L) : PK K KH κ (ΓH K KH) W insertElemPre s
  L := by
  unfold insertElemPre
  peelSafe; peelSafe; peelSafe; peelSafe
  rename_i s4 L4 _ _ hG4
  refine PK.ite_ok hG4 hC (by proveSafe) (fun _ _ _ => ?_) (fun _ => PK.of_safe hC (by omega) (by
    omega)
    (by proveSafe) hG4)
  have hv : (Exp.var "exlab" + .prm .De).ev κ s4 L4 = some (L4 "exlab" + s4.P.elementSpacing) := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get]
  have ha : L4 "exlab" < 2 ^ K := by have := hG4.loc "exlab"; simpa [ΓH] using this
  have hD : s4.P.elementSpacing < 2 ^ K := by simpa [PF.get] using hG4.vb.prm .De
  have hvK : L4 "exlab" + s4.P.elementSpacing < 2 ^ (K + 1) := by rw [pow_succ]; omega
  refine PK.assign_seq hG4 hv (hG4.pk hC (by proveSafe) hv) (by simpa [ΓH] using hvK)
    (fun hG5 => ?_)
  set L5 := Machine.State.upd L4 "v" (L4 "exlab" + s4.P.elementSpacing)
  have hBe := hG4.vb.room.Be
  have hs : ((Exp.bin .shl 1 (.prm .Be) ≤ₑ "v") ||ₑ ("v" ≤ₑ "exlab") : Exp).ShOK κ s4 L5 K :=
    ⟨⟨⟨trivial, trivial, fun _ => by simpa [Exp.val, Exp.ev, PF.get] using hBe⟩, trivial, fun h
      => by cases h⟩,
      ⟨trivial, trivial, fun h => by cases h⟩, fun h => by cases h⟩
  have hGd : PK K KH κ (ΓH K KH) W (.ite ((Exp.bin .shl 1 (.prm .Be) ≤ₑ "v") ||ₑ ("v" ≤ₑ
    "exlab")) .fail .skip)
      s4 L5 := by
    intro hnb
    cases hc : ((Exp.bin .shl 1 (.prm .Be) ≤ₑ "v") ||ₑ ("v" ≤ₑ "exlab") : Exp).ev κ s4 L5 with
    | none => simp only [Exp.ofNat_def] at hc; simp [evalF, hc] at hnb
    | some c => exact PK.ite hc (hG5.pkS hC hs hc (by proveSafe)) (fun _ => PK.fail) (fun _ =>
      PK.skip hG5) hnb
  refine PK.seq_g hGd (fun s6 L6 n6 h6 hG6 => ?_)
  obtain ⟨hc0, e1, e2⟩ := guard_ok h6
  subst e1 e2
  have hlt : L4 "exlab" + s4.P.elementSpacing < 2 ^ K := by
    simp only [Exp.ofNat_def] at hc0
    simp [Exp.ev, Machine.BinOp.eval, PF.get, L5,
      Machine.State.upd] at hc0
    have := pow_le_pow' hBe; omega
  exact PK.assign hG6 (v := L4 "exlab" + s4.P.elementSpacing) (by simp [Exp.ev, L5])
    (by simp only [Exp.pk, L5, upd_eq]; exact lt_of_lt_of_le hlt (pow_le_pow' (by omega)))
    (by simpa [ΓH] using hlt)

/-- **Linking a new element**: the group size and the count plus one are the end state's. -/
theorem linkElem_pkok (hKH : KH ≤ W) (hG : Gd K KH κ (ΓH K KH) s L)
    (hF : Fin (κ := κ) (fun t => FB K KH κ (.g .size) t ∧ FB K KH κ (.s .count) t) linkElemS s L) :
    PKok K KH κ (ΓH K KH) W linkElemS s L := by
  unfold linkElemS
  peelf; peelf; peelf; peelf; peelf; peelf; peelf; peelf; peelf; peelf
  refine PKok.wr_fin_seq (Q := fun t => FB K KH κ (.g .size) t ∧ FB K KH κ (.s .count) t) hC ‹_›
    (by proveSafe) (by proveSafe) (by decide) (fun _ h => h.1) ‹_› (fun s1 hG1 hF1 => ?_)
  exact PK.ok (PK.wr_fin hC hG1 (by proveSafe) (by proveSafe) (fun _ h => h.2) hF1)

theorem insertElem_pkok (hKH : KH ≤ W) (hG : Gd K KH κ (ΓH K KH) s L)
    (hF : Fin (κ := κ) (fun t => FB K KH κ (.g .size) t ∧ FB K KH κ (.s .count) t)
      insertElemP.body s L) :
    PKok K KH κ (ΓH K KH) W insertElemP.body s L :=
  PKok.seq (PK.ok (insertElemPre_pk hC hK hW hG))
    (fun _ _ _ h1 hG1 => linkElem_pkok hC hK hW hKH hG1 (Fin.seq_right hF h1))

end core4

end OrderMaintenance.Impl
