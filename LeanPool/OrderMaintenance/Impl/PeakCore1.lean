/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakHP
public import LeanPool.OrderMaintenance.Impl.GroupStep
public import LeanPool.OrderMaintenance.Impl.ListErase


/-!
# Theorem W, option (A), stage A2: the peak of the queue, list, element and group procedures

For each procedure, `PK`: from a state with the invariant `Gd` (and, for the few that store a
computed value, a bound on it), the run computes nothing at or above `2^W`, `W ≥ 2K + 4`, and
keeps the invariant. Most procedures are safe (`Stm.Safe`, closed by `safe_tac`); the others store
a label after its guard (`afterS`), a centre label `2^(B−1)`, a size plus one, or a loop counter.

The locals are at width `K` (`ΓK`), except the candidate label `v` of `afterS`, at width `K + 1`
(`ΓV`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

/-- Every local at width `K`. -/
abbrev ΓK (K : Nat) : Reg → Nat := fun _ => K
/-- Every local at width `K`, except the candidate label `v` of `afterS`, at `K + 1`. -/
abbrev ΓV (K : Nat) : Reg → Nat := fun x => if x = "v" then K + 1 else K

theorem ΓK_le_ΓV (K : Nat) : ∀ x, ΓK K x ≤ ΓV K x := by intro x; simp only [ΓV, ΓK]; split <;> omega

/-- The locals of a chunk split step: `v` (of `afterS`) at width `K + 1`, the moved size `mv` at
`K + 2`, every other at `K`. -/
abbrev ΓM (K : Nat) : Reg → Nat := fun x => if x = "mv" then K + 2 else if x = "v" then K + 1 else K
/-- The locals of an element insertion: the handle `h` at width `KH`, the candidate label `v` at
`K + 1`, every other at `K`. -/
abbrev ΓH (K KH : Nat) : Reg → Nat := fun x => if x = "h" then KH else if x = "v" then K + 1 else K
/-- The locals of a drain start: the weight sums `t`, `b`, `ws` (of at most 511 weights) at width
`K + 9`, every other at `K`. -/
abbrev ΓD (K : Nat) : Reg → Nat := fun x => if x = "t" ∨ x = "b" ∨ x = "ws" then K + 9 else K
/-- The locals of `roomNextTo`: the lower bound `lo` (a label plus one) at width `K + 1`. -/
abbrev ΓR (K : Nat) : Reg → Nat := fun x => if x = "lo" then K + 1 else K

/-- Close `Stm.Safe` of a concrete statement (after its definitions are unfolded). -/
macro "safe_tac" : tactic => `(tactic| (simp [Stm.Safe, Exp.OK, Exp.wq, Exp.vw, Exp.noShl, Fld.wd,
    OrderMaintenance.Machine.BinOp.vw, OrderMaintenance.Machine.BinOp.wd, OrderMaintenance.Machine.UnOp.wd, Exp.maxShape, Exp.isCmp, Exp.isBool, Exp.monus, Exp.max,
    Exp.ifz, Exp.ar, Stm.war, Exp.sc, Stm.wsc, Exp.eF, Exp.gF, Exp.cF, Stm.weF, Stm.wgF, Stm.wcF, Proc.call,
    ΓK, ΓV, ΓM, ΓH, ΓR, ΓD] <;>
    omega))

variable {K KH W : Nat} {κ : Caps}

/-! ### Safe procedures -/

section safe
variable (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hK hW

theorem pqLinkAfter_safe : pqLinkAfterP.body.Safe K KH (ΓK K) W := by simp only [pqLinkAfterP]; safe_tac
theorem pqAdd_safe : pqAddP.body.Safe K KH (ΓK K) W := by simp only [pqAddP, pqLinkAfterP]; safe_tac
theorem pqDel_safe : pqDelP.body.Safe K KH (ΓK K) W := by simp only [pqDelP]; safe_tac
theorem pqInsertScan_safe : pqInsertScanP.body.Safe K KH (ΓK K) W := by
  simp only [pqInsertScanP, pqAddP, pqLinkAfterP]; safe_tac
theorem pqEnterIfAbove_safe : pqEnterIfAboveP.body.Safe K KH (ΓK K) W := by
  simp only [pqEnterIfAboveP, pqInsertScanP, pqAddP, pqLinkAfterP]; safe_tac
theorem pqPopMax_safe : pqPopMaxP.body.Safe K KH (ΓK K) W := by simp only [pqPopMaxP, pqDelP]; safe_tac
theorem pqEmpty_safe : pqEmptyP.body.Safe K KH (ΓK K) W := by simp only [pqEmptyP]; safe_tac
theorem find_safe (k : LK) : (findP k).body.Safe K KH (ΓK K) W := by simp only [findP]; safe_tac
theorem assocSet_safe (k : LK) : (assocSetP k).body.Safe K KH (ΓK K) W := by simp only [assocSetP]; safe_tac
theorem lookup_safe (k : LK) : (lookupP k).body.Safe K KH (ΓK K) W := by simp only [lookupP, findP]; safe_tac
theorem insertIdx_safe (k : LK) : (insertIdxP k).body.Safe K KH (ΓK K) W := by
  simp only [insertIdxP, swapS]; safe_tac
theorem copyS_safe (k : LK) : (copyS k).Safe K KH (ΓK K) W := by simp only [copyS, copyBody]; safe_tac
theorem eraseIdx_safe (k : LK) : (eraseIdxP k).body.Safe K KH (ΓK K) W := by simp only [eraseIdxP, mvS]; safe_tac
theorem order_safe : orderP.body.Safe K KH (ΓK K) W := by simp only [orderP, keyS]; safe_tac
theorem markDead_safe : markDeadP.body.Safe K KH (ΓK K) W := by simp only [markDeadP]; safe_tac
theorem labBefore_safe : labBeforeP.body.Safe K KH (ΓK K) W := by
  simp only [labBeforeP, labBeforeS, beforeS, betweenS]; safe_tac
theorem newGroup_safe : newGroupP.body.Safe K KH (ΓK K) W := by
  simp only [newGroupP, newGroupS, resetGS, rgA, rgB, rgC]; safe_tac
theorem linkGroupPair_safe : linkGroupPairS.Safe K KH (ΓK K) W := by
  simp only [linkGroupPairS, lgpA0, lgpA2, lgpG]; safe_tac
theorem unlinkGroup_safe : unlinkGroupS.Safe K KH (ΓK K) W := by simp only [unlinkGroupS, ulG, ulCE]; safe_tac
theorem move_safe (b : Bool) : (moveP b).body.Safe K KH (ΓK K) W := by
  cases b <;> simp only [moveP, moveS, mvGS, mvDS, mvES] <;> safe_tac

end safe

/-! ### Rules for the procedures below -/

section rules
variable {Γ : Reg → Nat} {s : Core} {L : Loc}

theorem PK.ite_ok {c : Exp} {t f : Stm} (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) (hc : c.OK Γ K KH W)
    (ht : ∀ v, c.ev κ s L = some v → v ≠ 0 → PK K KH κ Γ W t s L)
    (hf : c.ev κ s L = some 0 → PK K KH κ Γ W f s L) : PK K KH κ Γ W (.ite c t f) s L := by
  intro hnb
  cases hv : c.ev κ s L with
  | none => simp [evalF, hv] at hnb
  | some v => exact PK.ite hv (hG.pk hC hc hv) (ht v hv) (fun h0 => hf (h0 ▸ hv)) hnb

theorem PK.safe_seq {c d : Stm} {Γ' : Reg → Nat} (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W)
    (hS : c.Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ s1 L1 → PK K KH κ Γ' W d s1 L1) :
    PK K KH κ Γ' W (c;; d) s L :=
  PK.seq (PK.of_safe hC hK hW hS hG) (fun s1 L1 n1 h => hd s1 L1 n1 h ((PK.of_safe hC hK hW hS hG).post h))

theorem evalF_assign_inv {x : Reg} {e : Exp} {s1 : Core} {L1 : Loc} {n : Nat}
    (h : evalF κ (x ::= e) s L = .ok s1 L1 n) : ∃ v, e.ev κ s L = some v ∧ s = s1 ∧ L1 = OrderMaintenance.Machine.State.upd L x v := by
  simp only [evalF] at h
  split at h
  · next v hv => simp at h; obtain ⟨rfl, rfl, -⟩ := h; exact ⟨v, hv, rfl, rfl⟩
  · cases h

theorem upd_eq (L : Loc) (x : Reg) (v : Nat) : OrderMaintenance.Machine.State.upd L x v x = v := by
  simp [OrderMaintenance.Machine.State.upd]
theorem upd_ne (L : Loc) {x y : Reg} (v : Nat) (h : y ≠ x) : OrderMaintenance.Machine.State.upd L x v y = L y := by
  simp [OrderMaintenance.Machine.State.upd, h]

theorem pow_le_pow' {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

end rules

/-- Close a width goal `Exp.wq … ≤ W` or `Exp.vw … ≤ w` of a concrete expression. -/
macro "wq_tac" : tactic => `(tactic| (simp [Exp.wq, Exp.vw, Fld.wd, OrderMaintenance.Machine.BinOp.vw, OrderMaintenance.Machine.BinOp.wd,
    OrderMaintenance.Machine.UnOp.wd, Exp.maxShape, Exp.isCmp, Exp.isBool, Exp.monus, Exp.max, Exp.ifz, Exp.ar, Exp.sc, Exp.eF, Exp.gF, Exp.cF,
    ΓK, ΓV, ΓM, ΓH, ΓR, ΓD] <;> omega))

/-! ### Labels: `afterS`, and the centre label -/

section labels
variable {s : Core} {L : Loc}

/-- `afterS`: the candidate `v = a + D` (at width `K + 1`), its guard, and `lab := v` below `2^B`. -/
theorem afterS_pk (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W) (hG : Gd K KH κ (ΓV K) s L)
    (hB : L "B" ≤ K) (ha : L "a" < 2 ^ K) (hD : L "D" < 2 ^ K) : PK K KH κ (ΓV K) W afterS s L := by
  unfold afterS
  have hv : (("a" : Exp) + "D").ev κ s L = some (L "a" + L "D") := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval]
  have hvK : L "a" + L "D" < 2 ^ (K + 1) := by rw [pow_succ]; omega
  have hp : (("a" : Exp) + "D").pk κ s L < 2 ^ W :=
    hG.pkS hC (Exp.shOK_of_noShl _ _ _ _ _ rfl) hv (by wq_tac)
  refine PK.seq (PK.assign (x := "v") hG hv hp (by simpa [ΓV] using hvK)) (fun s1 L1 n1 h1 => ?_)
  obtain ⟨v, hv1, e1, e2⟩ := evalF_assign_inv h1
  subst e1; subst e2
  rw [hv] at hv1; cases hv1
  have hG1 := (PK.assign (x := "v") hG hv hp (by simpa [ΓV] using hvK)).post h1
  set L1 := OrderMaintenance.Machine.State.upd L "v" (L "a" + L "D")
  have hL1v : L1 "v" = L "a" + L "D" := upd_eq _ _ _
  have hL1a : L1 "a" = L "a" := upd_ne _ _ (by decide)
  have hL1B : L1 "B" = L "B" := upd_ne _ _ (by decide)
  have hc : ((Exp.bin .shl 1 "B" ≤ₑ "v") ||ₑ ("v" ≤ₑ "a") : Exp).ev κ s L1 =
      some (if (1 * 2 ^ L "B" ≤ L "a" + L "D") ∨ (L "a" + L "D" ≤ L "a") then 1 else 0) := by
    simp only [Exp.ev, hL1v, hL1a, hL1B, Option.bind_some, OrderMaintenance.Machine.BinOp.eval]
    by_cases q1 : 1 * 2 ^ L "B" ≤ L "a" + L "D" <;> by_cases q2 : L "a" + L "D" ≤ L "a" <;> simp [q1, q2]
  have hs : ((Exp.bin .shl 1 "B" ≤ₑ "v") ||ₑ ("v" ≤ₑ "a") : Exp).ShOK κ s L1 K := by
    simp only [Exp.ShOK, Exp.val, Exp.ev, hL1B,
      Option.getD_some]; exact ⟨⟨⟨trivial, trivial, fun _ => hB⟩,
      trivial, fun h => by cases h⟩, ⟨trivial, trivial, fun h => by cases h⟩, fun h => by cases h⟩
  refine PK.ite hc (hG1.pkS hC hs hc (by wq_tac)) (fun _ => PK.fail) (fun h0 => ?_)
  -- `lab := v`, below `2^B ≤ 2^K`
  have hlt : L "a" + L "D" < 2 ^ K := by
    by_cases hh : (1 * 2 ^ L "B" ≤ L "a" + L "D" ∨ L "a" + L "D" ≤ L "a")
    · rw [ite_eq_left hh] at h0; cases h0
    · push Not at hh; have := pow_le_pow' hB; omega
  have hv2 : ("v" : Exp).ev κ s L1 = some (L "a" + L "D") := by simp [Exp.ev, hL1v]
  refine PK.assign hG1 hv2 ?_ (by simpa [ΓV] using hlt)
  simp only [Exp.pk, hL1v]; exact lt_of_lt_of_le hlt (pow_le_pow' (by omega))

/-- The value of `1 <<< monus (prm k) 1` (the centre label of `elementBits` or `groupBits`). -/
theorem centre_ev (s : Core) (L : Loc) (k : PF) :
    (Exp.bin .shl 1 (Exp.monus (.prm k) 1)).ev κ s L = some (2 ^ (k.get s.P - 1)) := by
  have hm := Exp.ev_monus κ s L (a := .prm k) (b := (1 : Exp)) (x := k.get s.P) (y := 1) (by simp [Exp.ev]) rfl
  simp only [Exp.ev, Option.bind_some]; rw [hm]; simp [OrderMaintenance.Machine.BinOp.eval]

theorem centre_shOK (s : Core) (L : Loc) {k : PF} (hk : k.get s.P ≤ K) :
    (Exp.bin .shl 1 (Exp.monus (.prm k) 1)).ShOK κ s L K := by
  have hm := Exp.ev_monus κ s L (a := .prm k) (b := (1 : Exp)) (x := k.get s.P) (y := 1) (by simp [Exp.ev]) rfl
  refine ⟨trivial, Exp.shOK_of_noShl _ _ _ _ _ rfl, fun _ => ?_⟩
  rw [Exp.val_of hm]; omega

/-- The centre label `2^(B − 1)` with `B ≤ K`: an assignment below `2^K`. -/
theorem centre_pk {Γ : Reg → Nat} (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W) (hG : Gd K KH κ Γ s L)
    {k : PF} (hk : k.get s.P ≤ K) {x : Reg} (hx : K ≤ Γ x) :
    PK K KH κ Γ W (x ::= Exp.bin .shl 1 (Exp.monus (.prm k) 1)) s L := by
  have hv := centre_ev (κ := κ) s L k
  have hlt : 2 ^ (k.get s.P - 1) < 2 ^ K := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact PK.assign hG hv (hG.pkS hC (centre_shOK s L hk) hv (by wq_tac)) (lt_of_lt_of_le hlt (pow_le_pow' hx))

end labels

/-! ### More rules -/

section rules2
variable {Γ : Reg → Nat} {s : Core} {L : Loc}

/-- An assignment whose value is known, then the rest. -/
theorem PK.assign_seq {x : Reg} {e : Exp} {d : Stm} {v : Nat} (hG : Gd K KH κ Γ s L)
    (hv : e.ev κ s L = some v) (hp : e.pk κ s L < 2 ^ W) (hx : v < 2 ^ Γ x)
    (hd : Gd K KH κ Γ s (OrderMaintenance.Machine.State.upd L x v) → PK K KH κ Γ W d s (OrderMaintenance.Machine.State.upd L x v)) :
    PK K KH κ Γ W ((x ::= e);; d) s L :=
  PK.seq_ok (show evalF κ (x ::= e) s L = .ok s (OrderMaintenance.Machine.State.upd L x v) (1 + e.cost) by simp [evalF, hv])
    (PK.assign hG hv hp hx) (hd ⟨hG.enc, hG.vb, upd_lt hG.loc hx⟩)

/-- A safe assignment whose value is known, then the rest. -/
theorem PK.safe_assign_seq {x : Reg} {e : Exp} {d : Stm} {v : Nat} (hC : CapsW K κ) (hG : Gd K KH κ Γ s L)
    (he : e.OK Γ K KH W) (hw : e.vw Γ K KH K ≤ Γ x) (hv : e.ev κ s L = some v)
    (hd : Gd K KH κ Γ s (OrderMaintenance.Machine.State.upd L x v) → PK K KH κ Γ W d s (OrderMaintenance.Machine.State.upd L x v)) :
    PK K KH κ Γ W ((x ::= e);; d) s L :=
  PK.assign_seq hG hv (hG.pk hC he hv) (hG.valW hC he hw hv) hd

theorem evalF_wr_inv {f : Fld} {i e : Exp} {s1 : Core} {L1 : Loc} {n : Nat}
    (h : evalF κ (.wr f i e) s L = .ok s1 L1 n) :
    ∃ j v, i.ev κ s L = some j ∧ e.ev κ s L = some v ∧ f.set κ s j v = some s1 ∧ L1 = L := by
  simp only [evalF] at h
  split at h
  · next j v hj hv =>
    split at h
    · next s' hs => simp at h; obtain ⟨rfl, rfl, -⟩ := h; exact ⟨j, v, hj, hv, hs, rfl⟩
    · cases h
  · cases h

/-- **A call with argument expressions of width `K`**; the body's bound is given for the
callee's entry frame. -/
theorem PK.callS {q : Proc} {args : List Exp} {ds : List Reg} {Γc : Reg → Nat} {Γe : Reg → Nat}
    (hC : CapsW K κ)
    (hG : Gd K KH κ Γ s L) (ha : ∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) (hps : ∀ x, K ≤ Γe x)
    (hb : ∀ vs, evList κ s L args = some vs → Gd K KH κ Γe s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) q.params vs) →
      PK K KH κ Γc W q.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) q.params vs))
    (hr : ∀ r ∈ q.rets, Γc r ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) : PK K KH κ Γ W (q.call args ds) s L := by
  intro hnb
  cases hv : evList κ s L args with
  | none => simp [Proc.call, evalF, hv] at hnb
  | some vs =>
    have hG0 : Gd K KH κ Γe s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) q.params vs) :=
      ⟨hG.enc, hG.vb, setLocs_lt (zero_locs _) (fun x _ => hps x) (hG.vals hC ha hv)⟩
    exact PK.call hG hv (hG.pkList hC (fun e he => (ha e he).1) hv) (hb vs hv hG0) hr hd hnb

end rules2

theorem PK.safe_seq' {c d : Stm} {Γ : Reg → Nat} {s : Core} {L : Loc} (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W)
    (hS : c.Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ s1 L1 → PK K KH κ Γ W d s1 L1) :
    PK K KH κ Γ W (c;; d) s L := PK.safe_seq hC hK hW hS hG hd

theorem ΓV_ge (K : Nat) : ∀ x, K ≤ ΓV K x := by intro x; simp only [ΓV]; split <;> omega

/-- Run a safe first statement of a sequence. -/
macro "peel" : tactic => `(tactic| refine PK.safe_seq' (by assumption) (by omega) (by omega) (by safe_tac)
  (by assumption) (fun _ _ _ _ _ => ?_))

/-! ### Group labels and moves -/

section groups
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

theorem gd_a (hG : Gd K KH κ (ΓV K) s L) (x : Reg) (hx : x ≠ "v") : L x < 2 ^ K := by
  have := hG.loc x; simp only [ΓV, ite_eq_right hx] at this; exact this

/-- The tail of `labAfter` and of the left label of a move: `a`, `D`, `B := prm k`, `afterS`. -/
theorem afterTail_pk {a : Exp} {kD kB : PF} (hG : Gd K KH κ (ΓV K) s L) (hB : kB.get s.P ≤ K)
    (ha : a.OK (ΓV K) K KH W) (haw : a.vw (ΓV K) K KH K ≤ K) :
    PK K KH κ (ΓV K) W ("a" ::= a;; "D" ::= .prm kD;; "B" ::= .prm kB;; afterS) s L := by
  refine PK.safe_seq hC (by omega) (by omega) ⟨ha, by simpa [ΓV] using haw⟩ hG (fun s1 L1 n1 h1 hG1 => ?_)
  refine PK.safe_seq hC (by omega) (by omega) (by safe_tac) hG1 (fun s2 L2 n2 h2 hG2 => ?_)
  have hP : s2.P = s.P := (evalF_P h2).trans (evalF_P h1)
  refine PK.safe_assign_seq hC hG2 (by safe_tac) (by safe_tac) (v := kB.get s2.P) (by simp [Exp.ev]) (fun hG3 => ?_)
  exact afterS_pk hC hK hW hG3 (by rw [upd_eq, hP]; exact hB) (gd_a hC hK hW hG3 _ (by decide))
    (gd_a hC hK hW hG3 _ (by decide))

theorem labAfter_pk (hG : Gd K KH κ (ΓV K) s L) (hP : PRoom K s.P) : PK K KH κ (ΓV K) W labAfterS s L := by
  unfold labAfterS
  refine PK.safe_seq hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  have hP1 : s1.P = s.P := evalF_P h1
  refine PK.ite_ok hG1 hC (by safe_tac) (fun v _ _ => ?_) (fun _ => PK.of_safe hC (by omega) (by omega)
    (by simp only [betweenS]; safe_tac) hG1)
  refine PK.seq (Γ' := ΓV K) (PK.of_safe hC (by omega) (by omega) (by safe_tac) hG1) (fun s2 L2 n2 h2 => ?_)
  -- `labAfter`'s own tail is `"D" ::= …`, `"B" ::= …`, `afterS` after `"a"`
  have hG2 := (PK.of_safe (W := W) hC (by omega) (by omega) (by safe_tac : ("a" ::= Exp.gF .lab "g").Safe K KH (ΓV K) W)
    hG1).post h2
  have hP2 : s2.P = s.P := (evalF_P h2).trans hP1
  refine PK.safe_seq hC (by omega) (by omega) (by safe_tac) hG2 (fun s3 L3 n3 h3 hG3 => ?_)
  have hP3 : s3.P = s.P := (evalF_P h3).trans hP2
  refine PK.safe_assign_seq hC hG3 (by safe_tac) (by safe_tac) (v := PF.Bg.get s3.P) (by simp [Exp.ev])
    (fun hG4 => ?_)
  exact afterS_pk hC hK hW hG4 (by rw [upd_eq, hP3]; exact hP.Bg) (gd_a hC hK hW hG4 _ (by decide))
    (gd_a hC hK hW hG4 _ (by decide))

theorem moveLabL_pk (hG : Gd K KH κ (ΓV K) s L) (hP : PRoom K s.P) : PK K KH κ (ΓV K) W moveLabL s L := by
  unfold moveLabL
  refine PK.ite_ok hG hC (by safe_tac) (fun v _ _ => ?_) (fun _ => ?_)
  · exact centre_pk hC hK hW hG (k := .Be) hP.Be (by simp [ΓV])
  · exact afterTail_pk hC hK hW hG hP.Be (by safe_tac) (by safe_tac)

theorem moveLabR_pk (hG : Gd K KH κ (ΓV K) s L) (hP : PRoom K s.P) : PK K KH κ (ΓV K) W moveLabR s L := by
  unfold moveLabR
  refine PK.ite_ok hG hC (by safe_tac) (fun v _ _ => ?_) (fun _ => ?_)
  · exact centre_pk hC hK hW hG (k := .Be) hP.Be (by simp [ΓV])
  · exact PK.of_safe hC (by omega) (by omega) (by simp only [beforeS]; safe_tac) hG

theorem moveElem_pk (hG : Gd K KH κ (ΓV K) s L) (hP : PRoom K s.P) : PK K KH κ (ΓV K) W moveElemS s L := by
  unfold moveElemS
  refine PK.safe_seq hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  refine PK.safe_seq hC (by omega) (by omega) (by safe_tac) hG1 (fun s2 L2 n2 h2 hG2 => ?_)
  have hP2 : s2.P = s.P := (evalF_P h2).trans (evalF_P h1)
  refine PK.ite_ok hG2 hC (by safe_tac) (fun v _ _ => ?_) (fun _ => ?_)
  · refine PK.seq (moveLabL_pk hC hK hW hG2 (hP2 ▸ hP)) (fun s3 L3 n3 h3 => ?_)
    exact PK.of_safe hC (by omega) (by omega) (by simp only [moveP, moveS, mvGS, mvDS, mvES]; safe_tac)
      ((moveLabL_pk hC hK hW hG2 (hP2 ▸ hP)).post h3)
  · refine PK.seq (moveLabR_pk hC hK hW hG2 (hP2 ▸ hP)) (fun s3 L3 n3 h3 => ?_)
    exact PK.of_safe hC (by omega) (by omega) (by simp only [moveP, moveS, mvGS, mvDS, mvES]; safe_tac)
      ((moveLabR_pk hC hK hW hG2 (hP2 ▸ hP)).post h3)

end groups

/-! ### Reads -/

theorem Exp.ev_rd_inv {f : Fld} {i : Exp} {s : Core} {L : Loc} {w : Nat} (h : (Exp.rd f i).ev κ s L = some w) :
    ∃ j, i.ev κ s L = some j ∧ j < f.cap κ ∧ w = f.get s j := by
  simp only [Exp.ev, Option.bind_eq_some_iff] at h
  obtain ⟨j, hj, h⟩ := h
  split at h
  · next hc => cases h; exact ⟨j, hj, hc, rfl⟩
  · cases h

theorem Exp.ev_add1_inv {e : Exp} {s : Core} {L : Loc} {w : Nat} (h : (e + 1).ev κ s L = some w) :
    ∃ x, e.ev κ s L = some x ∧ w = x + 1 := by
  simp only [Exp.add_def, Exp.ev, Option.bind_eq_some_iff, OrderMaintenance.Machine.BinOp.eval,
    Exp.ofNat_def,
    Option.some.injEq] at h
  obtain ⟨x, hx, y, rfl, rfl⟩ := h; exact ⟨x, hx, rfl⟩

theorem Exp.ev_monus_le {a b : Exp} {s : Core} {L : Loc} {w : Nat} (h : (Exp.monus a b).ev κ s L = some w) :
    ∃ x, a.ev κ s L = some x ∧ w ≤ x := by
  cases ha : a.ev κ s L with
  | none => simp [Exp.monus, Exp.max, Exp.ev, ha] at h
  | some x =>
    cases hb : b.ev κ s L with
    | none => simp [Exp.monus, Exp.max, Exp.ev, ha, hb] at h
    | some y =>
      rw [Exp.ev_monus κ s L ha hb] at h; cases h; exact ⟨x, rfl, Nat.sub_le _ _⟩

/-! ### The tail of a group split step, the split start, the removal -/

section steps
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- The sizes after a move: `size d + 1` below `2^K`. -/
theorem gssTail_pk (hG : Gd K KH κ (ΓV K) s L)
    (hd : L "d" < κ.tbl .G → (s.Gs.getX (L "d")).size + 1 < 2 ^ K) :
    PK K KH κ (ΓV K) W gssTail s L := by
  unfold gssTail
  refine PK.safe_seq hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  simp only [Stm.wgF] at h1
  obtain ⟨j, v, hj, hv, hset, hL1⟩ := evalF_wr_inv h1
  subst hL1
  obtain ⟨x, hx, hvx⟩ := Exp.ev_monus_le hv
  obtain ⟨j', hj', -, hx'⟩ := Exp.ev_rd_inv hx
  rw [hj] at hj'; cases hj'
  simp only [Exp.ev, Option.some.injEq] at hj
  subst hj
  -- the second write
  have hw2 : PK K KH κ (ΓV K) W (.wgF .size "d" (.gF .size "d" + 1)) s1 L1 := by
    intro hnb
    cases hw : (Exp.gF .size "d" + 1).ev κ s1 L1 with
    | none =>
      exfalso; apply hnb
      simp only [Exp.add_def, Exp.ofNat_def] at hw
      simp [evalF, Stm.wgF, hw, show (Exp.var "d").ev κ s1 L1 = some (L1 "d") from rfl]
    | some w =>
      obtain ⟨y, hy, hwy⟩ := Exp.ev_add1_inv hw
      obtain ⟨jd, hjd, hjdc, hyd⟩ := Exp.ev_rd_inv hy
      simp only [Exp.ev, Option.some.injEq] at hjd
      have hd := hd (by rw [hjd]; exact hjdc)
      have hval : w < 2 ^ K := by
        rw [hwy, hyd, ← hjd, Fld.get_set hset _ (hjd ▸ hjdc)]
        split
        · next e =>
          obtain ⟨-, e2⟩ := e
          rw [e2] at hd
          simp only [Fld.get, GF.get] at hd hvx hx' ⊢
          omega
        · simpa [Fld.get, GF.get] using hd
      exact PK.wr (j := L1 "d") hG1 (by simp [Exp.ev]) hw
        (hG1.pk hC (by safe_tac) (show (Exp.var "d").ev κ s1 L1 = some (L1 "d") from rfl))
        (hG1.pk hC (by safe_tac) hw) (by simpa [Fld.wd] using hval) hnb
  exact PK.seq hw2 (fun s2 L2 n2 h2 => PK.of_safe hC (by omega) (by omega)
    (by simp only [gssChkE]; safe_tac) (hw2.post h2))

end steps

section steps2
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

theorem labAfterCall_pk {args : List Exp} {ds : List Reg} {Γ : Reg → Nat} (hG : Gd K KH κ Γ s L)
    (ha : ∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) :
    PK K KH κ Γ W (labAfterP.call args ds) s L :=
  PK.callS (Γc := ΓV K) (Γe := ΓV K) hC hG ha (ΓV_ge K) (fun vs _ hG0 => labAfter_pk hC hK hW hG0 hG0.vb.room)
    (by simp [labAfterP, ΓV]) hd

theorem startGroupSplit_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W startGroupSplitS s L := by
  unfold startGroupSplitS
  refine PK.safe_seq' hC (by omega) (by omega) (by simp only [labBeforeP, labBeforeS, beforeS, betweenS]; safe_tac)
    hG (fun _ _ _ _ _ => ?_)
  have hA := labAfterCall_pk (W := W) hC hK hW (args := [.var "g"]) (ds := ["labR"]) ‹Gd K KH κ (ΓK K) _ _›
    (by safe_tac) (by simp)
  refine PK.seq hA (fun s2 L2 n2 h2 => ?_)
  exact PK.of_safe hC (by omega) (by omega)
    (by simp only [newGroupP, newGroupS, resetGS, rgA, rgB, rgC, linkGroupPairS, lgpA0, lgpA2,
      lgpG]; safe_tac)
    (hA.post h2)

theorem splitIf_pk {x q : Reg} (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W (splitIfS x q) s L := by
  unfold splitIfS
  refine PK.ite_ok hG hC (by simp only [splitIfE]; safe_tac) (fun _ _ _ => ?_) (fun _ => PK.skip hG)
  exact PK.callS (Γe := ΓK K) hC hG (by safe_tac) (fun _ => le_refl K) (fun vs _ hG0 => startGroupSplit_pk hC hK hW hG0)
    (by simp [startGroupSplitP]) (by simp)

theorem removeGroup_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W removeGroupS s L := by
  unfold removeGroupS
  refine PK.safe_seq' hC (by omega) (by omega) (by simp only [unlinkGroupS, ulG, ulCE]; safe_tac) hG
    (fun _ _ _ _ _ => ?_)
  peel; peel
  refine PK.safe_seq' hC (by omega) (by omega) (by simp only [quietS, quietE]; safe_tac) ‹_› (fun _ _ _ _ _ => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by simp only [quietS, quietE]; safe_tac) ‹_› (fun _ _ _ _ hG5 => ?_)
  exact PK.seq (splitIf_pk hC hK hW hG5) (fun _ _ _ h => splitIf_pk hC hK hW ((splitIf_pk hC hK hW hG5).post h))

end steps2

/-! ### A group split step and the drive -/

section drive
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **A group split step**, given the size bound of the group that receives the element (after
the move, at the local `d` the move sets). -/
theorem groupSplitStep_pk (hG : Gd K KH κ (ΓK K) s L)
    (hsz : ∀ L0 S1 L1 n, L0 "g" = L "g" → evalF κ moveElemS s L0 = .ok S1 L1 n → L1 "d" < κ.tbl .G →
      (S1.Gs.getX (L1 "d")).size + 1 < 2 ^ K) :
    PK K KH κ (ΓV K) W groupSplitStepS s L := by
  unfold groupSplitStepS
  refine PK.safe_seq (Γ := ΓK K) hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨v, -, e1, e2⟩ := evalF_assign_inv h1
  subst e1
  have hL1 : L1 "g" = L "g" := by rw [e2]; exact upd_ne _ _ (by decide)
  refine PK.ite_ok (hG1.mono (ΓK_le_ΓV K)) hC (by safe_tac) (fun _ _ _ => ?_) (fun _ => ?_)
  · refine PK.mono (Γ := ΓK K) ?_ (le_refl W) (ΓK_le_ΓV K)
    exact PK.seq (removeGroup_pk hC hK hW hG1) (fun _ _ _ h => PK.of_safe hC (by omega) (by omega) (by safe_tac)
      ((removeGroup_pk hC hK hW hG1).post h))
  · have hM := moveElem_pk hC hK hW (hG1.mono (ΓK_le_ΓV K)) hG1.vb.room
    exact PK.seq hM (fun S1 L2 n2 h2 => gssTail_pk hC hK hW (hM.post h2) (hsz _ _ _ _ hL1 h2))

end drive

end OrderMaintenance.Impl
