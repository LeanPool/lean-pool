/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Elem
public import LeanPool.OrderMaintenance.Impl.CM
public import LeanPool.OrderMaintenance.Impl.StartDrain
public import LeanPool.OrderMaintenance.Proof.Correct.GroupSplit


/-!
# M6: groups (`Model/Core.lean`: group splits)

Each procedure is a sequence of field writes. A write is a `modify` of one record
(`evalF_wrG_ok` …), consecutive writes to one record merge (`Array.modify_modify_same`), and the
blocks follow Level F's `let`s, so a conditional write needs a two-way split only.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)
open OrderMaintenance.Proof.Top (getX_modify')

local notation "upd" => Machine.State.upd

/-! ### Writes -/

theorem evalF_wrG_ok {κ : Caps} {s : Core} {L : Loc} {k : GF} {i e : Exp} {j w : Nat} (hi : i.ev
  κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.Gs.size) (hk : k.ok w = true) :
    evalF κ (.wr (.g k) i e) s L = .ok {
      s with
      Gs := s.Gs.modify j (GF.set · w k)
    } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

theorem evalF_wrC_ok {κ : Caps} {s : Core} {L : Loc} {k : CF} {i e : Exp} {j w : Nat} (hi : i.ev
  κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.C.size) (hk : k.ok w = true) :
    evalF κ (.wr (.c k) i e) s L = .ok {
      s with
      C := s.C.modify j (CF.set · w k)
    } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

theorem evalF_wrS_ok {κ : Caps} {s : Core} {L : Loc} {k : SF} {e : Exp} {w : Nat}
    (he : e.ev κ s L = some w) (hk : k.ok w = true) :
    evalF κ (.wr (.s k) 0 e) s L = .ok (k.set s w) L (1 + 1 + e.cost) := by
  simp [evalF, he, Fld.set, hk, Exp.ev, Exp.cost]

/-! ### `linkGroupPair` -/

/-- Initialize and link the left overflow group before its source. -/
def lgpA0 : Stm := cm{
  G[gl].lab := labL; G[gl].st := 1; G[gl].src := g; G[gl].prev := gp; G[gl].next := g }
/-- Initialize and link the right overflow group after its source. -/
def lgpA2 : Stm := cm{
  G[gr].lab := labR; G[gr].st := 1; G[gr].src := g; G[gr].prev := g; G[gr].next := gn }
/-- Mark the source group as splitting and record its two overflow siblings. -/
def lgpG : Stm := cm{
  G[g].prev := gl; G[g].next := gr; G[g].st := 2; G[g].l := gl; G[g].r := gr }

/-- `linkGroupPair`: link `gl`, `gr` around `g` (locals `g gl gr labL labR`). -/
def linkGroupPairS : Stm := cm{
  gp := G[g].prev; gn := G[g].next; c := G[g].chk
  lgpA0
  if gp ≠ 0 then G[gp].next := gl
  lgpA2
  if gn ≠ 0 then G[gn].prev := gr
  if C[c].first = g then C[c].first := gl
  lgpG
  if C[c].last = g then C[c].last := gr
  if gp = 0 then S.firstGroup := gl }

/-- Five writes to one group. -/
theorem five_wrG {κ : Caps} {s : Core} {L : Loc} {x : Reg} {j : Nat} {k1 k2 k3 k4 k5 : GF} {e1
  e2 e3 e4 e5 : Exp}
    {w1 w2 w3 w4 w5 : Nat} (hx : L x = j) (hj : j < s.Gs.size)
    (h1 : ∀ s', e1.ev κ s' L = some w1) (h2 : ∀ s', e2.ev κ s' L = some w2) (h3 : ∀ s', e3.ev κ
      s' L = some w3)
    (h4 : ∀ s', e4.ev κ s' L = some w4) (h5 : ∀ s', e5.ev κ s' L = some w5)
    (o1 : k1.ok w1 = true) (o2 : k2.ok w2 = true) (o3 : k3.ok w3 = true) (o4 : k4.ok w4 = true)
      (o5 : k5.ok w5 = true) :
    evalF κ (.wr (.g k1) (.var x) e1;; .wr (.g k2) (.var x) e2;; .wr (.g k3) (.var x) e3;;
      .wr (.g k4) (.var x) e4;; .wr (.g k5) (.var x) e5) s L =
      .ok {
        s with
        Gs := s.Gs.modify j (fun X => GF.set (GF.set (GF.set (GF.set (GF.set X w1 k1) w2 k2) w3
          k3) w4 k4) w5 k5)
      } L
        (5 + 5 + e1.cost + e2.cost + e3.cost + e4.cost + e5.cost) := by
  have hv : ∀ s' : Core, (Exp.var x).ev κ s' L = some j := fun _ => by simp [Exp.ev, hx]
  rw [evalF_seq_ok2 (evalF_wrG_ok (hv _) (h1 _) hj  o1) (evalF_seq_ok2 (evalF_wrG_ok (hv _)
    (h2 _) (by simpa using hj)  o2)
    (evalF_seq_ok2 (evalF_wrG_ok (hv _) (h3 _) (by simpa using hj)  o3)
      (evalF_seq_ok2 (evalF_wrG_ok (hv _) (h4 _) (by simpa using hj)  o4)
        (evalF_wrG_ok (hv _) (h5 _) (by simpa using hj)  o5))))]
  simp only [Array.modify_modify_same, Function.comp_def, Exp.cost]
  congr 1; omega

theorem ite_skip_ok {κ : Caps} {c : Exp} {t : Stm} {s s' : Core} {L : Loc} {ct : Nat} (b : Bool)
    (hc : c.ev κ s L = some (if b then 1 else 0)) (ht : b = true → evalF κ t s L = .ok s' L ct)
      (hs : b = false → s' = s) :
    ∃ n, evalF κ (.ite c t .skip) s L = .ok s' L n ∧ n ≤ 1 + c.cost + max ct 1 := by
  cases b
  · obtain rfl := hs rfl; exact ⟨_, evalF_ite_f (by simpa using hc) evalF_skip, by omega⟩
  · exact ⟨_, evalF_ite_t (v := 1) (by simpa using hc) one_ne_zero (ht rfl), by omega⟩

/-- Update the first-group pointer exactly when its predecessor is absent. -/
theorem write_firstGroup_if_zero {κ : Caps} {s : Core} {L : Loc} {prev w : Nat} {r : Reg}
    (hp : L "gp" = prev) (hw : L r = w) :
    ∃ n, evalF κ (.ite ("gp" =ₑ 0) (.wsc .firstGroup (.var r)) .skip) s L =
      .ok { s with firstGroup := if prev != NIL then s.firstGroup else w } L n ∧
      n ≤ 1 + ("gp" =ₑ 0 : Exp).cost + 3 := by
  refine ite_skip_ok (κ := κ) (L := L) (ct := 3) (prev == NIL) ?_ ?_ ?_
  · simp [Exp.ev, Machine.BinOp.eval, hp, NIL]
  · intro hb
    have hp0 : prev = 0 := by simpa [NIL] using hb
    simp only [hp0, NIL, bne_self_eq_false, Bool.false_eq_true, ite_false, Stm.wsc]
    exact evalF_wrS_ok (κ := κ) (L := L) (k := .firstGroup) (e := .var r) (w := w)
      (by simp [Exp.ev, hw]) rfl
  · intro hb
    have hp0 : (prev != NIL) = true := by simpa [NIL] using hb
    rw [ite_eq_left hp0]

/-- Append a group index to the reversed free-list view, updating the model free list. -/
theorem append_free_group_ok {κ : Caps} {s : Core} {L : Loc} {g : Nat}
    (hg : L "g" = g) (hc : s.freeG.length + 1 ≤ κ.lcap .freeG)
    (hr : 0 < κ.lrec .freeG) :
    evalF κ (.lgrow .freeG 0 "g" 0) s L = .ok { s with freeG := g :: s.freeG } L 22 := by
  have hso : LK.set κ s 0 (LK.view s 0 .freeG ++ [(g, 0)]) .freeG =
      some { s with freeG := g :: s.freeG } := by
    rw [LK.set_ok (by simp [LK.recOk]) (by simp [LK.valid, LK.view]) (by
      simpa [LK.view] using hc) hr]
    simp [LK.put, LK.view, Function.comp_def]
  simp [evalF, Exp.ev, hg, hso, Exp.cost]

/-- **`linkGroupPairS` computes `linkGroupPair`.** -/
theorem linkGroupPairS_agree (κ : Caps) (σ : Core) (L : Loc) {g gl gr labL labR : Nat} (hg : L
  "g" = g)
    (hgl : L "gl" = gl) (hgr : L "gr" = gr) (hlL : L "labL" = labL) (hlR : L "labR" = labR)
    (hgG : g < σ.Gs.size) (hglG : gl < σ.Gs.size) (hgrG : gr < σ.Gs.size)
    (hpG : (σ.Gs.getX g).prev < σ.Gs.size) (hnG : (σ.Gs.getX g).next < σ.Gs.size)
    (hcC : (σ.Gs.getX g).chk < σ.C.size) (hG : σ.Gs.size ≤ κ.tbl .G) (hC : σ.C.size ≤ κ.tbl .C) :
    ∃ L' n, evalF κ linkGroupPairS σ L = .ok (linkGroupPair σ g gl gr labL labR) L' n ∧ n ≤ 150
      := by
  set G := σ.Gs.getX g
  set c := G.chk
  set C := σ.C.getX c
  have hgT : g < κ.tbl .G := by omega
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "gp") (e := .gF .prev "g") (v :=
    G.prev)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L "gp" G.prev) (x := "gn") (e := .gF
    .next "g") (v := G.next)
    (by simp [Exp.gF, Exp.ev, Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, G,
      hgT])
  have e3 := evalF_assign_ok (κ := κ) (s := σ) (L := upd (upd L "gp" G.prev) "gn" G.next) (x := "c")
    (e := .gF .chk "g") (v := c) (by simp [Exp.gF, Exp.ev, Machine.State.upd, hg, Fld.cap,
      Fld.get, GF.get, c, G, hgT])
  set L3 := upd (upd (upd L "gp" G.prev) "gn" G.next) "c" c
  have r : ∀ x, x ≠ "gp" → x ≠ "gn" → x ≠ "c" → L3 x = L x := fun x h1 h2 h3 => by
    simp [L3, Machine.State.upd, h1, h2, h3]
  have rg := r "g" (by decide) (by decide) (by decide)
  have rgl := r "gl" (by decide) (by decide) (by decide)
  have rgr := r "gr" (by decide) (by decide) (by decide)
  have rlL := r "labL" (by decide) (by decide) (by decide)
  have rlR := r "labR" (by decide) (by decide) (by decide)
  have rgp : L3 "gp" = G.prev := by simp [L3, Machine.State.upd]
  have rgn : L3 "gn" = G.next := by simp [L3, Machine.State.upd]
  have rc : L3 "c" = c := by simp [L3, Machine.State.upd]
  -- the left sibling
  set A0 := σ.Gs.modify gl fun X => {
    X with
    lab := labL
    st := .overflow
    src := g
    prev := G.prev
    next := g
  }
  have b1 : evalF κ lgpA0 σ L3 = .ok {
    σ with
    Gs := A0
  } L3 15 := by
    simp only [lgpA0, Stm.wgF]
    rw [five_wrG (x := "gl") (j := gl) (w1 := labL) (w2 := 1) (w3 := g) (w4 := G.prev) (w5 := g)
      (by rw [rgl, hgl]) hglG  (fun _ => by simp [Exp.ev, rlL, hlL])
      (fun _ => rfl) (fun _ => by simp [Exp.ev, rg, hg]) (fun _ => by simp [Exp.ev, rgp])
      (fun _ => by simp [Exp.ev, rg, hg]) rfl rfl rfl rfl rfl]
    rfl
  -- the left neighbour
  set A1 := if G.prev != NIL then A0.modify G.prev (fun X => {
    X with
    next := gl
  }) else A0
  obtain ⟨n2, b2, hn2⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gp" =ₑ 0)) (t := .wgF .next "gp" "gl")
    (s := {
      σ with
      Gs := A0
    }) (s' := {
      σ with
      Gs := A1
    }) (L := L3) (ct := 3) (G.prev != NIL)
    (by by_cases h : G.prev = 0 <;> simp [Exp.ev, Machine.BinOp.eval, Machine.UnOp.eval, rgp, h,
      NIL])
    (fun hb => by
      have hb' : G.prev ≠ 0 := by simpa [NIL] using hb
      simp only [A1, hb, ite_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgp]) (by simp [Exp.ev, rgl, hgl]) (by
        simpa [A0] using hpG)  rfl)
    (fun hb => by simp [A1, hb])
  -- the right sibling
  set A2 := A1.modify gr fun X => {
    X with
    lab := labR
    st := .overflow
    src := g
    prev := g
    next := G.next
  }
  have hA1 : A1.size = σ.Gs.size := by simp only [A1, A0]; split <;> simp
  have b3 : evalF κ lgpA2 {
    σ with
    Gs := A1
  } L3 = .ok {
    σ with
    Gs := A2
  } L3 15 := by
    simp only [lgpA2, Stm.wgF]
    rw [five_wrG (x := "gr") (j := gr) (w1 := labR) (w2 := 1) (w3 := g) (w4 := g) (w5 := G.next)
      (by rw [rgr, hgr]) (by simp [hA1, hgrG])  (fun _ => by simp [Exp.ev, rlR, hlR])
      (fun _ => rfl) (fun _ => by simp [Exp.ev, rg, hg]) (fun _ => by simp [Exp.ev, rg, hg])
      (fun _ => by simp [Exp.ev, rgn]) rfl rfl rfl rfl rfl]
    rfl
  have hA2 : A2.size = σ.Gs.size := by simp [A2, hA1]
  -- the right neighbour
  set A3 := if G.next != NIL then A2.modify G.next (fun X => {
    X with
    prev := gr
  }) else A2
  obtain ⟨n4, b4, hn4⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gn" =ₑ 0)) (t := .wgF .prev "gn" "gr")
    (s := {
      σ with
      Gs := A2
    }) (s' := {
      σ with
      Gs := A3
    }) (L := L3) (ct := 3) (G.next != NIL)
    (by by_cases h : G.next = 0 <;> simp [Exp.ev, Machine.BinOp.eval, Machine.UnOp.eval, rgn, h,
      NIL])
    (fun hb => by
      simp only [A3, hb, ite_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgn]) (by simp [Exp.ev, rgr, hgr]) (by
        simpa [hA2] using hnG)  rfl)
    (fun hb => by simp [A3, hb])
  have hA3 : A3.size = σ.Gs.size := by simp only [A3]; split <;> simp [hA2]
  -- the chunk's first group
  have hcT : c < κ.tbl .C := by omega
  set C1 := if C.first == g then σ.C.modify c (fun X => {
    X with
    first := gl
  }) else σ.C
  obtain ⟨n5, b5, hn5⟩ := ite_skip_ok (κ := κ) (c := .cF .first "c" =ₑ "g") (t := .wcF .first
    "c" "gl")
    (s := {
      σ with
      Gs := A3
    }) (s' := {
      σ with
      Gs := A3
      C := C1
    }) (L := L3) (ct := 3) (C.first == g)
    (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, rc, rg, hg, hcT, Fld.cap,
      Fld.get, CF.get, C])
    (fun hb => by
      simp only [C1, hb, ite_true, Stm.wcF]
      exact evalF_wrC_ok (by simp [Exp.ev, rc]) (by simp [Exp.ev, rgl, hgl]) hcC  rfl)
    (fun hb => by simp [C1, hb])
  -- `g` itself
  set A4 := A3.modify g fun X => {
    X with
    prev := gl
    next := gr
    st := .splitting
    l := gl
    r := gr
  }
  have b6 : evalF κ lgpG {
    σ with
    Gs := A3
    C := C1
  } L3 = .ok {
    σ with
    Gs := A4
    C := C1
  } L3 15 := by
    simp only [lgpG, Stm.wgF]
    rw [five_wrG (x := "g") (j := g) (w1 := gl) (w2 := gr) (w3 := 2) (w4 := gl) (w5 := gr)
      (by rw [rg, hg]) (by simp [hA3, hgG])  (fun _ => by simp [Exp.ev, rgl, hgl])
      (fun _ => by simp [Exp.ev, rgr, hgr]) (fun _ => rfl) (fun _ => by simp [Exp.ev, rgl, hgl])
      (fun _ => by simp [Exp.ev, rgr, hgr]) rfl rfl rfl rfl rfl]
    rfl
  -- the chunk's last group
  have hC1 : (C1.getX c).last = C.last := by simp only [C1]; split <;> simp [ C]; split <;> rfl
  have hC1s : C1.size = σ.C.size := by simp only [C1]; split <;> simp
  set C2 := if C.last == g then C1.modify c (fun X => {
    X with
    last := gr
  }) else C1
  obtain ⟨n7, b7, hn7⟩ := ite_skip_ok (κ := κ) (c := .cF .last "c" =ₑ "g") (t := .wcF .last "c"
    "gr")
    (s := {
      σ with
      Gs := A4
      C := C1
    }) (s' := {
      σ with
      Gs := A4
      C := C2
    }) (L := L3) (ct := 3) (C.last == g)
    (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, rc, rg, hg, hcT, Fld.cap,
      Fld.get, CF.get, hC1])
    (fun hb => by
      simp only [C2, hb, ite_true, Stm.wcF]
      exact evalF_wrC_ok (by simp [Exp.ev, rc]) (by simp [Exp.ev, rgr, hgr]) (by
        rw [hC1s]
        exact hcC)  rfl)
    (fun hb => by simp [C2, hb])
  -- the first group of the structure
  obtain ⟨n8, b8, hn8⟩ := write_firstGroup_if_zero
    (κ := κ) (s := { σ with Gs := A4, C := C2 }) (L := L3) (prev := G.prev)
    (w := gl) (r := "gl") rgp (by rw [rgl, hgl])
  refine ⟨L3, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 b1
    (evalF_seq_ok2 b2
    (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 (evalF_seq_ok2 b5 (evalF_seq_ok2 b6 (evalF_seq_ok2 b7
      b8))))))))), ?_⟩
  simp only [Exp.cost, Exp.gF, Exp.cF] at hn2 hn4 hn5 hn7 hn8 ⊢
  omega

/-! ### `unlinkGroup` -/

/-- Test whether the group being removed is its chunk's only group. -/
def ulCE : Exp := cme{ cf = g && cl = g }
/-- Mark a removed group dead and clear its list links. -/
def ulG : Stm := cm{ G[g].dead := 1; G[g].next := 0; G[g].prev := 0 }
/-- `unlinkGroup`: unlink `g` from the group list and its chunk, and free it (local `g`). -/
def unlinkGroupS : Stm := cm{
  gp := G[g].prev; gn := G[g].next; c := G[g].chk
  if gp ≠ 0 then G[gp].next := gn
  if gn ≠ 0 then G[gn].prev := gp
  ulG
  cf := C[c].first; cl := C[c].last
  if ‹ulCE› then { C[c].first := 0; C[c].last := 0 }
  else if cf = g then C[c].first := gn
  else if cl = g then C[c].last := gp
  if gp = 0 then S.firstGroup := gn
  append freeG[0] (g, 0) }

theorem unlinkGroupS_agree (κ : Caps) (σ : Core) (L : Loc) {g : Nat} (hg : L "g" = g)
    (hgG : g < σ.Gs.size) (hpG : (σ.Gs.getX g).prev < σ.Gs.size) (hnG : (σ.Gs.getX g).next <
      σ.Gs.size)
    (hcC : (σ.Gs.getX g).chk < σ.C.size) (hG : σ.Gs.size ≤ κ.tbl .G) (hC : σ.C.size ≤ κ.tbl .C)
    (hF : σ.freeG.length + 1 ≤ κ.lcap .freeG) (hF0 : 0 < κ.lrec .freeG) :
    ∃ L' n, evalF κ unlinkGroupS σ L = .ok (unlinkGroup σ g) L' n ∧ L' "g" = g ∧ n ≤ 150 := by
  set G := σ.Gs.getX g
  set c := G.chk
  set C := σ.C.getX c
  have hgT : g < κ.tbl .G := by omega
  have hcT : c < κ.tbl .C := by omega
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "gp") (e := .gF .prev "g") (v :=
    G.prev)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L "gp" G.prev) (x := "gn") (e := .gF
    .next "g") (v := G.next)
    (by simp [Exp.gF, Exp.ev, Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, G,
      hgT])
  have e3 := evalF_assign_ok (κ := κ) (s := σ) (L := upd (upd L "gp" G.prev) "gn" G.next) (x := "c")
    (e := .gF .chk "g") (v := c) (by simp [Exp.gF, Exp.ev, Machine.State.upd, hg, Fld.cap,
      Fld.get, GF.get, c, G, hgT])
  set L3 := upd (upd (upd L "gp" G.prev) "gn" G.next) "c" c
  have rg : L3 "g" = g := by simp [L3, Machine.State.upd, hg]
  have rgp : L3 "gp" = G.prev := by simp [L3, Machine.State.upd]
  have rgn : L3 "gn" = G.next := by simp [L3, Machine.State.upd]
  have rc : L3 "c" = c := by simp [L3, Machine.State.upd]
  -- the neighbours
  set A1 := if G.prev != NIL then σ.Gs.modify G.prev (fun X => {
    X with
    next := G.next
  }) else σ.Gs
  obtain ⟨n4, b4, hn4⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gp" =ₑ 0)) (t := .wgF .next "gp" "gn")
    (s := σ) (s' := {
      σ with
      Gs := A1
    }) (L := L3) (ct := 3) (G.prev != NIL)
    (by by_cases h : G.prev = 0 <;> simp [Exp.ev, Machine.BinOp.eval, Machine.UnOp.eval, rgp, h,
      NIL])
    (fun hb => by
      simp only [A1, hb, ite_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgp]) (by simp [Exp.ev, rgn]) hpG  rfl)
    (fun hb => by simp [A1, hb])
  have hA1 : A1.size = σ.Gs.size := by simp only [A1]; split <;> simp
  set A2 := if G.next != NIL then A1.modify G.next (fun X => {
    X with
    prev := G.prev
  }) else A1
  obtain ⟨n5, b5, hn5⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gn" =ₑ 0)) (t := .wgF .prev "gn" "gp")
    (s := {
      σ with
      Gs := A1
    }) (s' := {
      σ with
      Gs := A2
    }) (L := L3) (ct := 3) (G.next != NIL)
    (by by_cases h : G.next = 0 <;> simp [Exp.ev, Machine.BinOp.eval, Machine.UnOp.eval, rgn, h,
      NIL])
    (fun hb => by
      simp only [A2, hb, ite_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgn]) (by simp [Exp.ev, rgp]) (by simp only [hA1]; exact
        hnG)  rfl)
    (fun hb => by simp [A2, hb])
  have hA2 : A2.size = σ.Gs.size := by simp only [A2]; split <;> simp [hA1]
  -- `g` itself
  set A3 := A2.modify g fun X => {
    X with
    alive := false
    next := NIL
    prev := NIL
  }
  have b6 : evalF κ ulG {
    σ with
    Gs := A2
  } L3 = .ok {
    σ with
    Gs := A3
  } L3 9 := by
    simp only [ulG, Stm.wgF]
    have hv : ∀ s' : Core, (Exp.var "g").ev κ s' L3 = some g := fun _ => by simp [Exp.ev, rg]
    rw [evalF_seq_ok2 (evalF_wrG_ok (hv _) rfl (by simp [hA2, hgG])  rfl)
      (evalF_seq_ok2 (evalF_wrG_ok (hv _) rfl (by simp [hA2, hgG])  rfl)
        (evalF_wrG_ok (hv _) rfl (by simp [hA2, hgG])  rfl))]
    simp only [Array.modify_modify_same, Function.comp_def, Exp.cost]
    rfl
  -- the chunk
  have ecf := evalF_assign_ok (κ := κ) (s := {
    σ with
    Gs := A3
  }) (L := L3) (x := "cf") (e := .cF .first "c")
    (v := C.first) (by simp [Exp.cF, Exp.ev, rc, hcT, Fld.cap, Fld.get, CF.get, C])
  have ecl := evalF_assign_ok (κ := κ) (s := {
    σ with
    Gs := A3
  }) (L := upd L3 "cf" C.first) (x := "cl")
    (e := .cF .last "c") (v := C.last) (by simp [Exp.cF, Exp.ev, Machine.State.upd, rc, hcT,
      Fld.cap, Fld.get, CF.get, C])
  set L5 := upd (upd L3 "cf" C.first) "cl" C.last
  have r5 : ∀ x, x ≠ "cf" → x ≠ "cl" → L5 x = L3 x := fun x h1 h2 => by simp [L5,
    Machine.State.upd, h1, h2]
  set C' := if C.first == g && C.last == g then σ.C.modify c (fun X => {
    X with
    first := NIL
    last := NIL
  })
      else if C.first == g then σ.C.modify c (fun X => {
        X with
        first := G.next
      })
      else if C.last == g then σ.C.modify c (fun X => {
        X with
        last := G.prev
      })
      else σ.C
  have hcv : ∀ s' : Core, (Exp.var "c").ev κ s' L5 = some c := fun _ => by
    simp [Exp.ev, r5 "c" (by decide) (by decide), rc]
  have b7 : ∃ n7, evalF κ (.ite ulCE (.wcF .first "c" 0;; .wcF .last "c" 0)
      (.ite ("cf" =ₑ "g") (.wcF .first "c" "gn") (.ite ("cl" =ₑ "g") (.wcF .last "c" "gp") .skip)))
      {
        σ with
        Gs := A3
      } L5 = .ok {
        σ with
        Gs := A3
        C := C'
      } L5 n7 ∧ n7 ≤ 30 := by
    have h5f : L5 "cf" = C.first := by simp [L5, Machine.State.upd]
    have h5l : L5 "cl" = C.last := by simp [L5, Machine.State.upd]
    have h5g : L5 "g" = g := by rw [r5 "g" (by decide) (by decide), rg]
    have h5p : L5 "gp" = G.prev := by rw [r5 "gp" (by decide) (by decide), rgp]
    have h5n : L5 "gn" = G.next := by rw [r5 "gn" (by decide) (by decide), rgn]
    simp only [Stm.wcF]
    have hcs : (({
      σ with
      Gs := A3
    } : Core)).C.size = σ.C.size := rfl
    by_cases hf : C.first = g <;> by_cases hl : C.last = g
    · have hC' : C' = (σ.C.modify c (CF.set · 0 .first)).modify c (CF.set · 0 .last) := by
        rw [Array.modify_modify_same]; simp [C', hf, hl]; rfl
      have w1 := evalF_wrC_ok (κ := κ) (s := {
        σ with
        Gs := A3
      }) (L := L5) (k := .first) (e := (0 : Exp)) (w := 0)
        (hcv _) rfl hcC  rfl
      have w2 := evalF_wrC_ok (κ := κ) (s := {
        σ with
        Gs := A3
        C := σ.C.modify c (CF.set · 0 .first)
      }) (L := L5)
        (k := .last) (e := (0 : Exp)) (w := 0) (hcv _) rfl (by simp [hcC])  rfl
      rw [hC']
      exact ⟨_, evalF_ite_t (v := 1) (by simp [ulCE, Exp.ev, Machine.BinOp.eval, h5f, h5l, h5g,
        hf, hl])
        one_ne_zero (evalF_seq_ok2 w1 w2), by simp [Exp.cost, ulCE]⟩
    · have hC' : C' = σ.C.modify c (CF.set · G.next .first) := by simp [C', hf, hl]; rfl
      have w1 := evalF_wrC_ok (κ := κ) (s := {
        σ with
        Gs := A3
      }) (L := L5) (k := .first) (e := .var "gn")
        (w := G.next) (hcv _) (by simp [Exp.ev, h5n]) hcC  rfl
      rw [hC']
      exact ⟨_, evalF_ite_f (by simp [ulCE, Exp.ev, Machine.BinOp.eval, h5f, h5l, h5g, hf, hl])
        (evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, h5f, h5g, hf]) one_ne_zero w1),
        by simp [Exp.cost, ulCE]⟩
    · have hC' : C' = σ.C.modify c (CF.set · G.prev .last) := by simp [C', hf, hl]; rfl
      have w1 := evalF_wrC_ok (κ := κ) (s := {
        σ with
        Gs := A3
      }) (L := L5) (k := .last) (e := .var "gp")
        (w := G.prev) (hcv _) (by simp [Exp.ev, h5p]) hcC  rfl
      rw [hC']
      exact ⟨_, evalF_ite_f (by simp [ulCE, Exp.ev, Machine.BinOp.eval, h5f, h5l, h5g, hf, hl])
        (evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, h5f, h5g, hf])
          (evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, h5l, h5g, hl]) one_ne_zero
            w1)),
        by simp [Exp.cost, ulCE]⟩
    · have hC' : C' = σ.C := by simp [C', hf, hl]
      rw [hC']
      exact ⟨_, evalF_ite_f (by simp [ulCE, Exp.ev, Machine.BinOp.eval, h5f, h5l, h5g, hf, hl])
        (evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, h5f, h5g, hf])
          (evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, h5l, h5g, hl]) evalF_skip)),
        by simp [Exp.cost, ulCE]⟩
  obtain ⟨n7, b7, hn7⟩ := b7
  set fg := if G.prev != NIL then σ.firstGroup else G.next
  obtain ⟨n8, b8, hn8⟩ := write_firstGroup_if_zero
    (κ := κ) (s := { σ with Gs := A3, C := C' }) (L := L5) (prev := G.prev)
    (w := G.next) (r := "gn")
    (by rw [r5 "gp" (by decide) (by decide), rgp])
    (by rw [r5 "gn" (by decide) (by decide), rgn])
  set S8 : Core := {
    σ with
    Gs := A3
    C := C'
    firstGroup := fg
  }
  have b9 := append_free_group_ok (κ := κ) (s := S8) (L := L5) (g := g)
    (by rw [r5 "g" (by decide) (by decide), rg]) hF hF0
  refine ⟨L5, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 b4
    (evalF_seq_ok2 b5
    (evalF_seq_ok2 b6 (evalF_seq_ok2 ecf (evalF_seq_ok2 ecl (evalF_seq_ok2 b7 (evalF_seq_ok2 b8
      b9))))))))),
    by rw [r5 "g" (by decide) (by decide), rg], ?_⟩
  simp only [Exp.cost, Exp.gF, Exp.cF] at hn4 hn5 hn8 ⊢
  omega

/-! ### Moving one element -/

theorem evalF_wrE_ok {κ : Caps} {s : Core} {L : Loc} {k : EF} {i e : Exp} {j w : Nat} (hi : i.ev
  κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.E.size) (hk : k.ok w = true) :
    evalF κ (.wr (.e k) i e) s L = .ok {
      s with
      E := s.E.modify j (EF.set · w k)
    } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

/-- Remove an endpoint element from its source group, clearing both endpoints if empty. -/
def mvGS (first : Bool) : Stm :=
  if first then cm{ if f = l then { G[g].first := 0; G[g].last := 0 } else G[g].first := en }
  else cm{ if f = l then { G[g].first := 0; G[g].last := 0 } else G[g].last := en }
/-- Attach a moving element to the corresponding end of its destination group. -/
def mvDS (first : Bool) : Stm :=
  if first then cm{ if G[d].first = 0 then G[d].first := e; G[d].last := e }
  else cm{ if G[d].first = 0 then G[d].last := e; G[d].first := e }
/-- Set the moving element's containing group and new label. -/
def mvES : Stm := cm{ E[e].grp := d; E[e].lab := lab }

/-- Move the first or last element of `g` to the corresponding end of `d`, with label `lab`.
The first of `g` goes to the end of `d`
(`first`), or the last of `g` to the front of `d` (locals `g d e lab`). -/
def moveS (first : Bool) : Stm := cm{
  f := G[g].first; l := G[g].last; en := E[e].‹if first then .next else .prev›
  ‹mvGS first›; ‹mvDS first›; mvES }

theorem moveS_agree (κ : Caps) (σ : Core) (L : Loc) (first : Bool) {g d e lab : Nat} (hg : L "g"
  = g)
    (hd : L "d" = d) (he : L "e" = e) (hl : L "lab" = lab) (hgG : g < σ.Gs.size) (hdG : d <
      σ.Gs.size)
    (heE : e < σ.E.size) (hG : σ.Gs.size ≤ κ.tbl .G) (hE : σ.E.size ≤ κ.tbl .E) :
    ∃ L' n, evalF κ (moveS first) σ L =
      .ok (if first then moveFirstLeft σ g d e lab else moveLastRight σ g d e lab) L' n ∧ n ≤ 80
        := by
  set G := σ.Gs.getX g
  set en := if first then (σ.E.getX e).next else (σ.E.getX e).prev
  have hgT : g < κ.tbl .G := by omega
  have hdT : d < κ.tbl .G := by omega
  have heT : e < κ.tbl .E := by omega
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "f") (e := .gF .first "g") (v :=
    G.first)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L "f" G.first) (x := "l") (e := .gF
    .last "g") (v := G.last)
    (by simp [Exp.gF, Exp.ev, Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, G,
      hgT])
  have e3 := evalF_assign_ok (κ := κ) (s := σ) (L := upd (upd L "f" G.first) "l" G.last) (x := "en")
    (e := .eF (if first then .next else .prev) "e") (v := en)
    (by cases first <;> simp [Exp.eF, Exp.ev, Machine.State.upd, he, Fld.cap, Fld.get, EF.get,
      en, heT])
  set L3 := upd (upd (upd L "f" G.first) "l" G.last) "en" en
  have r : ∀ x, x ≠ "f" → x ≠ "l" → x ≠ "en" → L3 x = L x := fun x h1 h2 h3 => by
    simp [L3, Machine.State.upd, h1, h2, h3]
  have rg : L3 "g" = g := by rw [r "g" (by decide) (by decide) (by decide), hg]
  have rd : L3 "d" = d := by rw [r "d" (by decide) (by decide) (by decide), hd]
  have re : L3 "e" = e := by rw [r "e" (by decide) (by decide) (by decide), he]
  have rl : L3 "lab" = lab := by rw [r "lab" (by decide) (by decide) (by decide), hl]
  have rf : L3 "f" = G.first := by simp [L3, Machine.State.upd]
  have rll : L3 "l" = G.last := by simp [L3, Machine.State.upd]
  have ren : L3 "en" = en := by simp [L3, Machine.State.upd]
  have hvg : ∀ s' : Core, (Exp.var "g").ev κ s' L3 = some g := fun _ => by simp [Exp.ev, rg]
  have hvd : ∀ s' : Core, (Exp.var "d").ev κ s' L3 = some d := fun _ => by simp [Exp.ev, rd]
  have hve : ∀ s' : Core, (Exp.var "e").ev κ s' L3 = some e := fun _ => by simp [Exp.ev, re]
  -- the source group
  set A1 := σ.Gs.modify g fun X => if G.first == G.last then {
    X with
    first := NIL
    last := NIL
  }
    else if first then {
      X with
      first := en
    } else {
      X with
      last := en
    }
  have b4 : ∃ n4, evalF κ (mvGS first) σ L3 = .ok {
    σ with
    Gs := A1
  } L3 n4 ∧ n4 ≤ 15 := by
    by_cases hfl : G.first = G.last
    · have w1 := evalF_wrG_ok (κ := κ) (s := σ) (L := L3) (k := .first) (e := (0 : Exp)) (w :=
        0) (hvg _) rfl hgG  rfl
      have w2 := evalF_wrG_ok (κ := κ) (s := {
        σ with
        Gs := σ.Gs.modify g (GF.set · 0 .first)
      }) (L := L3)
        (k := .last) (e := (0 : Exp)) (w := 0) (hvg _) rfl (by simp [hgG])  rfl
      have hA : A1 = (σ.Gs.modify g (GF.set · 0 .first)).modify g (GF.set · 0 .last) := by
        rw [Array.modify_modify_same]; simp only [A1, hfl, beq_self_eq_true, ite_true]; rfl
      rw [hA]
      have ec : ("f" =ₑ "l" : Exp).ev κ σ L3 = some 1 := by
        simp [Exp.ev, Machine.BinOp.eval, rf, rll, hfl]
      cases first <;> exact ⟨_, evalF_ite_t ec one_ne_zero (evalF_seq_ok2 w1 w2), by simp
        [Exp.cost]⟩
    · have ec : ("f" =ₑ "l" : Exp).ev κ σ L3 = some 0 := by
        simp [Exp.ev, Machine.BinOp.eval, rf, rll, hfl]
      cases first
      · have w1 := evalF_wrG_ok (κ := κ) (s := σ) (L := L3) (k := .last) (e := .var "en") (w :=
          en) (hvg _)
          (by simp [Exp.ev, ren]) hgG  rfl
        have hA : A1 = σ.Gs.modify g (GF.set · en .last) := by
          simp only [A1, show (G.first == G.last) = false by simpa using hfl]; rfl
        rw [hA]; exact ⟨_, evalF_ite_f ec w1, by simp [Exp.cost]⟩
      · have w1 := evalF_wrG_ok (κ := κ) (s := σ) (L := L3) (k := .first) (e := .var "en") (w :=
          en) (hvg _)
          (by simp [Exp.ev, ren]) hgG  rfl
        have hA : A1 = σ.Gs.modify g (GF.set · en .first) := by
          simp only [A1, show (G.first == G.last) = false by simpa using hfl]; rfl
        rw [hA]; exact ⟨_, evalF_ite_f ec w1, by simp [Exp.cost]⟩
  obtain ⟨n4, b4, hn4⟩ := b4
  -- the destination group
  have hA1s : A1.size = σ.Gs.size := by simp [A1]
  set D1 := A1.getX d
  set A2 := A1.modify d fun X => if first then {
    X with
    first := if X.first == NIL then e else X.first
    last := e
  }
    else {
      X with
      last := if X.first == NIL then e else X.last
      first := e
    }
  have b5 : ∃ n5, evalF κ (mvDS first) {
    σ with
    Gs := A1
  } L3 = .ok {
    σ with
    Gs := A2
  } L3 n5 ∧ n5 ≤ 15 := by
    have ec : (.gF .first "d" =ₑ 0 : Exp).ev κ {
      σ with
      Gs := A1
    } L3 = some (if D1.first = 0 then 1 else 0) := by
      simp [Exp.gF, Exp.ev, Machine.BinOp.eval, rd, hdT, Fld.cap, Fld.get,
        GF.get, D1]
    by_cases h0 : D1.first = 0
    · have h0' : (A1.getX d).first = 0 := h0
      rw [ite_eq_left h0] at ec
      cases first
      · have w1 := evalF_wrG_ok (κ := κ) (s := {
        σ with
        Gs := A1
      }) (L := L3) (k := .last) (e := .var "e") (w := e)
          (hvd _) (hve _) (by simp [hA1s, hdG])  rfl
        have w2 := evalF_wrG_ok (κ := κ) (s := {
          σ with
          Gs := A1.modify d (GF.set · e .last)
        }) (L := L3) (k := .first)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG])  rfl
        have hA : A2 = (A1.modify d (GF.set · e .last)).modify d (GF.set · e .first) := by
          rw [Array.modify_modify_same]; apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_t ec one_ne_zero w1) w2, by simp [Exp.cost, Exp.gF]⟩
      · have w1 := evalF_wrG_ok (κ := κ) (s := {
        σ with
        Gs := A1
      }) (L := L3) (k := .first) (e := .var "e") (w := e)
          (hvd _) (hve _) (by simp [hA1s, hdG])  rfl
        have w2 := evalF_wrG_ok (κ := κ) (s := {
          σ with
          Gs := A1.modify d (GF.set · e .first)
        }) (L := L3) (k := .last)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG])  rfl
        have hA : A2 = (A1.modify d (GF.set · e .first)).modify d (GF.set · e .last) := by
          rw [Array.modify_modify_same]; apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_t ec one_ne_zero w1) w2, by simp [Exp.cost, Exp.gF]⟩
    · have h0' : ¬(A1.getX d).first = 0 := h0
      rw [ite_eq_right h0] at ec
      cases first
      · have w2 := evalF_wrG_ok (κ := κ) (s := {
        σ with
        Gs := A1
      }) (L := L3) (k := .first)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG])  rfl
        have hA : A2 = A1.modify d (GF.set · e .first) := by
          apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_f ec evalF_skip) w2, by simp [Exp.cost, Exp.gF]⟩
      · have w2 := evalF_wrG_ok (κ := κ) (s := {
        σ with
        Gs := A1
      }) (L := L3) (k := .last)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG])  rfl
        have hA : A2 = A1.modify d (GF.set · e .last) := by
          apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_f ec evalF_skip) w2, by simp [Exp.cost, Exp.gF]⟩
  obtain ⟨n5, b5, hn5⟩ := b5
  -- the element
  have w6 := evalF_wrE_ok (κ := κ) (s := {
    σ with
    Gs := A2
  }) (L := L3) (k := .grp) (e := .var "d") (w := d)
    (hve _) (hvd _) heE  rfl
  have w7 := evalF_wrE_ok (κ := κ) (s := {
    σ with
    Gs := A2
    E := σ.E.modify e (EF.set · d .grp)
  }) (L := L3)
    (k := .lab) (e := .var "lab") (w := lab) (hve _) (by simp [Exp.ev, rl]) (by simp [heE])  rfl
  have hfin : {
    σ with
    Gs := A2
    E := (σ.E.modify e (EF.set · d .grp)).modify e (EF.set · lab .lab)
  } =
      (if first then moveFirstLeft σ g d e lab else moveLastRight σ g d e lab) := by
    rw [Array.modify_modify_same]
    cases first <;> rfl
  refine ⟨L3, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 b4
    (evalF_seq_ok2 b5
    (by simp only [mvES, Stm.weF]; rw [← hfin]; exact evalF_seq_ok2 w6 w7))))), ?_⟩
  simp only [Exp.cost, Exp.gF, Exp.eF] at hn4 hn5 ⊢
  omega

/-! ### Label primitives -/

theorem guard_run_ne {α : Type} {msg : String} {s s' : Core} {v : α} :
  (OrderMaintenance.Model.guard msg : CM α).run s ≠ .ok v s' := by
  simp [OrderMaintenance.Model.guard]

/-- `lab := between a b` (locals `a b`). -/
def betweenS : Stm := cm{ if b ≤ a + 1 then fail else lab := (a + b) / 2 }
/-- `lab := after a D B` (locals `a D B`). -/
def afterS : Stm := cm{
  v := a + D
  if 1 <<< B ≤ v || v ≤ a then fail else lab := v }
/-- `lab := before b D` (locals `b D`). -/
def beforeS : Stm := cm{ if b < D || D = 0 then fail else lab := b - D }

theorem between_inv {a b : Nat} {why : String} {s s' : Core} {v : Nat} (h : (between a b
  why).run s = .ok v s') :
    s' = s ∧ a + 1 < b ∧ v = (a + b) / 2 := by
  unfold between at h
  by_cases hc : a + 1 ≥ b
  · simp only [ge_iff_le, hc, ↓reduceIte, Model.guard, bind_pure_comp] at h
    cases h
  · simp only [ge_iff_le, hc, ↓reduceIte, EStateM.run_pure, EStateM.Result.ok.injEq] at h
    exact ⟨h.2.symm, by omega, h.1.symm⟩

theorem after_inv {a D B : Nat} {why : String} {s s' : Core} {v : Nat} (h : (after a D B
  why).run s = .ok v s') :
    s' = s ∧ a + D < 1 <<< B ∧ a < a + D ∧ v = a + D := by
  unfold after at h
  dsimp only at h
  split at h
  · change EStateM.Result.error (Err.guard why) s = .ok v s' at h
    cases h
  · next hgood =>
    have hg : ¬(a + D ≥ 1 <<< B ∨ a + D ≤ a) := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hgood
    have hv : a + D = v ∧ s = s' := by simpa using h
    exact ⟨hv.2.symm, by omega, by omega, hv.1.symm⟩

theorem before_inv {b D : Nat} {why : String} {s s' : Core} {v : Nat} (h : (before b D why).run
  s = .ok v s') :
    s' = s ∧ D ≤ b ∧ D ≠ 0 ∧ v = b - D := by
  unfold before at h
  split at h
  · change EStateM.Result.error (Err.guard why) s = .ok v s' at h
    cases h
  · next hgood =>
    have hg : ¬(b < D ∨ D = 0) := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] using hgood
    have hv : b - D = v ∧ s = s' := by simpa using h
    exact ⟨hv.2.symm, by omega, by omega, hv.1.symm⟩

theorem betweenS_ok {κ : Caps} {s : Core} {L : Loc} {a b : Nat} (ha : L "a" = a) (hb : L "b" =
  b) (h : a + 1 < b) :
    ∃ c, evalF κ betweenS s L = .ok s (upd L "lab" ((a + b) / 2)) c ∧ c ≤ 15 := by
  have : ¬ b ≤ a + 1 := by omega
  refine ⟨12, ?_, by omega⟩
  simp [betweenS, evalF, Exp.ev, Machine.BinOp.eval, ha, hb, this, Exp.cost,
    Res.addCost]

theorem afterS_ok {κ : Caps} {s : Core} {L : Loc} {a D B : Nat} (ha : L "a" = a) (hD : L "D" =
  D) (hB : L "B" = B)
    (h1 : a + D < 1 <<< B) (h2 : a < a + D) :
    ∃ c, evalF κ afterS s L = .ok s (upd (upd L "v" (a + D)) "lab" (a + D)) c ∧ c ≤ 20 := by
  have h1' : ¬ 1 * 2 ^ B ≤ a + D := by rw [Nat.shiftLeft_eq] at h1; omega
  have h2' : D ≠ 0 := by omega
  have h3 : a + D < 2 ^ B := by omega
  refine ⟨16, ?_, by omega⟩
  simp only [afterS, Exp.add_def, Exp.ofNat_def, evalF, Res.bind, Exp.ev, ha, hD, BinOp.eval,
      Option.bind_some, Exp.cost, Nat.reduceAdd, Res.addCost, Machine.State.upd,
      String.reduceEq, ↓reduceIte, hB, one_mul, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
      h2', ne_eq, not_true_eq_false, or_false, ite_not, ite_eq_right_iff, one_ne_zero,
      imp_false, not_le, ite_eq_left_iff, not_lt]
  rw [ite_eq_left h3]; simp [Machine.State.upd]

theorem beforeS_ok {κ : Caps} {s : Core} {L : Loc} {b D : Nat} (hb : L "b" = b) (hD : L "D" = D)
    (h1 : D ≤ b) (h2 : D ≠ 0) : evalF κ beforeS s L = .ok s (upd L "lab" (b - D)) 12 := by
  have : ¬ b < D := by omega
  simp [beforeS, evalF, Exp.ev, Machine.BinOp.eval, hb, hD, this, h1, h2,
    Exp.cost, Res.addCost]

/-! ### `labBefore`, `labAfter` -/

/-- `lab := labBefore g` (local `g`). -/
def labBeforeS : Stm := cm{
  c := G[g].chk
  if C[c].first = g then { b := G[g].lab; D := P.Dg; beforeS }
  else { a := G[G[g].prev].lab; b := G[g].lab; betweenS } }

/-- `lab := labAfter g` (local `g`). -/
def labAfterS : Stm := cm{
  c := G[g].chk
  if C[c].last = g then { a := G[g].lab; D := P.Dg; B := P.Bg; afterS }
  else { a := G[g].lab; b := G[G[g].next].lab; betweenS } }

theorem labBeforeS_agree (κ : Caps) (σ : Core) (L : Loc) {g : Nat} (hg : L "g" = g) (hgT : g <
  κ.tbl .G)
    (hcT : (σ.Gs.getX g).chk < κ.tbl .C) (hpT : (σ.Gs.getX g).prev < κ.tbl .G) {v : Nat} {σ' : Core}
    (h : (labBefore g).run σ = .ok v σ') :
    σ' = σ ∧ ∃ L' c, evalF κ labBeforeS σ L = .ok σ L' c ∧ L' "lab" = v ∧ L' "g" = g ∧ c ≤ 50 := by
  set G := σ.Gs.getX g
  set C := σ.C.getX G.chk
  unfold labBefore at h
  simp only [getP, bind_pure_comp, getG, getC, beq_iff_eq, bind_map_left, EStateM.run_bind,
      EStateM.run_get, Proof.run_ite] at h
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "c") (e := .gF .chk "g") (v := G.chk)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  set L1 := upd L "c" G.chk
  have h1g : L1 "g" = g := by simp [L1, Machine.State.upd, hg]
  have h1c : L1 "c" = G.chk := by simp [L1, Machine.State.upd]
  by_cases hf : g = C.first
  · rw [ite_eq_left hf] at h
    obtain ⟨hs, hDb, hD0, rfl⟩ := before_inv h
    subst σ'
    refine ⟨rfl, ?_⟩
    have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "b") (e := .gF .lab "g") (v :=
      G.lab)
      (by simp [Exp.gF, Exp.ev, h1g, Fld.cap, Fld.get, GF.get, G, hgT])
    have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L1 "b" G.lab) (x := "D") (e := .prm
      .Dg) (v := σ.P.groupSpacing)
      (by simp [Exp.ev, PF.get])
    have b3 := beforeS_ok (κ := κ) (s := σ) (L := upd (upd L1 "b" G.lab) "D" σ.P.groupSpacing)
      (b := G.lab) (D := σ.P.groupSpacing)
      (by simp [Machine.State.upd]) (by simp [Machine.State.upd]) hDb hD0
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_ite_t (v := 1)
      (by simp only [Exp.ev, Exp.cF, h1c, Fld.cap, Fld.get, CF.get, Option.bind_some, hcT,
          ↓reduceIte, h1g, BinOp.eval, Option.some.injEq, ite_eq_left_iff, zero_ne_one,
          imp_false, Decidable.not_not]; exact hf.symm)
      one_ne_zero (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 b3))), by simp [Machine.State.upd]; rfl,
      by simp [Machine.State.upd, h1g], by simp [Exp.cost, Exp.gF, Exp.cF]⟩
  · rw [ite_eq_right hf] at h
    obtain ⟨hs, hab, rfl⟩ := between_inv h
    subst σ'
    refine ⟨rfl, ?_⟩
    have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "a") (e := .gF .lab (.gF .prev
      "g"))
      (v := (σ.Gs.getX G.prev).lab) (by simp [Exp.gF, Exp.ev, h1g, Fld.cap, Fld.get, GF.get, G,
        hgT, hpT])
    have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L1 "a" (σ.Gs.getX G.prev).lab) (x := "b")
      (e := .gF .lab "g") (v := G.lab) (by simp [Exp.gF, Exp.ev, Machine.State.upd, h1g,
        Fld.cap, Fld.get, GF.get, G, hgT])
    obtain ⟨c3, b3, hc3⟩ := betweenS_ok (κ := κ) (s := σ) (L := upd (upd L1 "a" (σ.Gs.getX
      G.prev).lab) "b" G.lab)
      (a := (σ.Gs.getX G.prev).lab) (b := G.lab) (by simp [Machine.State.upd]) (by simp
        [Machine.State.upd]) hab
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_ite_f
      (by simp only [Exp.ev, Exp.cF, h1c, Fld.cap, Fld.get, CF.get, Option.bind_some, hcT,
          ↓reduceIte, h1g, BinOp.eval, Option.some.injEq, ite_eq_right_iff,
          one_ne_zero, imp_false]; exact Ne.symm hf)
      (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 b3))), by simp [Machine.State.upd]; rfl,
      by simp [Machine.State.upd,
        h1g], by simp [Exp.cost, Exp.gF, Exp.cF] at hc3 ⊢; omega⟩

theorem labAfterS_agree (κ : Caps) (σ : Core) (L : Loc) {g : Nat} (hg : L "g" = g) (hgT : g <
  κ.tbl .G)
    (hcT : (σ.Gs.getX g).chk < κ.tbl .C) (hnT : (σ.Gs.getX g).next < κ.tbl .G) {v : Nat} {σ' : Core}
    (h : (labAfter g).run σ = .ok v σ') :
    σ' = σ ∧ ∃ L' c, evalF κ labAfterS σ L = .ok σ L' c ∧ L' "lab" = v ∧ L' "g" = g ∧ c ≤ 50 := by
  set G := σ.Gs.getX g
  set C := σ.C.getX G.chk
  unfold labAfter at h
  simp only [getP, bind_pure_comp, getG, getC, beq_iff_eq, bind_map_left, EStateM.run_bind,
      EStateM.run_get, Proof.run_ite] at h
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "c") (e := .gF .chk "g") (v := G.chk)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  set L1 := upd L "c" G.chk
  have h1g : L1 "g" = g := by simp [L1, Machine.State.upd, hg]
  have h1c : L1 "c" = G.chk := by simp [L1, Machine.State.upd]
  by_cases hf : g = C.last
  · rw [ite_eq_left hf] at h
    obtain ⟨hs, h1, h2, rfl⟩ := after_inv h
    subst σ'
    refine ⟨rfl, ?_⟩
    have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "a") (e := .gF .lab "g") (v :=
      G.lab)
      (by simp [Exp.gF, Exp.ev, h1g, Fld.cap, Fld.get, GF.get, G, hgT])
    have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L1 "a" G.lab) (x := "D") (e := .prm
      .Dg) (v := σ.P.groupSpacing)
      (by simp [Exp.ev, PF.get])
    have a3 := evalF_assign_ok (κ := κ) (s := σ) (L := upd (upd L1 "a" G.lab) "D"
      σ.P.groupSpacing) (x := "B") (e := .prm .Bg)
      (v := σ.P.groupBits) (by simp [Exp.ev, PF.get])
    obtain ⟨c4, b4, hc4⟩ := afterS_ok (κ := κ) (s := σ) (L := upd (upd (upd L1 "a" G.lab) "D"
      σ.P.groupSpacing) "B" σ.P.groupBits)
      (a := G.lab) (D := σ.P.groupSpacing) (B := σ.P.groupBits) (by simp [Machine.State.upd])
        (by simp [Machine.State.upd])
      (by simp [Machine.State.upd]) h1 h2
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_ite_t (v := 1)
      (by simp only [Exp.ev, Exp.cF, h1c, Fld.cap, Fld.get, CF.get, Option.bind_some, hcT,
          ↓reduceIte, h1g, BinOp.eval, Option.some.injEq, ite_eq_left_iff, zero_ne_one,
          imp_false, Decidable.not_not]; exact hf.symm)
      one_ne_zero (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 b4)))),
      (by simp [Machine.State.upd]; rfl),
      by simp [Machine.State.upd,
        h1g], by simp [Exp.cost, Exp.gF, Exp.cF] at hc4 ⊢; omega⟩
  · rw [ite_eq_right hf] at h
    obtain ⟨hs, hab, rfl⟩ := between_inv h
    subst σ'
    refine ⟨rfl, ?_⟩
    have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "a") (e := .gF .lab "g") (v :=
      G.lab)
      (by simp [Exp.gF, Exp.ev, h1g, Fld.cap, Fld.get, GF.get, G, hgT])
    have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L1 "a" G.lab) (x := "b") (e := .gF
      .lab (.gF .next "g"))
      (v := (σ.Gs.getX G.next).lab)
      (by simp [Exp.gF, Exp.ev, Machine.State.upd, h1g, Fld.cap, Fld.get, GF.get,
        G, hgT, hnT])
    obtain ⟨c3, b3, hc3⟩ := betweenS_ok (κ := κ) (s := σ) (L := upd (upd L1 "a" G.lab) "b"
      (σ.Gs.getX G.next).lab)
      (a := G.lab) (b := (σ.Gs.getX G.next).lab) (by simp [Machine.State.upd]) (by simp
        [Machine.State.upd]) hab
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_ite_f
      (by simp only [Exp.ev, Exp.cF, h1c, Fld.cap, Fld.get, CF.get, Option.bind_some, hcT,
          ↓reduceIte, h1g, BinOp.eval, Option.some.injEq, ite_eq_right_iff,
          one_ne_zero, imp_false]; exact Ne.symm hf)
      (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 b3))), by simp [Machine.State.upd]; rfl,
      by simp [Machine.State.upd,
        h1g], by simp [Exp.cost, Exp.gF, Exp.cF] at hc3 ⊢; omega⟩

/-! ### `newGroup` -/

/-- Clear a reused group's links and endpoints and set its containing chunk. -/
def rgA : Stm := cm{
  G[gn].next := 0; G[gn].prev := 0; G[gn].first := 0; G[gn].last := 0; G[gn].chk := c }
/-- Clear a reused group's label, size, split state, source and left sibling. -/
def rgB : Stm := cm{
  G[gn].lab := 0; G[gn].size := 0; G[gn].st := 0; G[gn].src := 0; G[gn].l := 0 }
/-- Clear a reused group's right sibling and mark it alive. -/
def rgC : Stm := cm{ G[gn].r := 0; G[gn].dead := 0 }
/-- Reset group `gn` to `{
  chk := c
}` (every field written). -/
def resetGS : Stm := rgA;; rgB;; rgC

/-- `gn := newGroup c`: reuse the last freed group, or push a new one (local `c`). -/
def newGroupS : Stm := cm{
  nf := len freeG[0]
  if nf = 0 then { gn := new G; G[gn].chk := c }
  else { gn := freeG[0][nf - 1].fst; pop freeG[0]; resetGS } }

/-- The record update corresponding to the first reused-group reset stage. -/
def rgF1 (c : Nat) (X : Group) : Group :=
  GF.set (GF.set (GF.set (GF.set (GF.set X 0 .next) 0 .prev) 0 .first) 0 .last) c .chk
/-- The record update corresponding to the second reused-group reset stage. -/
def rgF2 (X : Group) : Group := GF.set (GF.set (GF.set (GF.set (GF.set X 0 .lab) 0 .size) 0 .st)
  0 .src) 0 .l

theorem resetGS_ok {κ : Caps} {s : Core} {L : Loc} {j c : Nat} (hj : L "gn" = j) (hc : L "c" = c)
    (hjs : j < s.Gs.size) :
    ∃ n, evalF κ resetGS s L = .ok {
      s with
      Gs := s.Gs.modify j fun _ => {
        chk := c
      }
    } L n ∧ n ≤ 40 := by
  have hv : ∀ s' : Core, (Exp.var "gn").ev κ s' L = some j := fun _ => by simp [Exp.ev, hj]
  have b1 := five_wrG (κ := κ) (s := s) (L := L) (x := "gn") (j := j) (k1 := .next) (k2 :=
    .prev) (k3 := .first)
    (k4 := .last) (k5 := .chk) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := .var "c") (w1 :=
      0) (w2 := 0) (w3 := 0)
    (w4 := 0) (w5 := c) hj hjs  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => by simp [Exp.ev, hc]) rfl rfl rfl rfl rfl
  have b2 := five_wrG (κ := κ) (L := L) (x := "gn") (j := j) (k1 := .lab) (k2 := .size) (k3 := .st)
    (k4 := .src) (k5 := .l) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (w1 := 0) (w2 :=
      0) (w3 := 0)
    (w4 := 0) (w5 := 0) (s := {
      s with
      Gs := s.Gs.modify j (rgF1 c)
    })
    hj (by simp [hjs])  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ =>
      rfl)
    rfl rfl rfl rfl rfl
  set A := (s.Gs.modify j (rgF1 c)).modify j rgF2
  have w1 := evalF_wrG_ok (κ := κ) (s := {
    s with
    Gs := A
  }) (L := L) (k := .r) (e := (0 : Exp)) (w := 0) (hv _) rfl
    (by simp [A, hjs])  rfl
  have w2 := evalF_wrG_ok (κ := κ) (s := {
    s with
    Gs := A.modify j (GF.set · 0 .r)
  }) (L := L) (k := .dead)
    (e := (0 : Exp)) (w := 0) (hv _) rfl (by simp [A, hjs])  rfl
  have hfin : (A.modify j (GF.set · 0 .r)).modify j (GF.set · 0 .dead) = s.Gs.modify j fun _ => {
    chk := c
  } := by
    simp only [A, Array.modify_modify_same]
    congr 1
  rw [hfin] at w2
  exact ⟨_, evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 w1 w2)), by simp [Exp.cost]⟩

theorem newGroup_run (c : Nat) (σ : Core) : (newGroup c).run σ = (match σ.freeG with
    | i :: rest => .ok i {
      σ with
      freeG := rest
      Gs := σ.Gs.set! i {
        chk := c
      }
    }
    | [] => .ok σ.Gs.size {
      σ with
      Gs := σ.Gs.push {
        chk := c
      }
    }) := by
  unfold newGroup
  cases h : σ.freeG <;>
    simp [h, EStateM.run, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, ]

theorem newGroupS_agree (κ : Caps) (σ : Core) (L : Loc) {c : Nat} (hc : L "c" = c) {i : Nat} {σ'
  : Core}
    (h : (newGroup c).run σ = .ok i σ') (hG : σ.Gs.size < κ.tbl .G) (hfree : ∀ x ∈ σ.freeG, x <
      σ.Gs.size)
    (hF0 : 0 < κ.lrec .freeG) (hF : σ.freeG.length ≤ κ.lcap .freeG) :
    ∃ L' n, evalF κ newGroupS σ L = .ok σ' L' n ∧ L' "gn" = i ∧ L' "c" = c ∧ n ≤ 80 := by
  rw [newGroup_run] at h
  split at h
  case h_2 hf =>
    injection h with h1 h2
    subst h1 h2
    have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "nf") (e := .llen .freeG 0) (v := 0)
      (by simp [Exp.ev, hF0, LK.view, hf])
    set L1 := upd L "nf" 0
    have p1 := evalF_pushN_ok (κ := κ) (s := σ) (L := L1) (x := "gn")
    have hp : evalF κ (.push .G "gn") σ L1 = .ok {
      σ with
      Gs := σ.Gs.push default
    } (upd L1 "gn" σ.Gs.size) pushCost := by
      simp [evalF, Tbl.size, Tbl.push, hG]
    have w := evalF_wrG_ok (κ := κ) (s := {
      σ with
      Gs := σ.Gs.push default
    }) (L := upd L1 "gn" σ.Gs.size)
      (k := .chk) (i := .var "gn") (e := .var "c") (j := σ.Gs.size) (w := c) (by simp [Exp.ev,
        Machine.State.upd])
      (by simp [Exp.ev, Machine.State.upd, L1, hc]) (by simp)  rfl
    have hm : (σ.Gs.push default).modify σ.Gs.size (GF.set · c .chk) = σ.Gs.push {
      chk := c
    } := by
      rw [Array.modify_push_size]; rfl
    rw [hm] at w
    have t1 := evalF_seq_ok2 hp w
    have t2 : evalF κ (.push .G "gn";; .wgF .chk "gn" "c") σ L1 =
        .ok {
          σ with
          Gs := σ.Gs.push {
            chk := c
          }
        } (upd L1 "gn" σ.Gs.size) (pushCost + 3) := t1
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, L1,
      Machine.State.upd]) one_ne_zero t2), by simp [Machine.State.upd],
      by simp [Machine.State.upd, L1, hc], by simp [Exp.cost, pushCost]⟩
  case h_1 j rest hf =>
    injection h with h1 h2
    subst h1 h2
    have hjs : j < σ.Gs.size := hfree j (by simp [hf])
    have hv : LK.view σ 0 .freeG = (rest.reverse.map fun e => (e, 0)) ++ [(j, 0)] := by
      simp [LK.view, hf]
    have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "nf") (e := .llen .freeG 0) (v
      := rest.length + 1)
      (by simp [Exp.ev, hF0, hv])
    set L1 := upd L "nf" (rest.length + 1)
    have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "gn") (e := .lrd .freeG false 0
      ("nf" - 1)) (v := j)
      (by simp [Exp.ev, Machine.BinOp.eval, L1,
        Machine.State.upd, hF0, hv])
    set L2 := upd L1 "gn" j
    have hso : LK.set κ σ 0 (LK.view σ 0 .freeG).dropLast .freeG = some {
      σ with
      freeG := rest
    } := by
      rw [LK.set_ok (by simp [LK.recOk]) (by simp [LK.valid, hv]) (by
        simp only [hv, List.map_reverse, ne_eq, List.cons_ne_self, not_false_eq_true,
            List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil,
            List.length_reverse, List.length_map]
        rw [hf] at hF
        simp only [List.length_cons] at hF
        omega) hF0]
      simp [LK.put, hv, Function.comp_def]
    have hso' : LK.set κ σ 0 (List.map (fun e => (e, 0)) rest).reverse .freeG = some {
      σ with
      freeG := rest
    } := by
      rw [← hso, hv]; simp
    have e3 : evalF κ (.lshrink .freeG 0) σ L2 = .ok {
      σ with
      freeG := rest
    } L2 6 := by
      simp only [evalF, Exp.ev,  hv, Exp.cost]; simp [hso']
    obtain ⟨n4, e4, hn4⟩ := resetGS_ok (κ := κ) (s := {
      σ with
      freeG := rest
    }) (L := L2) (j := j) (c := c)
      (by simp [L2,
        Machine.State.upd]) (by simp [L2, L1, Machine.State.upd,
        hc]) hjs
    have hfin : ({
      {
        σ with
        freeG := rest
      } with
      Gs := σ.Gs.modify j fun _ => {
        chk := c
      }
    } : Core) =
        {
          σ with
          freeG := rest
          Gs := σ.Gs.set! j {
            chk := c
          }
        } := by
      rw [Array.set!_eq_modify]
    rw [hfin] at e4
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, L1,
      Machine.State.upd])
      (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 e4))), by simp [L2, Machine.State.upd],
      by simp [L2, L1, Machine.State.upd, hc], by simp [Exp.cost] at hn4 ⊢; omega⟩

/-! ### `startGroupSplit` -/

theorem newGroup_eff {c i : Nat} {σ σ' : Core} (h : (newGroup c).run σ = .ok i σ')
    (hfree : ∀ x ∈ σ.freeG, x < σ.Gs.size) :
    (∀ x, σ'.Gs.getX x = if x = i then {
      chk := c
    } else σ.Gs.getX x) ∧ σ.Gs.size ≤ σ'.Gs.size ∧
      σ'.Gs.size ≤ σ.Gs.size + 1 ∧ i < σ'.Gs.size ∧ σ'.C = σ.C ∧ σ'.P = σ.P ∧ σ'.freeG.length ≤
        σ.freeG.length ∧
      (∀ x ∈ σ'.freeG, x ∈ σ.freeG) := by
  rw [newGroup_run] at h
  split at h
  case h_1 j rest hf =>
    injection h with h1 h2; subst h1 h2
    have hj := hfree j (by simp [hf])
    refine ⟨fun x => ?_, (by simp), (by simp), (by
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      exact hj), rfl, rfl, (by simp [hf]), fun x hx => by simp [hf, hx]⟩
    simp only [Array.set!_eq_modify, getX_modify']
    by_cases e : x = j <;> simp [e, hj]
  case h_2 hf =>
    injection h with h1 h2; subst h1 h2
    refine ⟨fun x => ?_, by simp, by simp, by simp, rfl, rfl, le_refl _, fun x hx => hx⟩
    simp only [OrderMaintenance.Proof.Top.getX_push']

/-- Procedure selecting a group label before the given group. -/
def labBeforeP : Proc := { name := "labBefore", params := ["g"], rets := ["lab"], body :=
  labBeforeS }
/-- Procedure selecting a group label after the given group. -/
def labAfterP : Proc := { name := "labAfter", params := ["g"], rets := ["lab"], body := labAfterS }
/-- Procedure allocating or reusing a group in a chunk. -/
def newGroupP : Proc := { name := "newGroup", params := ["c"], rets := ["gn"], body := newGroupS }

/-- `startGroupSplit g`, guarded by Level F; every successful run satisfies the guard. -/
def startGroupSplitS : Stm := cm{
  labL ← labBeforeP(g); labR ← labAfterP(g)
  c := G[g].chk
  gl ← newGroupP(c); gr ← newGroupP(c)
  linkGroupPairS }

theorem startGroupSplitS_agree (κ : Caps) (σ : Core) (L : Loc) {g : Nat} (hg : L "g" = g)
    (hG2 : σ.Gs.size + 2 ≤ κ.tbl .G) (hC : σ.C.size ≤ κ.tbl .C)
    (hpG : (σ.Gs.getX g).prev < σ.Gs.size) (hnG : (σ.Gs.getX g).next < σ.Gs.size)
    (hcC : (σ.Gs.getX g).chk < σ.C.size) (hfree : ∀ x ∈ σ.freeG, x < σ.Gs.size)
    (hF0 : 0 < κ.lrec .freeG) (hF : σ.freeG.length ≤ κ.lcap .freeG) {σ' : Core}
    (h : (startGroupSplit g).run σ = .ok () σ') :
    ∃ L' n, evalF κ startGroupSplitS σ L = .ok σ' L' n ∧ n ≤ 600 := by
  unfold startGroupSplit at h
  simp only [OrderMaintenance.Proof.run_getG_bind, OrderMaintenance.Proof.run_get_bind,
    OrderMaintenance.Proof.run_require_bind] at h
  by_cases ha : (g != NIL && decide (g < σ.Gs.size) && (σ.Gs.getX g).alive) = true
  · rw [ite_eq_left ha] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at ha
    obtain ⟨labL, s2, h2, h⟩ := run_bind_ok h
    obtain ⟨labR, s3, h3, h⟩ := run_bind_ok h
    simp only [OrderMaintenance.Proof.run_newGroup_bind, OrderMaintenance.Proof.run_modify] at h
    have hgT : g < κ.tbl .G := by omega
    have hcT : (σ.Gs.getX g).chk < κ.tbl .C := by omega
    -- the labels
    obtain ⟨hs2, La, ca, ea, hla, -, hca⟩ := labBeforeS_agree κ σ (Machine.State.setLocs (fun _
      => 0) ["g"] [g])
      (g := g) (by simp [Machine.State.setLocs, Machine.State.upd]) hgT hcT (by omega) h2
    subst s2
    obtain ⟨hs3, Lb, cb, eb, hlb, -, hcb⟩ := labAfterS_agree κ σ (Machine.State.setLocs (fun _
      => 0) ["g"] [g])
      (g := g) (by simp [Machine.State.setLocs, Machine.State.upd]) hgT hcT (by omega) h3
    subst s3
    have e1 := evalF_call_ok (q := labBeforeP) (args := [.var "g"]) (ds := ["labL"]) (L := L)
      (by simp [evList, Exp.ev, hg]) ea
    set L1 := Machine.State.setLocs L ["labL"] (labBeforeP.rets.map La)
    have e2 := evalF_call_ok (q := labAfterP) (args := [.var "g"]) (ds := ["labR"]) (L := L1)
      (by simp [evList, Exp.ev, L1, labBeforeP, Machine.State.setLocs,
        Machine.State.upd, hg]) eb
    set L2 := Machine.State.setLocs L1 ["labR"] (labAfterP.rets.map Lb)
    set c := (σ.Gs.getX g).chk
    have e3 := evalF_assign_ok (κ := κ) (s := σ) (L := L2) (x := "c") (e := .gF .chk "g") (v := c)
      (by simp [Exp.gF, Exp.ev, L2, L1, labBeforeP, labAfterP,
        Machine.State.setLocs, Machine.State.upd, hg,
        Fld.cap, Fld.get, GF.get, hgT, c])
    set L3 := upd L2 "c" c
    -- the two new groups
    set σ1 := (OrderMaintenance.Proof.allocGroup σ c).2
    set gl := (OrderMaintenance.Proof.allocGroup σ c).1
    have hn1 : (newGroup c).run σ = .ok gl σ1 := OrderMaintenance.Proof.run_newGroup c σ
    obtain ⟨E1, E2, E3, E4, E5, E6, E7, E8⟩ := newGroup_eff hn1 hfree
    obtain ⟨Lg1, cg1, eg1, hgl1, -, hcg1⟩ := newGroupS_agree κ σ (Machine.State.setLocs (fun _
      => 0) ["c"] [c])
      (c := c) (by simp [Machine.State.setLocs, Machine.State.upd]) hn1 (by omega) hfree hF0 hF
    have e4 := evalF_call_ok (q := newGroupP) (args := [.var "c"]) (ds := ["gl"]) (L := L3)
      (by simp [evList, Exp.ev, L3, Machine.State.upd]) eg1
    set L4 := Machine.State.setLocs L3 ["gl"] (newGroupP.rets.map Lg1)
    set σ2 := (OrderMaintenance.Proof.allocGroup σ1 c).2
    set gr := (OrderMaintenance.Proof.allocGroup σ1 c).1
    have hn2 : (newGroup c).run σ1 = .ok gr σ2 := OrderMaintenance.Proof.run_newGroup c σ1
    have hfree1 : ∀ x ∈ σ1.freeG, x < σ1.Gs.size := fun x hx => by have := hfree x (E8 x hx); omega
    obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8⟩ := newGroup_eff hn2 hfree1
    obtain ⟨Lg2, cg2, eg2, hgr2, -, hcg2⟩ := newGroupS_agree κ σ1 (Machine.State.setLocs (fun _
      => 0) ["c"] [c])
      (c := c) (by simp [Machine.State.setLocs, Machine.State.upd]) hn2 (by omega) hfree1 hF0
        (by omega)
    have e5 := evalF_call_ok (q := newGroupP) (args := [.var "c"]) (ds := ["gr"]) (L := L4)
      (by simp [evList, Exp.ev, L4, L3, newGroupP, Machine.State.setLocs,
        Machine.State.upd]) eg2
    set L5 := Machine.State.setLocs L4 ["gr"] (newGroupP.rets.map Lg2)
    -- the link
    have hσ2g : σ2.Gs.getX g = if g = gr then {
      chk := c
    } else if g = gl then {
      chk := c
    } else σ.Gs.getX g := by
      rw [F1, E1]
    have hpG2 : (σ2.Gs.getX g).prev < σ2.Gs.size := by
      rw [hσ2g]; split_ifs <;> first | omega | (simp [NIL]; omega)
    have hnG2 : (σ2.Gs.getX g).next < σ2.Gs.size := by
      rw [hσ2g]; split_ifs <;> first | omega | (simp [NIL]; omega)
    have hcC2 : (σ2.Gs.getX g).chk < σ2.C.size := by
      rw [hσ2g, F5, E5]
      split_ifs <;> omega
    obtain ⟨L6, c6, e6, hc6⟩ := linkGroupPairS_agree κ σ2 L5 (g := g) (gl := gl) (gr := gr)
      (labL := labL)
      (labR := labR)
      (by simp [L5, L4, L3, L2, L1, newGroupP, labAfterP, labBeforeP,
        Machine.State.setLocs, Machine.State.upd, hg])
      (by simp [L5, L4, L3, newGroupP, Machine.State.setLocs,
        Machine.State.upd, hgl1])
      (by simp [L5, newGroupP, Machine.State.setLocs,
        Machine.State.upd, hgr2])
      (by simp [L5, L4, L3, L2, L1, newGroupP, labAfterP, labBeforeP,
        Machine.State.setLocs, Machine.State.upd, hla])
      (by simp [L5, L4, L3, L2, newGroupP, labAfterP, Machine.State.setLocs,
        Machine.State.upd, hlb])
      (by omega) (by omega) F4 hpG2 hnG2 hcC2 (by omega) (by rw [F5, E5]; exact hC)
    injection h with _ h
    rw [h] at e6
    refine ⟨L6, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
      (evalF_seq_ok2 e5 e6)))), ?_⟩
    simp only [Exp.cost, costList, Exp.gF, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hca hcb hcg1 hcg2 hc6 ⊢
    omega
  · rw [ite_eq_right ha] at h; simp [] at h

end OrderMaintenance.Impl
