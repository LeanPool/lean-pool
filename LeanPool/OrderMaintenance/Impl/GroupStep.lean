/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Group
public import LeanPool.OrderMaintenance.Proof.Cost.GMove


/-!
# M6: group split steps (`removeGroup`, `moveElem`, `groupSplitStep`, `driveGroup`)

The agreement lemmas cover the cases Level F's cost proof uses (`removeGroup_ok`, `MoveLOK`,
`MoveROK`), and reach the states it names (`removeState`, `moveLState`, `moveRState`).
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)
open OrderMaintenance.Proof.Top (getX_modify')

local notation "upd" => OrderMaintenance.Machine.State.upd

/-! ### `removeGroup` -/

def startGroupSplitP : Proc := { name := "startGroupSplit", params := ["g"], rets := [], body := startGroupSplitS }

/-- Quiet the overflow sibling `x` of `g` (flag `q`). -/
def quietE (x : Reg) : Exp := cme{ G[‹x›].st = 1 && G[‹x›].src = g }
def quietS (x q : Reg) : Stm :=
  cm{ ‹q› := 0; if ‹quietE x› then { G[‹x›].st := 0; G[‹x›].src := 0; ‹q› := 1 } }
/-- Split the quieted sibling `x` if it is full. -/
def splitIfE (x q : Reg) : Exp := cme{ ‹q› && P.G ≤ G[‹x›].size }
def splitIfS (x q : Reg) : Stm := cm{ if ‹splitIfE x q› then call startGroupSplitP(‹x›) }

/-- `removeGroup g`: unlink and free `g`, then its overflow siblings become quiet (and split if full). -/
def removeGroupS : Stm := cm{
  unlinkGroupS; gL := G[g].l; gR := G[g].r
  ‹quietS "gL" "qL"›; ‹quietS "gR" "qR"›; ‹splitIfS "gL" "qL"›; ‹splitIfS "gR" "qR"› }

theorem quietS_ok {κ : Caps} {S0 : Core} {L : Loc} {x q : Reg} {j p : Nat} (hx : L x = j) (hg : L "g" = p)
    (hq : q ≠ x) (hqg : q ≠ "g") (hst : (S0.Gs.getX j).st = .overflow) (hsrc : (S0.Gs.getX j).src = p) (hj : j < S0.Gs.size)
    (hjT : j < κ.tbl .G) :
    ∃ n, evalF κ (quietS x q) S0 L = .ok { S0 with Gs := S0.Gs.modify j OrderMaintenance.Proof.quietG } (upd (upd L q 0) q 1) n ∧
      n ≤ 30 := by
  set L1 := upd L q 0
  have h1x : L1 x = j := by simp [L1, OrderMaintenance.Machine.State.upd, Ne.symm hq, hx]
  have hv : ∀ s' : Core, (Exp.var x).ev κ s' L1 = some j := fun _ => by simp [Exp.ev, h1x]
  have w1 := evalF_wrG_ok (κ := κ) (s := S0) (L := L1) (k := .st) (e := (0 : Exp)) (w := 0) (hv _) rfl hj hjT rfl
  have w2 := evalF_wrG_ok (κ := κ) (s := { S0 with Gs := S0.Gs.modify j (GF.set · 0 .st) }) (L := L1) (k := .src)
    (e := (0 : Exp)) (w := 0) (hv _) rfl (by simp [hj]) hjT rfl
  have hfin : (S0.Gs.modify j (GF.set · 0 .st)).modify j (GF.set · 0 .src) = S0.Gs.modify j OrderMaintenance.Proof.quietG := by
    rw [Array.modify_modify_same]; rfl
  rw [hfin] at w2
  have a3 := evalF_assign_ok (κ := κ) (s := { S0 with Gs := S0.Gs.modify j OrderMaintenance.Proof.quietG }) (L := L1) (x := q)
    (e := (1 : Exp)) (v := 1) rfl
  have hc : (quietE x).ev κ S0 L1 = some 1 := by
    have hg1 : L1 "g" = p := by simp [L1, OrderMaintenance.Machine.State.upd, Ne.symm hqg, hg]
    simp [quietE, Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, h1x, hg1, hjT, Fld.cap,
      Fld.get, GF.get, hst, hsrc]
    rfl
  refine ⟨_, evalF_seq_ok2 (evalF_assign_ok (v := 0) rfl) (evalF_ite_t hc one_ne_zero
    (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w1) (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w2) a3))),
    by simp [Exp.cost, quietE, Exp.gF]⟩

theorem splitIfS_skip {κ : Caps} {S0 : Core} {L : Loc} {x q : Reg} {j : Nat} (hx : L x = j) (hq : L q = 1)
    (hsz : (S0.Gs.getX j).size < S0.P.G) (hjT : j < κ.tbl .G) :
    ∃ n, evalF κ (splitIfS x q) S0 L = .ok S0 L n ∧ n ≤ 15 := by
  have hc : (splitIfE x q).ev κ S0 L = some 0 := by
    have : ¬ S0.P.G ≤ (S0.Gs.getX j).size := by omega
    simp [splitIfE, Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, hx, hq, hjT, Fld.cap,
      Fld.get, GF.get, PF.get, this]
  exact ⟨_, evalF_ite_f hc evalF_skip, by simp [Exp.cost, splitIfE, Exp.gF]⟩

open OrderMaintenance.Proof in
theorem removeGroupS_agree (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p)
    (hp : LiveG s p) (he : gF s p = NIL) (hlr : gLl s p ≠ gRr s p)
    (hl : gSt s (gLl s p) = .overflow ∧ gSrc s (gLl s p) = p)
    (hr : gSt s (gRr s p) = .overflow ∧ gSrc s (gRr s p) = p)
    (hszl : gSz s (gLl s p) < s.P.G) (hszr : gSz s (gRr s p) < s.P.G)
    (hlS : gLl s p < s.Gs.size) (hrS : gRr s p < s.Gs.size)
    (hpG : gP s p < s.Gs.size) (hnG : gN s p < s.Gs.size) (hcC : gC s p < s.C.size)
    (hG : s.Gs.size ≤ κ.tbl .G) (hC : s.C.size ≤ κ.tbl .C)
    (hF : s.freeG.length + 1 ≤ κ.lcap .freeG) (hF0 : 0 < κ.lrec .freeG) :
    ∃ L' n, evalF κ removeGroupS s L = .ok (removeState s p) L' n ∧ n ≤ 300 := by
  obtain ⟨L1, c1, e1, h1g, hc1⟩ := unlinkGroupS_agree κ s L hg hp.2.1 hpG hnG hcC hG hC hF hF0
  set U := unlinkGroup s p
  set l := gLl s p
  set r := gRr s p
  have hpT : p < κ.tbl .G := by have := hp.2.1; omega
  have hUs : U.Gs.size = s.Gs.size := by
    simp only [U, unlinkGroup]; split_ifs <;> simp
  obtain ⟨u1, u2, -, -, -, uP⟩ := unlinkGroup_getX_lr s p p
  obtain ⟨-, -, l3, l4, l5, -⟩ := unlinkGroup_getX_lr s p l
  obtain ⟨-, -, r3, r4, r5, -⟩ := unlinkGroup_getX_lr s p r
  replace u1 : (U.Gs.getX p).l = (s.Gs.getX p).l := u1
  replace u2 : (U.Gs.getX p).r = (s.Gs.getX p).r := u2
  replace l3 : (U.Gs.getX l).st = (s.Gs.getX l).st := l3
  replace l4 : (U.Gs.getX l).src = (s.Gs.getX l).src := l4
  replace l5 : (U.Gs.getX l).size = (s.Gs.getX l).size := l5
  replace r3 : (U.Gs.getX r).st = (s.Gs.getX r).st := r3
  replace r4 : (U.Gs.getX r).src = (s.Gs.getX r).src := r4
  replace r5 : (U.Gs.getX r).size = (s.Gs.getX r).size := r5
  have a1 := evalF_assign_ok (κ := κ) (s := U) (L := L1) (x := "gL") (e := .gF .l "g") (v := l)
    (by simp [Exp.gF, Exp.ev, h1g, hpT, Fld.cap, Fld.get, GF.get, u1, l, gLl])
  have a2 := evalF_assign_ok (κ := κ) (s := U) (L := upd L1 "gL" l) (x := "gR") (e := .gF .r "g") (v := r)
    (by simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.State.upd, h1g, hpT, Fld.cap, Fld.get,
      GF.get, u2, r, gRr])
  set L2 := upd (upd L1 "gL" l) "gR" r
  obtain ⟨n3, e3, hn3⟩ := quietS_ok (κ := κ) (S0 := U) (L := L2) (x := "gL") (q := "qL") (j := l) (p := p)
    (by simp [L2,
      OrderMaintenance.Machine.State.upd]) (by simp [L2, OrderMaintenance.Machine.State.upd,
      h1g]) (by decide) (by decide)
    (by rw [l3]; exact hl.1) (by rw [l4]; exact hl.2) (by rw [hUs]; exact hlS) (by omega)
  set U1 := { U with Gs := U.Gs.modify l quietG }
  set L3 := upd (upd L2 "qL" 0) "qL" 1
  have hU1r : U1.Gs.getX r = U.Gs.getX r := by
    simp only [U1, getX_modify']; rw [ite_eq_right (fun h => hlr h.1.symm)]
  obtain ⟨n4, e4, hn4⟩ := quietS_ok (κ := κ) (S0 := U1) (L := L3) (x := "gR") (q := "qR") (j := r) (p := p)
    (by simp [L3, L2,
      OrderMaintenance.Machine.State.upd]) (by simp [L3, L2, OrderMaintenance.Machine.State.upd,
      h1g]) (by decide) (by decide)
    (by rw [hU1r,
      r3]; exact hr.1) (by rw [hU1r, r4]; exact hr.2) (by simp [U1, hUs]; exact hrS) (by omega)
  set U2 := { U1 with Gs := U1.Gs.modify r quietG }
  set L4 := upd (upd L3 "qR" 0) "qR" 1
  have hU2l : (U2.Gs.getX l).size = gSz s l := by
    simp only [U2, U1, getX_modify']; rw [ite_eq_right (fun h => hlr h.1)]
    split
    · simp [quietG, l5]
    · exact l5
  have hU2r : (U2.Gs.getX r).size = gSz s r := by
    simp only [U2, getX_modify']; split
    · simp [quietG, hU1r, r5]
    · rw [hU1r, r5]
  obtain ⟨n5, e5, hn5⟩ := splitIfS_skip (κ := κ) (S0 := U2) (L := L4) (x := "gL") (q := "qL") (j := l)
    (by simp [L4, L3, L2,
      OrderMaintenance.Machine.State.upd]) (by simp [L4, L3, OrderMaintenance.Machine.State.upd])
    (by rw [hU2l]; simp [U2, U1, U, uP]; exact hszl) (by omega)
  obtain ⟨n6, e6, hn6⟩ := splitIfS_skip (κ := κ) (S0 := U2) (L := L4) (x := "gR") (q := "qR") (j := r)
    (by simp [L4, L3, L2,
      OrderMaintenance.Machine.State.upd]) (by simp [L4, OrderMaintenance.Machine.State.upd])
    (by rw [hU2r]; simp [U2, U1, U, uP]; exact hszr) (by omega)
  refine ⟨L4, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
    (evalF_seq_ok2 e5 e6))))), ?_⟩
  simp only [Exp.cost, Exp.gF] at hc1 hn3 hn4 hn5 hn6 ⊢
  omega

/-! ### `moveElem` -/

/-- The centre label `1 <<< (elementBits - 1)`. -/
def centreE : Exp := cme{ 1 <<< (P.Be ∸ 1) }
def moveLabL : Stm := cm{
  if G[gl].first = 0 then lab := ‹centreE›
  else { a := E[G[gl].last].lab; D := P.De; B := P.Be; afterS } }
def moveLabR : Stm := cm{
  if G[gr].first = 0 then lab := ‹centreE›
  else { b := E[G[gr].first].lab; D := P.De; beforeS } }
def moveP (first : Bool) : Proc := { name := "move", params := ["g", "d", "e", "lab"], rets := [], body := moveS first }
/-- `d := moveElem g` (local `g`): move one element to the lighter sibling. -/
def moveElemS : Stm := cm{
  gl := G[g].l; gr := G[g].r
  if G[gl].size ≤ G[gr].size then {
    moveLabL; d := gl; e := G[g].first
    call ‹moveP true›(g, d, e, lab) }
  else {
    moveLabR; d := gr; e := G[g].last
    call ‹moveP false›(g, d, e, lab) } }

theorem centreE_ev {κ : Caps} {S0 : Core} {L : Loc} : centreE.ev κ S0 L = some (OrderMaintenance.Proof.cE S0.P) := by
  have hm := Exp.ev_monus κ S0 L (a := .prm .Be) (b := (1 : Exp)) (x := S0.P.elementBits) (y := 1) (by simp [Exp.ev, PF.get]) rfl
  simp only [centreE, Exp.ev, Option.bind_some]
  rw [hm]; simp [OrderMaintenance.Machine.BinOp.eval, OrderMaintenance.Proof.cE, Nat.shiftLeft_eq]

open OrderMaintenance.Proof in
theorem moveElemS_left (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p) (h : MoveLOK s p)
    (hlS : gLl s p < s.Gs.size) (hrS : gRr s p < s.Gs.size) (heE : gF s p < s.E.size)
    (hlast : gLs s (gLl s p) < κ.tbl .E) (hG : s.Gs.size ≤ κ.tbl .G) (hE : s.E.size ≤ κ.tbl .E) :
    ∃ L' n, evalF κ moveElemS s L =
      .ok (moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) L' n ∧ L' "d" = gLl s p ∧ L' "g" = p ∧ n ≤ 200 := by
  obtain ⟨⟨h0, hps, ha⟩, hne, hdir, hadj, hroom, hD, -⟩ := h
  set l := gLl s p
  set r := gRr s p
  have hpT : p < κ.tbl .G := by omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "gl") (e := .gF .l "g") (v := l)
    (by simp [Exp.gF, Exp.ev, hg, hpT, Fld.cap, Fld.get, GF.get, l, gLl])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "gl" l) (x := "gr") (e := .gF .r "g") (v := r)
    (by simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.State.upd, hg, hpT, Fld.cap, Fld.get,
      GF.get, r, gRr])
  set L2 := upd (upd L "gl" l) "gr" r
  have h2l : L2 "gl" = l := by simp [L2, OrderMaintenance.Machine.State.upd]
  have h2g : L2 "g" = p := by simp [L2, OrderMaintenance.Machine.State.upd, hg]
  have hc : (.gF .size "gl" ≤ₑ .gF .size "gr" : Exp).ev κ s L2 = some 1 := by
    simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2l, L2,
      OrderMaintenance.Machine.State.upd, Fld.cap, Fld.get, GF.get,
      show l < κ.tbl .G by omega, show r < κ.tbl .G by omega]
    exact hdir
  -- the label
  have b3 : ∃ L3 c3, evalF κ moveLabL s L2 = .ok s L3 c3 ∧ L3 "lab" = labMoveL s p ∧
      (∀ x, x ≠ "lab" → x ≠ "a" → x ≠ "D" → x ≠ "B" → x ≠ "v" → L3 x = L2 x) ∧ c3 ≤ 50 := by
    have hlT : l < κ.tbl .G := by omega
    have hcl : (.gF .first "gl" =ₑ 0 : Exp).ev κ s L2 = some (if gF s l = NIL then 1 else 0) := by
      simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2l, hlT, Fld.cap, Fld.get,
        GF.get, gF, NIL]
    by_cases he : gF s l = NIL
    · have aa := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "lab") (e := centreE) (v := cE s.P) centreE_ev
      rw [ite_eq_left he] at hcl
      have hlab : labMoveL s p = cE s.P := ite_eq_left he
      refine ⟨_, _, evalF_ite_t hcl one_ne_zero aa, by simp [OrderMaintenance.Machine.State.upd, hlab],
        fun x h1 _ _ _ _ => by simp [OrderMaintenance.Machine.State.upd, h1], by simp [Exp.cost, centreE, Exp.gF]⟩
    · have hr' := hroom he
      have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "a") (e := .eF .lab (.gF .last "gl"))
        (v := eL s (gLs s l)) (by simp [Exp.gF, Exp.eF, Exp.ev, h2l, hlT, hlast, Fld.cap, Fld.get, GF.get, EF.get])
      have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L2 "a" (eL s (gLs s l))) (x := "D") (e := .prm .De)
        (v := s.P.elementSpacing) (by simp [Exp.ev, PF.get])
      have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L2 "a" (eL s (gLs s l))) "D" s.P.elementSpacing) (x := "B")
        (e := .prm .Be) (v := s.P.elementBits) (by simp [Exp.ev, PF.get])
      obtain ⟨c4, b4, hc4⟩ := afterS_ok (κ := κ) (s := s)
        (L := upd (upd (upd L2 "a" (eL s (gLs s l))) "D" s.P.elementSpacing) "B" s.P.elementBits) (a := eL s (gLs s l)) (D := s.P.elementSpacing)
        (B := s.P.elementBits) (by simp [OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.upd])
        (by simp [OrderMaintenance.Machine.State.upd]) hr' (by omega)
      rw [ite_eq_right he] at hcl
      refine ⟨_, _, evalF_ite_f hcl (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 b4))),
        by have hlab : labMoveL s p = eL s (gLs s l) + s.P.elementSpacing := ite_eq_right he
           simp [OrderMaintenance.Machine.State.upd, hlab], fun x h1 h2 h3 h4 h5 => by
          simp [OrderMaintenance.Machine.State.upd, h1, h2, h3, h4,
            h5], by simp [Exp.cost, Exp.gF, Exp.eF] at hc4 ⊢; omega⟩
  obtain ⟨L3, c3, e3, h3lab, h3F, hc3⟩ := b3
  have h3l : L3 "gl" = l := by rw [h3F "gl" (by decide) (by decide) (by decide) (by decide) (by decide), h2l]
  have h3g : L3 "g" = p := by rw [h3F "g" (by decide) (by decide) (by decide) (by decide) (by decide), h2g]
  have a4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "d") (e := .var "gl") (v := l) (by simp [Exp.ev, h3l])
  have a5 := evalF_assign_ok (κ := κ) (s := s) (L := upd L3 "d" l) (x := "e") (e := .gF .first "g") (v := gF s p)
    (by simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.State.upd, h3g, hpT, Fld.cap, Fld.get,
      GF.get, gF])
  set L5 := upd (upd L3 "d" l) "e" (gF s p)
  obtain ⟨Lm, cm, em, hcm⟩ := moveS_agree κ s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["g", "d", "e", "lab"]
    [p, l, gF s p, labMoveL s p]) true (g := p) (d := l) (e := gF s p) (lab := labMoveL s p)
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd])
    hps hlS heE hG hE
  have e6 := evalF_call_ok (q := moveP true) (args := [.var "g", .var "d", .var "e", .var "lab"]) (ds := []) (L := L5)
    (by simp [evList, Exp.ev, L5, OrderMaintenance.Machine.State.upd, h3g, h3lab]) em
  refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_ite_t hc one_ne_zero (evalF_seq_ok2 e3
    (evalF_seq_ok2 a4 (evalF_seq_ok2 a5 e6))))), by simp [OrderMaintenance.Machine.State.setLocs, L5, OrderMaintenance.Machine.State.upd],
    by simp [OrderMaintenance.Machine.State.setLocs, L5, OrderMaintenance.Machine.State.upd,
      h3g], ?_⟩
  simp only [ite_true] at e6
  simp only [Exp.cost, costList, Exp.gF, List.map, List.sum_cons, List.sum_nil,
    List.length_nil] at hc3 hcm ⊢
  omega

open OrderMaintenance.Proof in
theorem moveElemS_right (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p) (h : MoveROK s p)
    (hlS : gLl s p < s.Gs.size) (hrS : gRr s p < s.Gs.size) (heE : gLs s p < s.E.size)
    (hfst : gF s (gRr s p) < κ.tbl .E) (hG : s.Gs.size ≤ κ.tbl .G) (hE : s.E.size ≤ κ.tbl .E) :
    ∃ L' n, evalF κ moveElemS s L =
      .ok (moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) L' n ∧ L' "d" = gRr s p ∧ L' "g" = p ∧ n ≤ 200 := by
  obtain ⟨⟨h0, hps, ha⟩, hne, hdir, hadj, hroom, hD, -⟩ := h
  set l := gLl s p
  set r := gRr s p
  have hpT : p < κ.tbl .G := by omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "gl") (e := .gF .l "g") (v := l)
    (by simp [Exp.gF, Exp.ev, hg, hpT, Fld.cap, Fld.get, GF.get, l, gLl])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "gl" l) (x := "gr") (e := .gF .r "g") (v := r)
    (by simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.State.upd, hg, hpT, Fld.cap, Fld.get,
      GF.get, r, gRr])
  set L2 := upd (upd L "gl" l) "gr" r
  have h2r : L2 "gr" = r := by simp [L2, OrderMaintenance.Machine.State.upd]
  have h2g : L2 "g" = p := by simp [L2, OrderMaintenance.Machine.State.upd, hg]
  have hc : (.gF .size "gl" ≤ₑ .gF .size "gr" : Exp).ev κ s L2 = some 0 := by
    have : ¬ (s.Gs.getX l).size ≤ (s.Gs.getX r).size := by simp only [gSz] at hdir; omega
    simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2r, L2,
      OrderMaintenance.Machine.State.upd, Fld.cap, Fld.get, GF.get,
      show l < κ.tbl .G by omega, show r < κ.tbl .G by omega, this]
  have b3 : ∃ L3 c3, evalF κ moveLabR s L2 = .ok s L3 c3 ∧ L3 "lab" = labMoveR s p ∧
      (∀ x, x ≠ "lab" → x ≠ "b" → x ≠ "D" → L3 x = L2 x) ∧ c3 ≤ 50 := by
    have hrT : r < κ.tbl .G := by omega
    have hcr : (.gF .first "gr" =ₑ 0 : Exp).ev κ s L2 = some (if gF s r = NIL then 1 else 0) := by
      simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2r, hrT, Fld.cap, Fld.get,
        GF.get, gF, NIL]
    by_cases he : gF s r = NIL
    · have aa := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "lab") (e := centreE) (v := cE s.P) centreE_ev
      rw [ite_eq_left he] at hcr
      have hlab : labMoveR s p = cE s.P := ite_eq_left he
      refine ⟨_, _, evalF_ite_t hcr one_ne_zero aa, by simp [OrderMaintenance.Machine.State.upd, hlab],
        fun x h1 _ _ => by simp [OrderMaintenance.Machine.State.upd, h1], by simp [Exp.cost, centreE, Exp.gF]⟩
    · have hr' := hroom he
      have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "b") (e := .eF .lab (.gF .first "gr"))
        (v := eL s (gF s r)) (by simp [Exp.gF, Exp.eF, Exp.ev, h2r, hrT, hfst, Fld.cap, Fld.get, GF.get, EF.get])
      have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L2 "b" (eL s (gF s r))) (x := "D") (e := .prm .De)
        (v := s.P.elementSpacing) (by simp [Exp.ev, PF.get])
      have b4 := beforeS_ok (κ := κ) (s := s) (L := upd (upd L2 "b" (eL s (gF s r))) "D"
        s.P.elementSpacing)
        (b := eL s (gF s r)) (D := s.P.elementSpacing) (by simp [OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.upd]) hr'
        (by omega)
      rw [ite_eq_right he] at hcr
      have hlab : labMoveR s p = eL s (gF s r) - s.P.elementSpacing := ite_eq_right he
      refine ⟨_, _, evalF_ite_f hcr (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 b4)),
        by simp [OrderMaintenance.Machine.State.upd,
          hlab], fun x h1 h2 h3 => by simp [OrderMaintenance.Machine.State.upd, h1, h2, h3],
        by simp [Exp.cost, Exp.gF, Exp.eF]⟩
  obtain ⟨L3, c3, e3, h3lab, h3F, hc3⟩ := b3
  have h3r : L3 "gr" = r := by rw [h3F "gr" (by decide) (by decide) (by decide), h2r]
  have h3g : L3 "g" = p := by rw [h3F "g" (by decide) (by decide) (by decide), h2g]
  have a4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "d") (e := .var "gr") (v := r) (by simp [Exp.ev, h3r])
  have a5 := evalF_assign_ok (κ := κ) (s := s) (L := upd L3 "d" r) (x := "e") (e := .gF .last "g") (v := gLs s p)
    (by simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.State.upd, h3g, hpT, Fld.cap, Fld.get,
      GF.get, gLs])
  set L5 := upd (upd L3 "d" r) "e" (gLs s p)
  obtain ⟨Lm, cm, em, hcm⟩ := moveS_agree κ s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["g", "d", "e", "lab"]
    [p, r, gLs s p, labMoveR s p]) false (g := p) (d := r) (e := gLs s p) (lab := labMoveR s p)
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd])
    hps hrS heE hG hE
  have e6 := evalF_call_ok (q := moveP false) (args := [.var "g", .var "d", .var "e", .var "lab"]) (ds := [])
    (L := L5) (by simp [evList, Exp.ev, L5, OrderMaintenance.Machine.State.upd, h3g, h3lab]) em
  refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_ite_f hc (evalF_seq_ok2 e3
    (evalF_seq_ok2 a4 (evalF_seq_ok2 a5 e6))))), by simp [OrderMaintenance.Machine.State.setLocs, L5, OrderMaintenance.Machine.State.upd],
    by simp [OrderMaintenance.Machine.State.setLocs, L5, OrderMaintenance.Machine.State.upd,
      h3g], ?_⟩
  simp only [Exp.cost, costList, Exp.gF, List.map, List.sum_cons, List.sum_nil,
    List.length_nil] at hc3 hcm ⊢
  omega

/-! ### `groupSplitStep` -/

def gssChkE : Exp := cme{ G[d].chk = G[g].chk }
/-- After a move: the sizes, and (unreachable under invariant F) a move across chunks. -/
def gssTail : Stm := cm{
  G[g].size := G[g].size ∸ 1; G[d].size := G[d].size + 1
  if ‹gssChkE› then skip else bug; ok := 1 }
/-- `ok := groupSplitStep g` (local `g`): one move of the split, or the removal of the empty group. -/
def groupSplitStepS : Stm := cm{
  gf := G[g].first
  if gf = 0 then { removeGroupS; ok := 0 } else { moveElemS; gssTail } }

theorem gssTail_ok {κ : Caps} {S1 : Core} {L : Loc} {p d : Nat} (hg : L "g" = p) (hd : L "d" = d)
    (hpS : p < S1.Gs.size) (hdS : d < S1.Gs.size) (hpT : p < κ.tbl .G) (hdT : d < κ.tbl .G)
    (hchk : (S1.Gs.getX d).chk = (S1.Gs.getX p).chk) :
    ∃ n, evalF κ gssTail S1 L = .ok (OrderMaintenance.Proof.sizeAdj S1 p d) (upd L "ok" 1) n ∧ n ≤ 60 := by
  have hm := Exp.ev_monus κ S1 L (a := .gF .size "g") (b := (1 : Exp)) (x := (S1.Gs.getX p).size) (y := 1)
    (by simp [Exp.gF, Exp.ev, hg, hpT, Fld.cap, Fld.get, GF.get]) rfl
  have w1 := evalF_wrG_ok (κ := κ) (s := S1) (L := L) (k := .size) (i := .var "g") (e := Exp.monus (.gF .size "g") 1)
    (j := p) (w := (S1.Gs.getX p).size - 1) (by simp [Exp.ev, hg]) hm hpS hpT rfl
  set A1 := S1.Gs.modify p (GF.set · ((S1.Gs.getX p).size - 1) .size)
  have hA1 : A1 = S1.Gs.modify p fun X => { X with size := X.size - 1 } := by
    apply Array.modify_congr_getX; rfl
  have w2 := evalF_wrG_ok (κ := κ) (s := { S1 with Gs := A1 }) (L := L) (k := .size) (i := .var "d")
    (e := .gF .size "d" + 1) (j := d) (w := (A1.getX d).size + 1) (by simp [Exp.ev, hd])
    (by simp [Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, hd, hdT, Fld.cap, Fld.get,
      GF.get]) (by simp [A1, hdS]) hdT rfl
  set A2 := A1.modify d (GF.set · ((A1.getX d).size + 1) .size)
  have hA2 : A2 = A1.modify d fun X => { X with size := X.size + 1 } := by
    apply Array.modify_congr_getX; rfl
  have hchk2 : ∀ z, (A2.getX z).chk = (S1.Gs.getX z).chk := by
    intro z; simp only [A2, A1, getX_modify']; split_ifs <;> rfl
  have hc : gssChkE.ev κ { S1 with Gs := A2 } L = some 1 := by
    simp [gssChkE, Exp.gF, Exp.ev, OrderMaintenance.Machine.BinOp.eval, hd, hg, hdT, hpT, Fld.cap,
      Fld.get, GF.get, hchk2, hchk]
  have hfin : ({ S1 with Gs := A2 } : Core) = OrderMaintenance.Proof.sizeAdj S1 p d := by
    simp only [OrderMaintenance.Proof.sizeAdj, hA2, hA1]
  rw [hfin] at hc
  refine ⟨_, evalF_seq_ok2 (by simp only [Stm.wgF]; exact w1) (evalF_seq_ok2 (by simp only [Stm.wgF]; rw [← hfin]; exact w2)
    (evalF_seq_ok2 (evalF_ite_t hc one_ne_zero evalF_skip) (evalF_assign_ok (v := 1) rfl))), ?_⟩
  simp [Exp.cost, gssChkE, Exp.gF]

open OrderMaintenance.Proof in
theorem groupSplitStepS_left (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p) (h : MoveLOK s p)
    (hlS : gLl s p < s.Gs.size) (hrS : gRr s p < s.Gs.size) (heE : gF s p < s.E.size)
    (hlast : gLs s (gLl s p) < κ.tbl .E) (hG : s.Gs.size ≤ κ.tbl .G) (hE : s.E.size ≤ κ.tbl .E) :
    ∃ L' n, evalF κ groupSplitStepS s L = .ok (moveLState s p) L' n ∧ L' "ok" = 1 ∧ L' "g" = p ∧ n ≤ 300 := by
  have hpT : p < κ.tbl .G := by have := h.live.2.1; omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "gf") (e := .gF .first "g") (v := gF s p)
    (by simp [Exp.gF, Exp.ev, hg, hpT, Fld.cap, Fld.get, GF.get, gF])
  obtain ⟨L2, c2, e2, h2d, h2g, hc2⟩ := moveElemS_left κ s (upd L "gf" (gF s p)) (p := p)
    (by simp [OrderMaintenance.Machine.State.upd, hg]) h hlS hrS heE hlast hG hE
  obtain ⟨n1, n2, n3, -, -, n6, -⟩ := moveFirstLeft_same (s := s) (g := p) (gl := gLl s p) (e := gF s p)
    (lab := labMoveL s p)
  obtain ⟨c3, e3, hc3⟩ := gssTail_ok (κ := κ) (S1 := moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) (L := L2)
    (p := p) (d := gLl s p) h2g h2d (by rw [n6]; exact h.live.2.1) (by rw [n6]; exact hlS) hpT (by omega)
    (by have := n3 (gLl s p); have := n3 p; have hc := h.chk; simp only [gC] at *; omega)
  have hc : ("gf" =ₑ 0 : Exp).ev κ s (upd L "gf" (gF s p)) = some 0 := by
    have := h.ne; simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, OrderMaintenance.Machine.State.upd]; simpa [NIL] using this
  exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f hc (evalF_seq_ok2 e2 e3)), by simp [OrderMaintenance.Machine.State.upd],
    by simp [OrderMaintenance.Machine.State.upd,
      h2g], by simp [Exp.cost, Exp.gF] at hc2 hc3 ⊢; omega⟩

open OrderMaintenance.Proof in
theorem groupSplitStepS_right (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p) (h : MoveROK s p)
    (hlS : gLl s p < s.Gs.size) (hrS : gRr s p < s.Gs.size) (heE : gLs s p < s.E.size)
    (hfst : gF s (gRr s p) < κ.tbl .E) (hG : s.Gs.size ≤ κ.tbl .G) (hE : s.E.size ≤ κ.tbl .E) :
    ∃ L' n, evalF κ groupSplitStepS s L = .ok (moveRState s p) L' n ∧ L' "ok" = 1 ∧ L' "g" = p ∧ n ≤ 300 := by
  have hpT : p < κ.tbl .G := by have := h.live.2.1; omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "gf") (e := .gF .first "g") (v := gF s p)
    (by simp [Exp.gF, Exp.ev, hg, hpT, Fld.cap, Fld.get, GF.get, gF])
  obtain ⟨L2, c2, e2, h2d, h2g, hc2⟩ := moveElemS_right κ s (upd L "gf" (gF s p)) (p := p)
    (by simp [OrderMaintenance.Machine.State.upd, hg]) h hlS hrS heE hfst hG hE
  obtain ⟨n1, n2, n3, -, -, n6, -⟩ := moveLastRight_same (s := s) (g := p) (gr := gRr s p) (e := gLs s p)
    (lab := labMoveR s p)
  obtain ⟨c3, e3, hc3⟩ := gssTail_ok (κ := κ) (S1 := moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) (L := L2)
    (p := p) (d := gRr s p) h2g h2d (by rw [n6]; exact h.live.2.1) (by rw [n6]; exact hrS) hpT (by omega)
    (by have := n3 (gRr s p); have := n3 p; have hc := h.chk; simp only [gC] at *; omega)
  have hc : ("gf" =ₑ 0 : Exp).ev κ s (upd L "gf" (gF s p)) = some 0 := by
    have := h.ne; simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, OrderMaintenance.Machine.State.upd]; simpa [NIL] using this
  exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f hc (evalF_seq_ok2 e2 e3)), by simp [OrderMaintenance.Machine.State.upd],
    by simp [OrderMaintenance.Machine.State.upd,
      h2g], by simp [Exp.cost, Exp.gF] at hc2 hc3 ⊢; omega⟩

open OrderMaintenance.Proof in
theorem groupSplitStepS_remove (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p)
    (hp : LiveG s p) (he : gF s p = NIL) (hlr : gLl s p ≠ gRr s p)
    (hl : gSt s (gLl s p) = .overflow ∧ gSrc s (gLl s p) = p)
    (hr : gSt s (gRr s p) = .overflow ∧ gSrc s (gRr s p) = p)
    (hszl : gSz s (gLl s p) < s.P.G) (hszr : gSz s (gRr s p) < s.P.G)
    (hlS : gLl s p < s.Gs.size) (hrS : gRr s p < s.Gs.size)
    (hpG : gP s p < s.Gs.size) (hnG : gN s p < s.Gs.size) (hcC : gC s p < s.C.size)
    (hG : s.Gs.size ≤ κ.tbl .G) (hC : s.C.size ≤ κ.tbl .C)
    (hF : s.freeG.length + 1 ≤ κ.lcap .freeG) (hF0 : 0 < κ.lrec .freeG) :
    ∃ L' n, evalF κ groupSplitStepS s L = .ok (removeState s p) L' n ∧ L' "ok" = 0 ∧ n ≤ 350 := by
  have hpT : p < κ.tbl .G := by have := hp.2.1; omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "gf") (e := .gF .first "g") (v := gF s p)
    (by simp [Exp.gF, Exp.ev, hg, hpT, Fld.cap, Fld.get, GF.get, gF])
  obtain ⟨L2, c2, e2, hc2⟩ := removeGroupS_agree κ s (upd L "gf" (gF s p)) (p := p)
    (by simp [OrderMaintenance.Machine.State.upd,
      hg]) hp he hlr hl hr hszl hszr hlS hrS hpG hnG hcC hG hC hF hF0
  have hc : ("gf" =ₑ 0 : Exp).ev κ s (upd L "gf" (gF s p)) = some 1 := by
    simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval,
      OrderMaintenance.Machine.State.upd]; simpa [NIL] using he
  exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t hc one_ne_zero (evalF_seq_ok2 e2 (evalF_assign_ok (v := 0) rfl))),
    by simp [OrderMaintenance.Machine.State.upd], by simp [Exp.cost, Exp.gF] at hc2 ⊢; omega⟩

/-! ### The drive loop -/

def groupSplitStepP : Proc := { name := "groupSplitStep", params := ["g"], rets := ["ok"], body := groupSplitStepS }
def driveBody : Stm := cm{ if dn = 0 then { ok ← groupSplitStepP(g); if ok = 0 then dn := 1 } }
/-- `driveGroupFrom g`: up to `groupBudget` split steps, stopping once `g` is removed. -/
def driveGroupFromS : Stm := cm{ dn := 0; for jj < P.KG do driveBody }

/-- A Level M split step that agrees with a Level F one (`b` = Level F's result). -/
def StepAgree (κ : Caps) (p : Nat) (t t' : Core) (b : Bool) : Prop :=
  ∀ L : Loc, L "g" = p → ∃ L' n, evalF κ groupSplitStepS t L = .ok t' L' n ∧ L' "ok" = b2n b ∧ n ≤ 350

/-- The body of Level F's drive loop. -/
def driveF (p : Nat) : Nat → Option Unit × Unit → CM (ForInStep (Option Unit × Unit)) :=
  fun _ _ => do
    let b ← groupSplitStep p
    if (!b) = true then pure (ForInStep.done (some (), ())) else pure (ForInStep.yield (none, ()))

theorem driveF_run_true {p j : Nat} {t t' : Core} {a : Option Unit × Unit} (h : (groupSplitStep p).run t = .ok true t') :
    (driveF p j a).run t = .ok (.yield (none, ())) t' := by
  simp only [driveF, OrderMaintenance.Proof.run_bind, h]; rfl

theorem driveF_run_false {p j : Nat} {t t' : Core} {a : Option Unit × Unit} (h : (groupSplitStep p).run t = .ok false t') :
    (driveF p j a).run t = .ok (.done (some (), ())) t' := by
  simp only [driveF, OrderMaintenance.Proof.run_bind, h]; rfl

theorem driveGroupFromS_agree (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p)
    (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.groupBudget → ∃ b t', (groupSplitStep p).run t = .ok b t' ∧
      (b = true → I (j + 1) t') ∧ StepAgree κ p t t' b) :
    ∃ t' L' n, (driveGroupFrom p).run s = .ok () t' ∧ evalF κ driveGroupFromS s L = .ok t' L' n ∧
      n ≤ 5 + s.P.groupBudget * 401 := by
  set K := s.P.groupBudget
  set R := fun (l : List Nat) (t : Core) => (forIn l ((none : Option Unit), ()) (driveF p)).run t
  -- Level F's loop ends
  have hF : ∀ (n j : Nat) (t : Core), I j t → j + n = K →
      ∃ c tF, R ((List.range K).drop j) t = .ok c tF := by
    intro n; induction n with
    | zero =>
      intro j t _ hj; refine ⟨(none, ()), t, ?_⟩
      simp only [R, show j = K by omega]; rw [List.drop_of_length_le (by simp)]; rfl
    | succ n ih =>
      intro j t hI hj
      have hjK : j < K := by omega
      rw [List.drop_eq_getElem_cons (by simpa using hjK), List.getElem_range]
      obtain ⟨b, t', hr, hI', -⟩ := hstep j t hI hjK
      cases b
      · exact ⟨_, _, by simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, driveF_run_false hr]; rfl⟩
      · obtain ⟨c, tF, h⟩ := ih (j + 1) t' (hI' rfl) (by omega)
        exact ⟨c, tF, by simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, driveF_run_true hr]; exact h⟩
  obtain ⟨c0, tF, hR0⟩ := hF K 0 s h0 (by omega)
  simp only [List.drop_zero] at hR0
  -- Level F's result
  have hFrun : (driveGroupFrom p).run s = .ok () tF := by
    unfold driveGroupFrom
    rw [OrderMaintenance.Proof.run_getP_bind, OrderMaintenance.Proof.run_bind]
    have hR0' : (forIn (List.range s.P.groupBudget) ((none : Option Unit), ()) (fun (_ : Nat) (_ : Option Unit × Unit) => do
        let b ← groupSplitStep p
        if (!b) = true then pure (ForInStep.done (some (), ())) else pure (ForInStep.yield (none, ())))).run s =
        .ok c0 tF := hR0
    rw [hR0']
    dsimp only
    split <;> rfl
  -- Level M's loop
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "dn") (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨S', L', c, he, hc, -, hI⟩ := evalF_loop (κ := κ) (x := "jj") (n := .prm .KG) (b := driveBody) (s := s)
    (L := upd L "dn" 0) (N := K) (by simp [Exp.ev, PF.get, K])
    (fun j S L' => L' "g" = p ∧ ((L' "dn" = 0 ∧ I j S ∧ ∃ c, R ((List.range K).drop j) S = .ok c tF) ∨
      (L' "dn" = 1 ∧ S = tF))) 400
    ⟨by simp [OrderMaintenance.Machine.State.upd,
      hg], Or.inl ⟨by simp [OrderMaintenance.Machine.State.upd], h0, c0, by simpa using hR0⟩⟩
    (by
      intro j hj S L1 ⟨h1g, hcase⟩
      set L2 := upd L1 "jj" j
      have h2g : L2 "g" = p := by simp [L2, OrderMaintenance.Machine.State.upd, h1g]
      rcases hcase with ⟨hdn, hIj, c1, hR⟩ | ⟨hdn, hSF⟩
      · have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 1 := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L2,
          OrderMaintenance.Machine.State.upd, hdn]
        obtain ⟨b, t', hr, hI', hSA⟩ := hstep j S hIj hj
        obtain ⟨Lg, ng, eg, hok, hng⟩ := hSA (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["g"] [p])
          (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
        have ec := evalF_call_ok (q := groupSplitStepP) (args := [.var "g"]) (ds := ["ok"]) (L := L2)
          (by simp [evList, Exp.ev, h2g]) eg
        set L3 := OrderMaintenance.Machine.State.setLocs L2 ["ok"] (groupSplitStepP.rets.map Lg)
        have h3ok : L3 "ok" = b2n b := by simp [L3, groupSplitStepP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hok]
        have h3g : L3 "g" = p := by simp [L3, groupSplitStepP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, h2g]
        have h3dn : L3 "dn" = 0 := by simp [L3, L2, groupSplitStepP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hdn]
        rw [List.drop_eq_getElem_cons (by simpa using hj), List.getElem_range] at hR
        cases b
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, driveF_run_false hr] at hR
          injection hR with _ hT; subst hT
          have e4 := evalF_assign_ok (κ := κ) (s := t') (L := L3) (x := "dn") (e := (1 : Exp)) (v := 1) rfl
          refine ⟨t', _, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 ec (evalF_ite_t (v := 1)
            (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, h3ok, b2n]) one_ne_zero e4)), ?_,
            by simp [OrderMaintenance.Machine.State.upd,
              h3g], Or.inr ⟨by simp [OrderMaintenance.Machine.State.upd], rfl⟩⟩
          simp [Exp.cost, costList] at hng ⊢; omega
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, driveF_run_true hr] at hR
          refine ⟨t', _, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 ec (evalF_ite_f
            (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, h3ok,
              b2n]) evalF_skip)), ?_, h3g,
            Or.inl ⟨h3dn, hI' rfl, c1, hR⟩⟩
          simp [Exp.cost, costList] at hng ⊢; omega
      · subst hSF
        have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 0 := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L2,
          OrderMaintenance.Machine.State.upd, hdn]
        exact ⟨S, L2, _, evalF_ite_f hc0 evalF_skip, by simp [Exp.cost], h2g,
          Or.inr ⟨by simp [L2, OrderMaintenance.Machine.State.upd, hdn], rfl⟩⟩)
  have hS' : S' = tF := by
    rcases hI with ⟨hdn, hIK, c2, hR⟩ | ⟨hdn, h⟩
    · rw [List.drop_of_length_le (by simp)] at hR
      simp only [R] at hR
      injection hR
    · exact h
  subst hS'
  refine ⟨S', L', _, hFrun, evalF_seq_ok2 a1 he, ?_⟩
  simp only [Exp.cost] at hc ⊢; omega

/-! ### `driveGroup` -/

def driveP : Proc := { name := "driveGroupFrom", params := ["g"], rets := [], body := driveGroupFromS }
/-- `driveGroup g`: drive the split `g` belongs to, if any (local `g`). -/
def driveGroupS : Stm := cm{
  st := G[g].st
  if st = 2 then call driveP(g)
  else if st = 1 then call driveP(G[g].src) }

/-- The drive of the split rooted at `q` agrees at Level M, ending in `t'`. -/
def DriveAgree (κ : Caps) (q : Nat) (s t' : Core) : Prop :=
  (driveGroupFrom q).run s = .ok () t' ∧
    ∀ L : Loc, L "g" = q → ∃ L' n, evalF κ driveGroupFromS s L = .ok t' L' n ∧ n ≤ 5 +
      s.P.groupBudget * 401

theorem driveGroupFromS_agree' (κ : Caps) (s : Core) {p : Nat} (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.groupBudget → ∃ b t', (groupSplitStep p).run t = .ok b t' ∧
      (b = true → I (j + 1) t') ∧ StepAgree κ p t t' b) : ∃ t', DriveAgree κ p s t' := by
  obtain ⟨t', L1, n1, hF, -, -⟩ := driveGroupFromS_agree κ s (fun _ => p) (p := p) rfl I h0 hstep
  refine ⟨t', hF, fun L hL => ?_⟩
  obtain ⟨t'', L', n, hF', he, hn⟩ := driveGroupFromS_agree κ s L (p := p) hL I h0 hstep
  rw [hF] at hF'; injection hF' with _ h; subst h; exact ⟨L', n, he, hn⟩

theorem driveGroup_split {s : Core} {g : Nat} (h : (s.Gs.getX g).st = .splitting) :
    (driveGroup g).run s = (driveGroupFrom g).run s := by
  unfold driveGroup; rw [OrderMaintenance.Proof.run_getG_bind, h]

theorem driveGroup_ovf {s : Core} {g : Nat} (h : (s.Gs.getX g).st = .overflow) :
    (driveGroup g).run s = (driveGroupFrom (s.Gs.getX g).src).run s := by
  unfold driveGroup; rw [OrderMaintenance.Proof.run_getG_bind, h]

theorem driveGroup_quiet {s : Core} {g : Nat} (h : (s.Gs.getX g).st = .quiet) : (driveGroup g).run s = .ok () s := by
  unfold driveGroup; rw [OrderMaintenance.Proof.run_getG_bind, h]; rfl

theorem driveGroup_dead {s : Core} {g : Nat} (h : (s.Gs.getX g).st = .dead) : (driveGroup g).run s = .ok () s := by
  unfold driveGroup; rw [OrderMaintenance.Proof.run_getG_bind, h]; rfl

theorem driveGroupS_agree (κ : Caps) (s : Core) (L : Loc) {g : Nat} (hg : L "g" = g) (hgT : g < κ.tbl .G)
    {σ' : Core} (h : (driveGroup g).run s = .ok () σ')
    (hA : ∀ q, ((s.Gs.getX g).st = .splitting ∧ q = g ∨ (s.Gs.getX g).st = .overflow ∧ q = (s.Gs.getX g).src) →
      DriveAgree κ q s σ') :
    ∃ L' n, evalF κ driveGroupS s L = .ok σ' L' n ∧ n ≤ 30 + s.P.groupBudget * 401 := by
  set G := s.Gs.getX g
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "st") (e := .gF .st "g") (v := G.st.toN)
    (by simp [Exp.gF, Exp.ev, hg, hgT, Fld.cap, Fld.get, GF.get, G])
  set L1 := upd L "st" G.st.toN
  have h1g : L1 "g" = g := by simp [L1, OrderMaintenance.Machine.State.upd, hg]
  have c1 : ("st" =ₑ 2 : Exp).ev κ s L1 = some (if G.st.toN = 2 then 1 else 0) := by
    simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L1, OrderMaintenance.Machine.State.upd]
  have c2 : ("st" =ₑ 1 : Exp).ev κ s L1 = some (if G.st.toN = 1 then 1 else 0) := by
    simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L1, OrderMaintenance.Machine.State.upd]
  cases hst : G.st with
  | splitting =>
    rw [hst] at c1; simp only [St.toN, ite_true] at c1
    obtain ⟨-, hM⟩ := hA g (Or.inl ⟨hst, rfl⟩)
    obtain ⟨Ld, nd, ed, hnd⟩ := hM (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["g"] [g])
      (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    have ec := evalF_call_ok (q := driveP) (args := [.var "g"]) (ds := []) (L := L1) (by simp [evList, Exp.ev, h1g]) ed
    exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t c1 one_ne_zero ec), by simp [Exp.cost, costList, Exp.gF] at hnd ⊢; omega⟩
  | overflow =>
    rw [hst] at c1 c2; simp only [St.toN, ite_true] at c1 c2
    obtain ⟨-, hM⟩ := hA G.src (Or.inr ⟨hst, rfl⟩)
    obtain ⟨Ld, nd, ed, hnd⟩ := hM (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["g"] [G.src])
      (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    have ec := evalF_call_ok (q := driveP) (args := [.gF .src "g"]) (ds := []) (L := L1)
      (by simp [evList, Exp.gF, Exp.ev, h1g, hgT, Fld.cap, Fld.get, GF.get, G]) ed
    exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f (by simpa using c1) (evalF_ite_t c2 one_ne_zero ec)),
      by simp [Exp.cost, costList, Exp.gF] at hnd ⊢; omega⟩
  | quiet =>
    rw [driveGroup_quiet hst] at h
    injection h with _ hs; subst hs
    rw [hst] at c1 c2; simp only [St.toN] at c1 c2
    have i2 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 1 : Exp)) (t := driveP.call [.gF .src "g"] []) (by simpa using c2)
      evalF_skip
    have i1 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 2 : Exp)) (t := driveP.call [.var "g"] []) (by simpa using c1) i2
    exact ⟨_, _, evalF_seq_ok2 a1 i1, by simp [Exp.cost, Exp.gF]; omega⟩
  | dead =>
    rw [driveGroup_dead hst] at h
    injection h with _ hs; subst hs
    rw [hst] at c1 c2; simp only [St.toN] at c1 c2
    have i2 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 1 : Exp)) (t := driveP.call [.gF .src "g"] []) (by simpa using c2)
      evalF_skip
    have i1 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 2 : Exp)) (t := driveP.call [.var "g"] []) (by simpa using c1) i2
    exact ⟨_, _, evalF_seq_ok2 a1 i1, by simp [Exp.cost, Exp.gF]; omega⟩

end OrderMaintenance.Impl
