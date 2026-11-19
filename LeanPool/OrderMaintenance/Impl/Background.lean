/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Reservation


/-!
# M6: background work at Level M (`chunkSize`, `background`)

`background y` after inserting element `y`: the chunk of `y` grows by one, a full quiet group
starts its split, the group and chunk splits of `y` are driven, and the reservation runs. Each
part is a procedure, so that its locals stay apart; the agreement is stated along Level F's run,
given as a trace of the parts.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => Machine.State.upd

/-! ### `chunkSize c true` -/

/-- Procedure incrementing a chunk size and updating its quiet-queue membership. -/
def csP : Proc where
  name := "chunkSize"
  params := ["c"]
  rets := []
  body := cm{
    old := C[c].size; new := old + 1; C[c].size := new
    if C[c].st = 0 then call pqAdjustP(c, old, new) }

theorem csP_agree {κ : Caps} {s : Core} {L : Loc} {c : Nat} (hc : L "c" = c) (hcs : c < s.C.size)
    (hcT : c < κ.tbl .C) (hq : PQCaps κ s) (hcC : c < Ccap κ) (hnB : (s.C.getX c).size + 1 < Bcap κ)
    {s' : Core} (h : (chunkSize c true).run s = .ok () s') :
    (∃ L' n, evalF κ csP.body s L = .ok s' L' n ∧ n ≤ 750) ∧ PQCaps κ s' := by
  set C := s.C.getX c
  unfold chunkSize at h
  simp only [OrderMaintenance.Proof.run_getC_bind, run_modC_bind] at h
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "old") (e := .cF .size "c") (v :=
    C.size)
    (by simp [Exp.cF, Exp.ev, hc, hcT, Fld.cap, Fld.get, CF.get, C])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "old" C.size) (x := "new") (e :=
    "old" + 1) (v := C.size + 1)
    (by
      simp [Exp.ev, Machine.State.upd, Machine.BinOp.eval])
  set L2 := upd (upd L "old" C.size) "new" (C.size + 1)
  have h2c : L2 "c" = c := by simp [L2, Machine.State.upd, hc]
  have w3 := evalF_wrC_ok (κ := κ) (s := s) (L := L2) (k := .size) (i := .var "c") (e := .var
    "new") (j := c)
    (w := C.size + 1) (by simp [Exp.ev, h2c]) (by simp [Exp.ev, L2, Machine.State.upd]) hcs  rfl
  set s1 : Core := {
    s with
    C := s.C.modify c fun C' => {
      C' with
      size := C.size + 1
    }
  }
  have hs1 : ({
    s with
    C := s.C.modify c (CF.set · (C.size + 1) .size)
  } : Core) = s1 := rfl
  rw [hs1] at w3
  have hq1 : PQCaps κ s1 := { hq with }
  have hst : (s1.C.getX c).st = C.st := by
    simp only [s1, getX_modify', hcs, and_self, ite_true]; rfl
  by_cases hQ : C.st = .quiet
  · have hQ' : (s.C.getX c).st = .quiet := hQ
    rw [ite_eq_left (by simp [hQ'])] at h
    have h' : (pqAdjust c C.size (C.size + 1)).run s1 = .ok () s' := h
    obtain ⟨⟨La, na, ea, hna⟩, hq'⟩ := pqAdjust_agree κ s1
      (Machine.State.setLocs (fun _ => 0) ["c", "old", "new"] [c, C.size, C.size + 1]) (c := c)
        (old := C.size)
      (by
        simp [Machine.State.setLocs, Machine.State.upd])
      (by
        simp [Machine.State.setLocs, Machine.State.upd])
      (by
        simp [Machine.State.setLocs, Machine.State.upd]) hq1 hcC hnB h'
    have e4 := evalF_call_ok (q := pqAdjustP) (args := ["c", "old", "new"]) (ds := []) (L := L2)
      (by
        simp [evList, Exp.ev,  L2, Machine.State.upd, hc]) ea
    refine ⟨⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 (by
      simp only [Stm.wcF]
      exact w3)
      (evalF_ite_t (v := 1) (by
        simp [Exp.cF, Exp.ev, h2c, hcT, Fld.cap, Fld.get, CF.get, hst, hQ, St.toN,
          Machine.BinOp.eval]) one_ne_zero e4))), ?_⟩, hq'⟩
    simp [Exp.cost, Exp.cF, costList] at hna ⊢; omega
  · have hQ' : ¬ (s.C.getX c).st = .quiet := hQ
    rw [ite_eq_right (by simpa using hQ')] at h
    injection h with _ h; subst h
    have hst0 : (s1.C.getX c).st.toN ≠ 0 := by rw [hst]; cases hC : C.st <;> simp_all [St.toN]
    have hc0 : (Exp.cF .st "c" =ₑ 0 : Exp).ev κ s1 L2 = some 0 := by
      simp only [Exp.cF, Exp.ev, h2c, Option.bind_some, Fld.cap, hcT, ite_true, Fld.get, CF.get]
      simp [Machine.BinOp.eval, hst0]
    refine ⟨⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 (by
      simp only [Stm.wcF]
      exact w3)
      (evalF_ite_f hc0 evalF_skip))), ?_⟩, hq1⟩
    simp [Exp.cost, Exp.cF]

/-! ### `background y` -/

theorem run_bind_of_ok {α β : Type} {m : CM α} {f : α → CM β} {s s' : Core} {a : α} (h : m.run s
  = .ok a s') :
    (m >>= f).run s = (f a).run s' := by
  rw [OrderMaintenance.Proof.run_bind, h]

/-- Procedure starting the incremental split of a full group. -/
def sgsP : Proc := {
  name := "startGroupSplit"
  params := ["g"]
  rets := []
  body := startGroupSplitS
}
/-- Procedure advancing the split associated with a group. -/
def dgP : Proc := {
  name := "driveGroup"
  params := ["g"]
  rets := []
  body := driveGroupS
}
/-- Procedure advancing the split associated with a chunk. -/
def dcP : Proc := {
  name := "driveChunk"
  params := ["x"]
  rets := []
  body := driveChunkS
}
/-- Procedure spending the scheduled reservation budget on the priority queue. -/
def resP : Proc := {
  name := "reservation"
  params := []
  rets := []
  body := reservationS
}

/-- `startGroupSplit g` when group `g` is quiet and full. -/
def bgSplitC : Exp := cme{ G[g].st = 0 && P.G ≤ G[g].size }

/-- `background y` (local `y`). -/
def backgroundS : Stm := cm{
  g := E[y].grp; c := G[g].chk; call csP(c)
  g := E[y].grp; if ‹bgSplitC› then call sgsP(g)
  g := E[y].grp; call dgP(g)
  g := E[y].grp; x := G[g].chk; call dcP(x)
  call resP() }

/-- The group of `y` and its chunk in state `t`. -/
abbrev gOf (t : Core) (y : Nat) : Nat := (t.E.getX y).grp
/-- The chunk containing the element with the given index. -/
abbrev cOf (t : Core) (y : Nat) : Nat := (t.Gs.getX (gOf t y)).chk

/-- `background`'s test for starting the split of `y`'s group. -/
def bgSplit (t : Core) (y : Nat) (P : Params) : Bool :=
  (t.Gs.getX (gOf t y)).st == .quiet && decide ((t.Gs.getX (gOf t y)).size ≥ P.G)

theorem backgroundS_agree {κ : Caps} {L : Loc} {y : Nat} {s0 s1 s2 s3 s4 s5 : Core} {D1 D2 D3 D4
  D5 : Nat}
    (hy : L "y" = y)
    -- Level F, part by part
    (h1 : (chunkSize (cOf s0 y) true).run s0 = .ok () s1)
    (h2 : (if bgSplit s1 y s0.P then startGroupSplit (gOf s1 y) else pure ()).run s1 = .ok () s2)
    (h3 : (driveGroup (gOf s2 y)).run s2 = .ok () s3)
    (h4 : (driveChunk (cOf s3 y)).run s3 = .ok () s4)
    (h5 : (reservation s0.P.reservationBudget).run s4 = .ok () s5)
    -- Level M, part by part
    (m1 : ∃ L' n, evalF κ csP.body s0 (Machine.State.setLocs (fun _ => 0) ["c"] [cOf s0 y]) =
      .ok s1 L' n ∧ n ≤ D1)
    (m2 : bgSplit s1 y s0.P = true →
      ∃ L' n, evalF κ sgsP.body s1 (Machine.State.setLocs (fun _ => 0) ["g"] [gOf s1 y]) = .ok
        s2 L' n ∧ n ≤ D2)
    (m3 : ∃ L' n, evalF κ dgP.body s2 (Machine.State.setLocs (fun _ => 0) ["g"] [gOf s2 y]) =
      .ok s3 L' n ∧ n ≤ D3)
    (m4 : ∃ L' n, evalF κ dcP.body s3 (Machine.State.setLocs (fun _ => 0) ["x"] [cOf s3 y]) =
      .ok s4 L' n ∧ n ≤ D4)
    (m5 : ∃ L' n, evalF κ resP.body s4 (Machine.State.setLocs (fun _ => 0) [] []) = .ok s5 L' n
      ∧ n ≤ D5)
    -- capacities and parameters
    (hP1 : s1.P = s0.P) (hyE : y < κ.tbl .E)
    (hg0 : gOf s0 y < κ.tbl .G) (hg1 : gOf s1 y < κ.tbl .G) (hg3 :
      gOf s3 y < κ.tbl .G) :
    (background y).run s0 = .ok () s5 ∧
      ∃ L' n, evalF κ backgroundS s0 L = .ok s5 L' n ∧ n ≤ D1 + D2 + D3 + D4 + D5 + 100 := by
  refine ⟨?_, ?_⟩
  · unfold background
    simp only [OrderMaintenance.Proof.run_getP_bind, OrderMaintenance.Proof.run_getE_bind,
      OrderMaintenance.Proof.run_getG_bind]
    rw [OrderMaintenance.Proof.run_bind, h1]; dsimp only
    simp only [OrderMaintenance.Proof.run_getE_bind, OrderMaintenance.Proof.run_getG_bind]
    have hrest : ∀ t, (driveGroup (gOf t y)).run t = .ok () s3 → (do
        let d ← getE y
        driveGroup d.grp
        let d ← getE y
        let G ← getG d.grp
        driveChunk G.chk
        reservation s0.P.reservationBudget : CM Unit).run t = .ok () s5 := by
      intro t ht
      rw [OrderMaintenance.Proof.run_getE_bind, run_bind_of_ok ht,
        OrderMaintenance.Proof.run_getE_bind, OrderMaintenance.Proof.run_getG_bind,
        run_bind_of_ok h4]
      exact h5
    by_cases hb : bgSplit s1 y s0.P = true
    · rw [ite_eq_left hb] at h2
      have hb' : ((s1.Gs.getX (s1.E.getX y).grp).st == St.quiet &&
          decide ((s1.Gs.getX (s1.E.getX y).grp).size ≥ s0.P.G)) = true := hb
      rw [ite_eq_left hb', run_bind_of_ok h2]
      exact hrest s2 h3
    · rw [ite_eq_right hb] at h2
      have he : s2 = s1 := by
        have : (pure () : CM Unit).run s1 = .ok () s1 := rfl
        rw [this] at h2; injection h2 with _ h; exact h.symm
      have hb' : ¬ ((s1.Gs.getX (s1.E.getX y).grp).st == St.quiet &&
          decide ((s1.Gs.getX (s1.E.getX y).grp).size ≥ s0.P.G)) = true := hb
      rw [ite_eq_right hb']
      exact hrest s1 (by
        rw [← he]
        exact h3)
  · obtain ⟨L1, n1, e1, hn1⟩ := m1
    obtain ⟨L3, n3, e3, hn3⟩ := m3
    obtain ⟨L4, n4, e4, hn4⟩ := m4
    obtain ⟨L5, n5, e5, hn5⟩ := m5
    -- the chunk grows
    have a1 := evalF_assign_ok (κ := κ) (s := s0) (L := L) (x := "g") (e := .eF .grp "y") (v :=
      gOf s0 y)
      (by simp [Exp.eF, Exp.ev, hy, hyE, Fld.cap, Fld.get, EF.get])
    have a2 := evalF_assign_ok (κ := κ) (s := s0) (L := upd L "g" (gOf s0 y)) (x := "c") (e :=
      .gF .chk "g")
      (v := cOf s0 y) (by
        simp [Exp.gF, Exp.ev, Machine.State.upd, hg0, Fld.cap, Fld.get, GF.get])
    set La := upd (upd L "g" (gOf s0 y)) "c" (cOf s0 y)
    have c1 := evalF_call_ok (q := csP) (args := [.var "c"]) (ds := []) (L := La)
      (by simp [evList, Exp.ev, La, Machine.State.upd]) e1
    have hLa : Machine.State.setLocs La [] (csP.rets.map L1) = La := rfl
    rw [hLa] at c1
    have hay : La "y" = y := by simp [La, Machine.State.upd, hy]
    -- the group's split
    have a3 := evalF_assign_ok (κ := κ) (s := s1) (L := La) (x := "g") (e := .eF .grp "y") (v :=
      gOf s1 y)
      (by simp [Exp.eF, Exp.ev, hay, hyE, Fld.cap, Fld.get, EF.get])
    set Lb := upd La "g" (gOf s1 y)
    have hby : Lb "y" = y := by simp [Lb, Machine.State.upd, hay]
    have e2 : ∃ c2, evalF κ (.ite bgSplitC (sgsP.call [.var "g"] []) .skip) s1 Lb = .ok s2 Lb c2
      ∧ c2 ≤ D2 + 20 := by
      have hcv : bgSplitC.ev κ s1 Lb = some (b2n (bgSplit s1 y s0.P)) := by
        simp only [bgSplitC, bgSplit, Exp.gF, Exp.ev, Lb, Machine.State.upd,
          ite_true, Option.bind_some, hg1,
          Fld.cap, Fld.get, GF.get, PF.get, hP1]
        cases hst : (s1.Gs.getX (gOf s1 y)).st <;>
          by_cases hz : s0.P.G ≤ (s1.Gs.getX (gOf s1 y)).size <;> simp [Machine.BinOp.eval,
            hz, St.toN, b2n]
      by_cases hb : bgSplit s1 y s0.P = true
      · obtain ⟨L2, n2, e2, hn2⟩ := m2 hb
        have c2 := evalF_call_ok (q := sgsP) (args := [.var "g"]) (ds := []) (L := Lb)
          (by simp [evList, Exp.ev, Lb, Machine.State.upd]) e2
        exact ⟨_, evalF_ite_t (by rw [hcv]) (by simp [hb, b2n]) c2, by
          simp [Exp.cost, costList, bgSplitC, Exp.gF]
          omega⟩
      · rw [ite_eq_right hb] at h2
        have he : s2 = s1 := by
          have : (pure () : CM Unit).run s1 = .ok () s1 := rfl
          rw [this] at h2; injection h2 with _ h; exact h.symm
        rw [he]
        exact ⟨_, evalF_ite_f (by
          rw [hcv]
          simp [b2n, hb]) evalF_skip, by simp [Exp.cost, bgSplitC, Exp.gF]⟩
    obtain ⟨c2, e2, hc2⟩ := e2
    -- the drives
    have a4 := evalF_assign_ok (κ := κ) (s := s2) (L := Lb) (x := "g") (e := .eF .grp "y") (v :=
      gOf s2 y)
      (by simp [Exp.eF, Exp.ev, hby, hyE, Fld.cap, Fld.get, EF.get])
    set Lc := upd Lb "g" (gOf s2 y)
    have c3 := evalF_call_ok (q := dgP) (args := [.var "g"]) (ds := []) (L := Lc)
      (by simp [evList, Exp.ev, Lc, Machine.State.upd]) e3
    have hLc : Machine.State.setLocs Lc [] (dgP.rets.map L3) = Lc := rfl
    rw [hLc] at c3
    have hcy : Lc "y" = y := by simp [Lc, Machine.State.upd, hby]
    have a5 := evalF_assign_ok (κ := κ) (s := s3) (L := Lc) (x := "g") (e := .eF .grp "y") (v :=
      gOf s3 y)
      (by simp [Exp.eF, Exp.ev, hcy, hyE, Fld.cap, Fld.get, EF.get])
    have a6 := evalF_assign_ok (κ := κ) (s := s3) (L := upd Lc "g" (gOf s3 y)) (x := "x") (e :=
      .gF .chk "g")
      (v := cOf s3 y) (by
        simp [Exp.gF, Exp.ev, Machine.State.upd, hg3, Fld.cap, Fld.get, GF.get])
    set Ld := upd (upd Lc "g" (gOf s3 y)) "x" (cOf s3 y)
    have c4 := evalF_call_ok (q := dcP) (args := [.var "x"]) (ds := []) (L := Ld)
      (by simp [evList, Exp.ev, Ld, Machine.State.upd]) e4
    have hLd : Machine.State.setLocs Ld [] (dcP.rets.map L4) = Ld := rfl
    rw [hLd] at c4
    have c5 := evalF_call_ok (q := resP) (args := []) (ds := []) (L := Ld) (by simp [evList]) e5
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 c1 (evalF_seq_ok2 a3
      (evalF_seq_ok2 e2
      (evalF_seq_ok2 a4 (evalF_seq_ok2 c3 (evalF_seq_ok2 a5 (evalF_seq_ok2 a6 (evalF_seq_ok2 c4
        c5))))))))), ?_⟩
    simp [Exp.cost, costList, Exp.eF, Exp.gF]; omega

/-! ### `insertAfter` -/

/-- Procedure performing the size updates and background work after insertion. -/
def bgP : Proc := {
  name := "background"
  params := ["y"]
  rets := []
  body := backgroundS
}

/-- `y := insertAfter x h`. FALLBACK never runs on the states of the cost invariant
(`insertAfter_cost`), so a failed guard is a `bug` here. -/
def insertAfterP : Proc where
  name := "insertAfter"
  params := ["x", "h"]
  rets := ["y"]
  body := cm{ try y ← insertElemP(x, h) catch bug; try call bgP(y) catch bug }

theorem insertAfterP_agree {κ : Caps} {s s1 s2 : Core} {L : Loc} {x hh y D : Nat} (hx : L "x" =
  x) (hl : L "h" = hh)
    (hxE : x < s.E.size) (hgG : (s.E.getX x).grp < s.Gs.size)
    (hnE : (s.E.getX x).next = 0 ∨ (s.E.getX x).next < s.E.size)
    (hE : s.E.size < κ.tbl .E) (hG : s.Gs.size ≤ κ.tbl .G)
    (h1 : (insertElem x hh).run s = .ok y s1) (h2 : (background y).run s1 = .ok () s2)
    (m2 : ∃ L' n, evalF κ bgP.body s1 (Machine.State.setLocs (fun _ => 0) ["y"] [y]) = .ok s2 L'
      n ∧ n ≤ D) :
    (insertAfter x hh).run s = .ok y s2 ∧
      ∃ L' n, evalF κ insertAfterP.body s L = .ok s2 L' n ∧ L' "y" = y ∧ n ≤ D + 220 := by
  refine ⟨?_, ?_⟩
  · unfold insertAfter
    rw [OrderMaintenance.Proof.run_bind, OrderMaintenance.Proof.run_onGuard_ok h1]
    dsimp only
    rw [OrderMaintenance.Proof.run_bind, OrderMaintenance.Proof.run_onGuard_ok h2]
    rfl
  · obtain ⟨Li, ni, ei, hyi, hni⟩ := insertElem_agree κ s (Machine.State.setLocs (fun _ => 0)
      ["x", "h"] [x, hh])
      (by
        simp [Machine.State.setLocs, Machine.State.upd])
      (by
        simp [Machine.State.setLocs, Machine.State.upd]) hxE hgG hnE hE hG h1
    have e1 := evalF_call_ok (q := insertElemP) (args := [.var "x", .var "h"]) (ds := ["y"]) (L
      := L)
      (by simp [evList, Exp.ev, hx, hl]) ei
    set L1 := Machine.State.setLocs L ["y"] (insertElemP.rets.map Li)
    have h1y : L1 "y" = y := by
      simp [L1, insertElemP, Machine.State.setLocs, Machine.State.upd, hyi]
    obtain ⟨Lb, nb, eb, hnb⟩ := m2
    have e2 := evalF_call_ok (q := bgP) (args := [.var "y"]) (ds := []) (L := L1) (by
      simp [evList, Exp.ev, h1y]) eb
    have c1 : evalF κ (.catch (insertElemP.call [.var "x", .var "h"] ["y"]) .bug) s L =
        .ok s1 L1 (1 + (1 + costList [.var "x", .var "h"] + 1 + ni)) := by
      simp only [evalF, e1]; rfl
    have c2 : evalF κ (.catch (bgP.call [.var "y"] []) .bug) s1 L1 =
        .ok s2 L1 (1 + (1 + costList [.var "y"] + 0 + nb)) := by
      simp only [evalF, e2]; rfl
    refine ⟨L1, _, evalF_seq_ok2 c1 c2, h1y, ?_⟩
    simp [costList, Exp.cost]; omega

end OrderMaintenance.Impl
