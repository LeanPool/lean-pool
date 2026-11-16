/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Background
public import LeanPool.OrderMaintenance.Proof.Top.PrepContract


/-!
# M6: building a core at Level M (`initCore`, `initStep`, `prepareStep`)

A new core lives in freshly allocated machine arrays, which read 0 everywhere: the core
`freshC P`, with every array empty. `initStateS` pushes and writes it into Level F's
`initState P`. The top structure is then built one level per `initStep`; `resetTop` runs only on
the fresh top structure, where it changes nothing.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => Machine.State.upd

/-- A core in fresh memory: every array empty (all cells read 0). -/
def freshC (P : Params) : Core := {
  P := P
  E := #[]
  Gs := #[]
  C := #[]
  nodes := #[]
}

/-- Allocate the dummy element and dead sentinel with a central label. -/
def initEltS : Stm := cm{
  t := new E; t := new E
  E[1].grp := 1; E[1].lab := 1 <<< (P.Be - 1); E[1].dead := 1 }
/-- Allocate the dummy group and the sentinel's initial group. -/
def initGrpS : Stm := cm{
  t := new G; t := new G
  G[1].chk := 1; G[1].lab := 1 <<< (P.Bg - 1); G[1].first := 1; G[1].last := 1
  G[1].size := 1 }
/-- Allocate the dummy chunk and the initial singleton chunk. -/
def initChkS : Stm := cm{ t := new C; t := new C; C[1].first := 1; C[1].last := 1; C[1].size := 1 }
/-- Initialize the dummy node, list heads, list tail and element count. -/
def initScS : Stm := cm{
  t := new N; S.firstGroup := 1; S.firstChunk := 1; S.head := 1; S.tail := 1
  S.count := 1 }
/-- `set (initState P)`, from fresh memory. -/
def initStateS : Stm := initEltS;; initGrpS;; initChkS;; initScS

theorem evalF_push_ok {κ : Caps} {s : Core} {L : Loc} {t : Tbl} {x : Reg} (h : t.size s < κ.tbl t) :
    evalF κ (.push t x) s L = .ok (t.push s) (upd L x (t.size s)) pushCost := by
  simp [evalF, h]

/-- The stages of `initStateS` on fresh memory. -/
def iE (P : Params) : Core :=
  {
    freshC P with
    E := #[default, {
      grp := 1
      lab := 1 <<< (P.elementBits - 1)
      h := 0
      live := false
    }]
  }
/-- The partially initialized core after creating its initial group. -/
def iG (P : Params) : Core :=
  {
    iE P with
    Gs := #[default, {
      chk := 1
      lab := 1 <<< (P.groupBits - 1)
      first := 1
      last := 1
      size := 1
    }]
  }
/-- The partially initialized core after creating its initial chunk. -/
def iC (P : Params) : Core := {
  iG P with
  C := #[default, {
    first := 1
    last := 1
    size := 1
  }]
}

theorem initEltS_ok {κ : Caps} {P : Params} {L : Loc} (hBe : 1 ≤ P.elementBits) (hE : 2 ≤ κ.tbl
  .E) :
    ∃ L' c, evalF κ initEltS (freshC P) L = .ok (iE P) L' c ∧ c ≤ 60 ∧ ∀ r, r ≠ "t" → L' r = L r
      := by
  have p1 := evalF_push_ok (κ := κ) (s := freshC P) (L := L) (t := .E) (x := "t") (by
    simp [Tbl.size, freshC]
    omega)
  have p2 := evalF_push_ok (κ := κ) (s := Tbl.push (freshC P) .E) (L := upd L "t" 0) (t := .E)
    (x := "t")
    (by
      simp [Tbl.size, Tbl.push, freshC]
      omega)
  set s2 := Tbl.push (Tbl.push (freshC P) .E) .E
  have hs2 : s2.E.size = 2 := by simp [s2, Tbl.push, freshC]
  have w1 := evalF_wrE_ok (κ := κ) (s := s2) (L := upd (upd L "t" 0) "t" 1) (k := .grp) (i := (1
    : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by omega)  rfl
  set s3 : Core := {
    s2 with
    E := s2.E.modify 1 (EF.set · 1 .grp)
  }
  have w2 := evalF_wrE_ok (κ := κ) (s := s3) (L := upd (upd L "t" 0) "t" 1) (k := .lab) (i := (1
    : Exp))
    (e := .bin .shl 1 (.prm .Be - 1)) (j := 1) (w := 1 <<< (P.elementBits - 1)) rfl
    (by
      simp [Exp.ev, Machine.BinOp.eval, PF.get, s3, s2, Tbl.push, freshC, hBe, Nat.shiftLeft_eq])
    (by simp [s3, hs2])  rfl
  set s4 : Core := {
    s3 with
    E := s3.E.modify 1 (EF.set · (1 <<< (P.elementBits - 1)) .lab)
  }
  have w3 := evalF_wrE_ok (κ := κ) (s := s4) (L := upd (upd L "t" 0) "t" 1) (k := .dead) (i :=
    (1 : Exp))
    (e := (1 : Exp)) (j := 1) (w := 1) rfl rfl (by simp [s4, s3, hs2])  rfl
  have hfin : ({
    s4 with
    E := s4.E.modify 1 (EF.set · 1 .dead)
  } : Core) = iE P := by
    simp only [s4, s3, s2, iE, freshC, Tbl.push]
    congr 1
  refine ⟨_, _, evalF_seq_ok2 p1 (evalF_seq_ok2 p2 (evalF_seq_ok2 (by
    simp only [Stm.weF]
    exact w1)
    (evalF_seq_ok2 (by
      simp only [Stm.weF]
      exact w2) (by
      simp only [Stm.weF]
      rw [← hfin]
      exact w3)))), ?_,
    fun r h => by simp [Machine.State.upd, h]⟩
  simp [pushCost, Exp.cost]

theorem initGrpS_ok {κ : Caps} {P : Params} {L : Loc} (hBg : 1 ≤ P.groupBits) (hG : 2 ≤ κ.tbl .G) :
    ∃ L' c, evalF κ initGrpS (iE P) L = .ok (iG P) L' c ∧ c ≤ 80 ∧ ∀ r, r ≠ "t" → L' r = L r := by
  have p1 := evalF_push_ok (κ := κ) (s := iE P) (L := L) (t := .G) (x := "t") (by
    simp [Tbl.size, iE, freshC]
    omega)
  have p2 := evalF_push_ok (κ := κ) (s := Tbl.push (iE P) .G) (L := upd L "t" 0) (t := .G) (x :=
    "t")
    (by
      simp [Tbl.size, Tbl.push, iE, freshC]
      omega)
  set s2 := Tbl.push (Tbl.push (iE P) .G) .G
  have hs2 : s2.Gs.size = 2 := by simp [s2, Tbl.push, iE, freshC]
  set L2 := upd (upd L "t" 0) "t" 1
  have w1 := evalF_wrG_ok (κ := κ) (s := s2) (L := L2) (k := .chk) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by omega)  rfl
  set s3 : Core := {
    s2 with
    Gs := s2.Gs.modify 1 (GF.set · 1 .chk)
  }
  have w2 := evalF_wrG_ok (κ := κ) (s := s3) (L := L2) (k := .lab) (i := (1 : Exp))
    (e := .bin .shl 1 (.prm .Bg - 1)) (j := 1) (w := 1 <<< (P.groupBits - 1)) rfl
    (by
      simp [Exp.ev, Machine.BinOp.eval, PF.get, s3, s2, Tbl.push, iE, freshC, hBg,
        Nat.shiftLeft_eq])
    (by simp [s3, hs2])  rfl
  set s4 : Core := {
    s3 with
    Gs := s3.Gs.modify 1 (GF.set · (1 <<< (P.groupBits - 1)) .lab)
  }
  have w3 := evalF_wrG_ok (κ := κ) (s := s4) (L := L2) (k := .first) (i := (1 : Exp)) (e := (1 :
    Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s4, s3, hs2])  rfl
  set s5 : Core := {
    s4 with
    Gs := s4.Gs.modify 1 (GF.set · 1 .first)
  }
  have w4 := evalF_wrG_ok (κ := κ) (s := s5) (L := L2) (k := .last) (i := (1 : Exp)) (e := (1 :
    Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s5, s4, s3, hs2])  rfl
  set s6 : Core := {
    s5 with
    Gs := s5.Gs.modify 1 (GF.set · 1 .last)
  }
  have w5 := evalF_wrG_ok (κ := κ) (s := s6) (L := L2) (k := .size) (i := (1 : Exp)) (e := (1 :
    Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s6, s5, s4, s3, hs2])  rfl
  have hfin : ({
    s6 with
    Gs := s6.Gs.modify 1 (GF.set · 1 .size)
  } : Core) = iG P := by
    simp only [s6, s5, s4, s3, s2, iG, iE, freshC, Tbl.push]
    congr 1
  refine ⟨_, _, evalF_seq_ok2 p1 (evalF_seq_ok2 p2 (evalF_seq_ok2 (by
    simp only [Stm.wgF]
    exact w1)
    (evalF_seq_ok2 (by
      simp only [Stm.wgF]
      exact w2) (evalF_seq_ok2 (by
      simp only [Stm.wgF]
      exact w3)
    (evalF_seq_ok2 (by
      simp only [Stm.wgF]
      exact w4) (by
      simp only [Stm.wgF]
      rw [← hfin]
      exact w5)))))), ?_,
    fun r h => by simp [L2, Machine.State.upd, h]⟩
  simp [pushCost, Exp.cost]

theorem initChkS_ok {κ : Caps} {P : Params} {L : Loc} (hC : 2 ≤ κ.tbl .C) :
    ∃ L' c, evalF κ initChkS (iG P) L = .ok (iC P) L' c ∧ c ≤ 60 ∧ ∀ r, r ≠ "t" → L' r = L r := by
  have p1 := evalF_push_ok (κ := κ) (s := iG P) (L := L) (t := .C) (x := "t")
    (by
      simp [Tbl.size, iG, iE, freshC]
      omega)
  have p2 := evalF_push_ok (κ := κ) (s := Tbl.push (iG P) .C) (L := upd L "t" 0) (t := .C) (x :=
    "t")
    (by
      simp [Tbl.size, Tbl.push, iG, iE, freshC]
      omega)
  set s2 := Tbl.push (Tbl.push (iG P) .C) .C
  have hs2 : s2.C.size = 2 := by simp [s2, Tbl.push, iG, iE, freshC]
  set L2 := upd (upd L "t" 0) "t" 1
  have w1 := evalF_wrC_ok (κ := κ) (s := s2) (L := L2) (k := .first) (i := (1 : Exp)) (e := (1 :
    Exp))
    (j := 1) (w := 1) rfl rfl (by omega)  rfl
  set s3 : Core := {
    s2 with
    C := s2.C.modify 1 (CF.set · 1 .first)
  }
  have w2 := evalF_wrC_ok (κ := κ) (s := s3) (L := L2) (k := .last) (i := (1 : Exp)) (e := (1 :
    Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s3, hs2])  rfl
  set s4 : Core := {
    s3 with
    C := s3.C.modify 1 (CF.set · 1 .last)
  }
  have w3 := evalF_wrC_ok (κ := κ) (s := s4) (L := L2) (k := .size) (i := (1 : Exp)) (e := (1 :
    Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s4, s3, hs2])  rfl
  have hfin : ({
    s4 with
    C := s4.C.modify 1 (CF.set · 1 .size)
  } : Core) = iC P := by
    simp only [s4, s3, s2, iC, iG, iE, freshC, Tbl.push]
    congr 1
  refine ⟨_, _, evalF_seq_ok2 p1 (evalF_seq_ok2 p2 (evalF_seq_ok2 (by
    simp only [Stm.wcF]
    exact w1)
    (evalF_seq_ok2 (by
      simp only [Stm.wcF]
      exact w2) (by
      simp only [Stm.wcF]
      rw [← hfin]
      exact w3)))), ?_,
    fun r h => by simp [L2, Machine.State.upd, h]⟩
  simp [pushCost, Exp.cost]

theorem initScS_ok {κ : Caps} {P : Params} {L : Loc} (hN : 1 ≤ κ.tbl .N) :
    ∃ L' c, evalF κ initScS (iC P) L = .ok (initState P) L' c ∧ c ≤ 40 ∧ ∀ r, r ≠ "t" → L' r = L
      r := by
  have p1 := evalF_push_ok (κ := κ) (s := iC P) (L := L) (t := .N) (x := "t")
    (by
      simp [Tbl.size, iC, iG, iE, freshC]
      omega)
  set L1 := upd L "t" (Tbl.size (iC P) .N)
  set t0 := Tbl.push (iC P) .N
  have hst : SF.set (SF.set (SF.set (SF.set (SF.set t0 1 .firstGroup) 1 .firstChunk) 1 .head) 1
    .tail) 1 .count =
      initState P := rfl
  have e2 := evalF_seq_ok2 (evalF_wrS_ok (κ := κ) (s := t0) (L := L1) (k := .firstGroup) (e :=
    (1 : Exp)) (w := 1) rfl rfl)
    (evalF_seq_ok2 (evalF_wrS_ok (k := .firstChunk) (e := (1 : Exp)) (w := 1) rfl rfl)
    (evalF_seq_ok2 (evalF_wrS_ok (k := .head) (e := (1 : Exp)) (w := 1) rfl rfl)
    (evalF_seq_ok2 (evalF_wrS_ok (k := .tail) (e := (1 : Exp)) (w := 1) rfl rfl)
      (evalF_wrS_ok (k := .count) (e := (1 : Exp)) (w := 1) rfl rfl))))
  rw [hst] at e2
  exact ⟨_, _, evalF_seq_ok2 p1 e2, by simp [pushCost, Exp.cost], fun r h => by simp [L1,
    Machine.State.upd, h]⟩

theorem initStateS_ok {κ : Caps} {P : Params} {L : Loc} (hBe : 1 ≤ P.elementBits) (hBg : 1 ≤
  P.groupBits)
    (hE : 2 ≤ κ.tbl .E) (hG : 2 ≤ κ.tbl .G) (hC : 2 ≤ κ.tbl .C) (hN : 1 ≤ κ.tbl .N) :
    ∃ L' c, evalF κ initStateS (freshC P) L = .ok (initState P) L' c ∧ c ≤ 300 ∧ ∀ r, r ≠ "t" →
      L' r = L r := by
  obtain ⟨L1, c1, e1, hc1, hF1⟩ := initEltS_ok (κ := κ) (L := L) hBe hE
  obtain ⟨L2, c2, e2, hc2, hF2⟩ := initGrpS_ok (κ := κ) (L := L1) hBg hG
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := initChkS_ok (κ := κ) (L := L2) (P := P) hC
  obtain ⟨L4, c4, e4, hc4, hF4⟩ := initScS_ok (κ := κ) (L := L3) (P := P) hN
  exact ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4)), by omega,
    fun r h => by rw [hF4 r h, hF3 r h, hF2 r h, hF1 r h]⟩

/-! ### `initStep` -/

/-- Link a newly prepared node to its lower entry, using chunk parents at height one. -/
def isLink : Stm := cm{
  if h = 1 then { clear cin[c]; append cin[c] (v, 0); lpar[c] := v }
  else { clear inTab[bl]; append inTab[bl] (v, 0); N[bl].livePar := v } }
/-- Allocate a singleton preparation node at the current height. -/
def isNode : Stm := cm{
  v := new N; N[v].height := h; append children[v] (bl, 0); append table[v] (bl, ctr)
  N[v].weight := 1; N[v].first := c; N[v].last := c }
/-- Advance the suspended preparation height, accumulated tag and ancestor path. -/
def isUp : Stm := cm{ prepSet(h + 1, v, tg + ctr * (1 <<< ((h - 1) * P.beta))); prepPath(h, v) }
/-- Construct and link one preparation level and report that preparation continues. -/
def isBuild : Stm := cm{ ctr := 1 <<< (P.beta - 1); isNode; isLink; isUp; done := 0 }
/-- Store the completed chunk tag and commit preparation. -/
def isFinish : Stm := cm{ C[c].tag := tg; prepCommit; done := 1 }
/-- Load the suspended preparation and clear the first chunk membership list if needed. -/
def isPre : Stm := cm{
  c := O.prepChunk; h := O.prepH; bl := O.prepBelow; tg := O.prepTag
  if h = 1 then clear cin[c] }

/-- `done := initStep`. -/
def initStepP : Proc where
  name := "initStep"
  params := []
  rets := ["done"]
  body := cm{ if O.prepOn then { isPre; if h ≤ P.H then isBuild else isFinish } else done := 1 }

theorem initStepP_none {κ : Caps} {s : Core} {L : Loc} (hp : s.prep = none) :
    ∃ L' c, evalF κ initStepP.body s L = .ok s L' c ∧ L' "done" = 1 ∧ c ≤ 10 := by
  refine ⟨_, _, evalF_ite_f (by simp [Exp.ev, OF.get, hp, b2n]) (evalF_assign_ok (v := 1) rfl),
    by simp [Machine.State.upd], by simp [Exp.cost]⟩

/-- The locals after the reads. -/
def isL (L : Loc) (pr : Prep) : Loc :=
  upd (upd (upd (upd L "c" pr.chunk) "h" pr.h) "bl" pr.below) "tg" pr.tag

theorem isPre_ok {κ : Caps} {s : Core} {L : Loc} {pr : Prep} (hp : s.prep = some pr)
    (hc : pr.h = 1 → pr.chunk < κ.lrec .cin) :
    evalF κ isPre s L = .ok (if pr.h = 1 then {
      s with
      cin := s.cin.setX pr.chunk []
    } else s)
      (isL L pr)
      (if pr.h = 1 then 19 else 17) := by
  have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "c") (e := .opt .prepChunk) (v :=
    pr.chunk)
    (by simp [Exp.ev, OF.get, hp])
  have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "c" pr.chunk) (x := "h") (e := .opt
    .prepH) (v := pr.h)
    (by simp [Exp.ev, OF.get, hp])
  have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L "c" pr.chunk) "h" pr.h) (x := "bl")
    (e := .opt .prepBelow) (v := pr.below) (by simp [Exp.ev, OF.get, hp])
  have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L "c" pr.chunk) "h" pr.h)
    "bl" pr.below)
    (x := "tg") (e := .opt .prepTag) (v := pr.tag) (by simp [Exp.ev, OF.get, hp])
  by_cases h1 : pr.h = 1
  · have e5 : evalF κ (.ite ("h" =ₑ 1) (.lclear .cin "c") .skip) s (isL L pr) =
        .ok {
          s with
          cin := s.cin.setX pr.chunk []
        } (isL L pr) 7 := by
      simp [evalF, Exp.ev, isL, Machine.State.upd, h1,
        Machine.BinOp.eval, LK.set, LK.recOk, LK.valid,
        hc h1, LK.put, Exp.cost, Res.addCost]
    rw [ite_eq_left h1, ite_eq_left h1]
    simp only [isPre]; exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2
      b4 e5)))
  · have e5 : evalF κ (.ite ("h" =ₑ 1) (.lclear .cin "c") .skip) s (isL L pr) = .ok s (isL L pr)
      5 := by
      simp [evalF, Exp.ev, isL, Machine.State.upd, h1,
        Machine.BinOp.eval, Exp.cost, Res.addCost]
    rw [ite_eq_right h1, ite_eq_right h1]
    simp only [isPre]; exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2
      b4 e5)))

/-- The state after the last step (`initStep_last`). -/
def isLastS (s : Core) (pr : Prep) : Core :=
  {
    s with
    path := s.path.setX pr.chunk pr.path
    C := s.C.modify pr.chunk (fun C => {
      C with
      tag := pr.tag
    })
    prep := none
  }

theorem initStepP_last {κ : Caps} {s : Core} {L : Loc} {pr : Prep} (hp : s.prep = some pr) (h1 :
  pr.h ≠ 1)
    (hH : s.P.H < pr.h) (hcs : pr.chunk < s.C.size) :
    ∃ L' c, evalF κ initStepP.body s L = .ok (isLastS s pr) L' c ∧ L' "done" = 1 ∧ c ≤ 80 := by
  have e1 := isPre_ok (κ := κ) (L := L) hp (fun h => absurd h h1)
  rw [ite_eq_right h1, ite_eq_right h1] at e1
  set L1 := isL L pr
  have w2 := evalF_wrC_ok (κ := κ) (s := s) (L := L1) (k := .tag) (i := .var "c") (e := .var
    "tg") (j := pr.chunk)
    (w := pr.tag) (by simp [Exp.ev, L1, isL, Machine.State.upd]) (by
      simp [Exp.ev, L1, isL, Machine.State.upd])
    hcs  rfl
  set s2 : Core := {
    s with
    C := s.C.modify pr.chunk (CF.set · pr.tag .tag)
  }
  have e3 : evalF κ .prepCommit s2 L1 = .ok (isLastS s pr) L1 15 := by
    simp [evalF, s2, hp]; rfl
  have e4 := evalF_assign_ok (κ := κ) (s := isLastS s pr) (L := L1) (x := "done") (e := (1 :
    Exp)) (v := 1) rfl
  have hc : ("h" ≤ₑ .prm .H : Exp).ev κ s L1 = some 0 := by
    simp [Exp.ev, L1, isL, Machine.State.upd,
      Machine.BinOp.eval, PF.get]; omega
  refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, OF.get, hp, b2n]) one_ne_zero
    (evalF_seq_ok2 e1 (evalF_ite_f hc (evalF_seq_ok2 (by
      simp only [Stm.wcF]
      exact w2) (evalF_seq_ok2 e3 e4)))),
    by simp [Machine.State.upd], by simp [Exp.cost]⟩

theorem evalF_lgrow_ok {κ : Caps} {s s' : Core} {L : Loc} {k : LK} {i a b : Exp} {x va vb : Nat}
    (hi : i.ev κ s L = some x) (ha : a.ev κ s L = some va) (hb : b.ev κ s L = some vb)
    (hs : k.set κ s x (k.view s x ++ [(va, vb)]) = some s') :
    evalF κ (.lgrow k i a b) s L = .ok s' L (14 + 6 * i.cost + a.cost + b.cost) := by
  simp [evalF, hi, ha, hb, hs]

/-- Level F's new chain node, as `initStep` makes it (`chainNew`). -/
def nodeS (S : Core) (pr : Prep) : Core :=
  {
    S with
    nodes := (S.nodes.push {
      height := pr.h
    }).modify S.nodes.size (chainNew S.P pr)
  }

/-- The locals after the reads and the label `ctr`. -/
def isL2 (L : Loc) (pr : Prep) (β : Nat) : Loc := upd (isL L pr) "ctr" (1 <<< (β - 1))

theorem isNode_ok {κ : Caps} {S : Core} {L : Loc} {pr : Prep} (hN : S.nodes.size < κ.tbl .N)
    (hrc : S.nodes.size < κ.lrec .children) (hrt : S.nodes.size < κ.lrec .table)
    (hcc : 1 ≤ κ.lcap .children) (hct : 1 ≤ κ.lcap .table) :
    ∃ c, evalF κ isNode S (isL2 L pr S.P.beta) =
      .ok (nodeS S pr) (upd (isL2 L pr S.P.beta) "v" S.nodes.size) c ∧ c ≤ 120 := by
  set v := S.nodes.size
  set L0 := isL2 L pr S.P.beta
  set L1 := upd L0 "v" v
  have h1v : L1 "v" = v := by simp [L1, Machine.State.upd]
  have h1h : L1 "h" = pr.h := by simp [L1, L0, isL2, isL, Machine.State.upd]
  have h1bl : L1 "bl" = pr.below := by simp [L1, L0, isL2, isL, Machine.State.upd]
  have h1c : L1 "c" = pr.chunk := by simp [L1, L0, isL2, isL, Machine.State.upd]
  have h1ctr : L1 "ctr" = 1 <<< (S.P.beta - 1) := by simp [L1, L0, isL2, Machine.State.upd]
  have p1 := evalF_push_ok (κ := κ) (s := S) (L := L0) (t := .N) (x := "v") (by
    simpa [Tbl.size] using hN)
  set S1 := Tbl.push S .N
  have hS1 : S1.nodes.size = v + 1 := by simp [S1, Tbl.push, v]
  have w2 := evalF_wrN_ok (κ := κ) (s := S1) (L := L1) (k := .height) (i := .var "v") (e := .var
    "h") (j := v)
    (w := pr.h) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1h]) (by omega)  rfl
  set S2 : Core := {
    S1 with
    nodes := S1.nodes.modify v (NF.set · pr.h .height)
  }
  have hS2v : S2.nodes.getX v = {
    height := pr.h
  } := by
    simp only [S2, S1, Tbl.push, v]; rw [Array.modify_push_size, getX_push', ite_eq_left rfl]; rfl
  have hS2n : S2.nodes.size = v + 1 := by simp [S2, hS1]
  set S3 := LK.put S2 v (LK.view S2 v .children ++ [(pr.below, 0)]) .children
  have e3 := evalF_lgrow_ok (κ := κ) (s := S2) (s' := S3) (L := L1) (k := .children) (i := .var
    "v") (a := .var "bl")
    (b := (0 : Exp)) (x := v) (va := pr.below) (vb := 0) (by simp [Exp.ev, h1v]) (by
      simp [Exp.ev, h1bl]) rfl
    (by
      simp [LK.set, LK.recOk, LK.valid, LK.view, hS2v, hS2n, hrc, hcc, S3])
  have hS3v : S3.nodes.getX v = {
    height := pr.h
    children := [pr.below]
  } := by
    simp only [S3, LK.put, LK.view, hS2v, getX_modify', hS2n, show v < v + 1 by omega, and_self,
      ite_true]; simp
  have hS3n : S3.nodes.size = v + 1 := by simp [S3, hS2n]
  set S4 := LK.put S3 v (LK.view S3 v .table ++ [(pr.below, 1 <<< (S.P.beta - 1))]) .table
  have e4 := evalF_lgrow_ok (κ := κ) (s := S3) (s' := S4) (L := L1) (k := .table) (i := .var
    "v") (a := .var "bl")
    (b := .var "ctr") (x := v) (va := pr.below) (vb := 1 <<< (S.P.beta - 1)) (by simp [Exp.ev, h1v])
    (by simp [Exp.ev, h1bl]) (by simp [Exp.ev, h1ctr])
    (by
      simp [LK.set, LK.recOk, LK.valid, LK.view, hS3v, hS3n, hrt, hct, S4])
  have hS4n : S4.nodes.size = v + 1 := by simp [S4, hS3n]
  have w5 := evalF_wrN_ok (κ := κ) (s := S4) (L := L1) (k := .weight) (i := .var "v") (e := (1 :
    Exp)) (j := v)
    (w := 1) (by simp [Exp.ev, h1v]) rfl (by omega)  rfl
  set S5 : Core := {
    S4 with
    nodes := S4.nodes.modify v (NF.set · 1 .weight)
  }
  have w6 := evalF_wrN_ok (κ := κ) (s := S5) (L := L1) (k := .first) (i := .var "v") (e := .var
    "c") (j := v)
    (w := pr.chunk) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1c]) (by simp [S5, hS4n])  rfl
  set S6 : Core := {
    S5 with
    nodes := S5.nodes.modify v (NF.set · pr.chunk .first)
  }
  have w7 := evalF_wrN_ok (κ := κ) (s := S6) (L := L1) (k := .last) (i := .var "v") (e := .var
    "c") (j := v)
    (w := pr.chunk) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1c]) (by simp [S6, S5, hS4n])  rfl
  have hfin : ({
    S6 with
    nodes := S6.nodes.modify v (NF.set · pr.chunk .last)
  } : Core) = nodeS
    S pr := by
    have hv2 : LK.view S2 v .children = [] := by simp [LK.view, hS2v]
    have hv3 : LK.view S3 v .table = [] := by simp [LK.view, hS3v]
    have hS3' : S3 = LK.put S2 v [(pr.below, 0)] .children := by
      simp only [S3, hv2, List.nil_append]
    have hS4' : S4 = LK.put S3 v [(pr.below, 1 <<< (S.P.beta - 1))] .table := by
      simp only [S4, hv3, List.nil_append]
    simp only [S6, S5, hS4', hS3', S2, S1, nodeS, Tbl.push, LK.put, Array.modify_modify_same, v]
    rw [Array.modify_push_size, Array.modify_push_size]
    rfl
  rw [hfin] at w7
  exact ⟨_, evalF_seq_ok2 p1 (evalF_seq_ok2 w2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 w5
    (evalF_seq_ok2 w6 w7))))), by simp [pushCost, Exp.cost]⟩

theorem lor_add_shift {a c k : Nat} (ha : a < 2 ^ k) : a ||| (c <<< k) = a + c * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]; ring

/-- The accumulated chunk tag after adding the current level's central label. -/
def prepTag (P : Params) (pr : Prep) : Nat := pr.tag + (1 <<< (P.beta - 1)) * 2 ^ ((pr.h - 1) *
  P.beta)
/-- The suspended preparation after installing a fresh node at the current level. -/
def prepMid (P : Params) (pr : Prep) (v : Nat) : Prep := {
  pr with
  h := pr.h + 1
  below := v
  tag := prepTag P pr
}

/-- The prep record after building height `pr.h` as node `v` (Level M's form of `prepNext`). -/
theorem prepNext_eq {P : Params} {pr : Prep} {v : Nat} (htag : pr.tag < 2 ^ ((pr.h - 1) * P.beta)) :
    prepNext P pr v = {
      prepMid P pr v with
      path := pr.path.setX pr.h v
    } := by
  simp only [prepNext, prepMid, prepTag, lor_add_shift htag]


theorem isUp_ok {κ : Caps} {S : Core} {L : Loc} {pr : Prep} {v : Nat} (hp : S.prep = some pr)
    (hh : L "h" = pr.h) (hv : L "v" = v) (htg : L "tg" = pr.tag) (hctr : L "ctr" = 1 <<<
      (S.P.beta - 1))
    (h1 : 1 ≤ pr.h) (hw : pr.h < κ.pw) (htag : pr.tag < 2 ^ ((pr.h - 1) * S.P.beta)) :
    ∃ c, evalF κ isUp S L = .ok {
      S with
      prep := some (prepNext S.P pr v)
    } L c ∧ c ≤ 60 := by
  rw [prepNext_eq htag]
  have e1 : evalF κ (.prepSet ("h" + 1) "v" ("tg" + "ctr" * .bin .shl 1 (("h" - 1) * .prm
    .beta))) S L =
      .ok {
        S with
        prep := some (prepMid S.P pr v)
      } L 26 := by
    simp [evalF, Exp.ev, hp, hh, hv, htg, hctr, Machine.BinOp.eval, PF.get, h1,
      prepMid, prepTag,
      Nat.shiftLeft_eq, Exp.cost]
  have e2 : evalF κ (.prepPath "h" "v") {
    S with
    prep := some (prepMid S.P pr v)
  } L =
      .ok {
        S with
        prep := some {
          prepMid S.P pr v with
          path := pr.path.setX pr.h v
        }
      } L 11 := by
    simp [evalF, Exp.ev, hh, hv, hw, Exp.cost, prepMid]
  exact ⟨_, evalF_seq_ok2 e1 e2, by omega⟩

/-- `isLink` above height 1: `below` gets the new node as its table and live parent. -/
theorem isLink_mid {κ : Caps} {S : Core} {L : Loc} {v bl : Nat} (hh : L "h" ≠ 1) (hv : L "v" =
  v) (hbl : L "bl" = bl)
    (hbs : bl < S.nodes.size) (hbr : bl < κ.lrec .inTab) (hci : 1 ≤ κ.lcap
      .inTab) :
    ∃ c, evalF κ isLink S L = .ok {
      S with
      nodes := S.nodes.modify bl fun n => {
        n with
        inTables := [v]
        livePar := v
      }
    } L c ∧ c ≤ 60 := by
  have e1 : evalF κ (.lclear .inTab "bl") S L = .ok (LK.put S bl [] .inTab) L 3 := by
    simp [evalF, Exp.ev, hbl, LK.set, LK.recOk, LK.valid, hbs, hbr, Exp.cost]
  set S1 := LK.put S bl [] .inTab
  have hv1 : LK.view S1 bl .inTab = [] := by
    rw [LK.view_put (by simp [LK.recOk, hbs]) (by rfl)]; simp
  set S2 := LK.put S1 bl [(v, 0)] .inTab
  have e2 := evalF_lgrow_ok (κ := κ) (s := S1) (s' := S2) (L := L) (k := .inTab) (i := .var
    "bl") (a := .var "v")
    (b := (0 : Exp)) (x := bl) (va := v) (vb := 0) (by simp [Exp.ev, hbl]) (by
      simp [Exp.ev, hv]) rfl
    (by
      rw [hv1]
      simp [LK.set, LK.recOk, LK.valid, S1, hbs, hbr, hci, S2])
  have w3 := evalF_wrN_ok (κ := κ) (s := S2) (L := L) (k := .livePar) (i := .var "bl") (e :=
    .var "v") (j := bl) (w := v)
    (by simp [Exp.ev, hbl]) (by simp [Exp.ev, hv]) (by simp [S2, S1, hbs])  rfl
  have hfin : ({
    S2 with
    nodes := S2.nodes.modify bl (NF.set · v .livePar)
  } : Core) =
      {
        S with
        nodes := S.nodes.modify bl fun n => {
          n with
          inTables := [v]
          livePar := v
        }
      } := by
    simp only [S2, S1, LK.put, Array.modify_modify_same]; rfl
  rw [hfin] at w3
  have hc : ("h" =ₑ 1 : Exp).ev κ S L = some 0 := by simp [Exp.ev, Machine.BinOp.eval, hh]
  exact ⟨_, evalF_ite_f hc (evalF_seq_ok2 e1 (evalF_seq_ok2 e2 w3)), by simp [Exp.cost]⟩

/-- Install the first preparation node as a chunk's live parent and sole table. -/
def linkFirstS (S : Core) (c v : Nat) : Core := {
  S with
  cin := (S.cin.setX c []).setX c [v]
  lpar := S.lpar.setX c v
}

/-- `isLink` at height 1: chunk `c` gets the new node as its table and live parent. -/
theorem isLink_first {κ : Caps} {S : Core} {L : Loc} {v c : Nat} (hh : L "h" = 1) (hv : L "v" =
  v) (hc : L "c" = c)
    (hcr : c < κ.lrec .cin) (hcc : 1 ≤ κ.lcap .cin) (hca : c < κ.arr .lpar) :
    ∃ n, evalF κ isLink S L = .ok (linkFirstS S c v) L n ∧ n ≤ 60 := by
  have e1 : evalF κ (.lclear .cin "c") S L = .ok (LK.put S c [] .cin) L 3 := by
    simp [evalF, Exp.ev, hc, LK.set, LK.recOk, LK.valid, hcr, Exp.cost]
  set S1 := LK.put S c [] .cin
  have hv1 : LK.view S1 c .cin = [] := by
    rw [LK.view_put (by rfl) (by rfl)]; simp
  set S2 := LK.put S1 c [(v, 0)] .cin
  have e2 := evalF_lgrow_ok (κ := κ) (s := S1) (s' := S2) (L := L) (k := .cin) (i := .var "c")
    (a := .var "v")
    (b := (0 : Exp)) (x := c) (va := v) (vb := 0) (by simp [Exp.ev, hc]) (by simp [Exp.ev, hv]) rfl
    (by
      rw [hv1]
      simp [LK.set, LK.recOk, LK.valid, hcr, hcc, S2])
  have w3 : evalF κ (.wr (.a .lpar) "c" "v") S2 L = .ok (linkFirstS S c v) L 3 := by
    simp [evalF, Exp.ev, hc, hv, Fld.set, hca, AF.set, AF.get, S2, S1, LK.put, Exp.cost, linkFirstS]
  have hc1 : ("h" =ₑ 1 : Exp).ev κ S L = some 1 := by simp [Exp.ev, Machine.BinOp.eval, hh]
  exact ⟨_, evalF_ite_t hc1 one_ne_zero (evalF_seq_ok2 e1 (evalF_seq_ok2 e2 w3)), by simp
    [Exp.cost]⟩

theorem initStepP_mid {κ : Caps} {s : Core} {L : Loc} {pr : Prep} (hp : s.prep = some pr) (h1 :
  pr.h ≠ 1)
    (hH : pr.h ≤ s.P.H) (hh0 : 1 ≤ pr.h) (htag : pr.tag < 2 ^ ((pr.h - 1) * s.P.beta)) (hb1 : 1
      ≤ s.P.beta)
    (hbs : pr.below < s.nodes.size) (hw : pr.h < κ.pw)
    (hN : s.nodes.size < κ.tbl .N) (hrc : s.nodes.size < κ.lrec .children) (hrt : s.nodes.size <
      κ.lrec .table)
    (hcc : 1 ≤ κ.lcap .children) (hct : 1 ≤ κ.lcap .table) (hbr : pr.below < κ.lrec .inTab) (hci
      : 1 ≤ κ.lcap .inTab) :
    ∃ L' c, evalF κ initStepP.body s L = .ok {
      s with
      nodes := ((s.nodes.push {
        height := pr.h
      }).modify s.nodes.size (chainNew s.P pr)).modify pr.below (fun n => {
        n with
        inTables := [s.nodes.size]
        livePar := s.nodes.size
      })
      prep := some (prepNext s.P pr s.nodes.size)
    } L' c ∧ L' "done" = 0 ∧ c ≤ 400 := by
  have e1 := isPre_ok (κ := κ) (L := L) hp (fun h => absurd h h1)
  rw [ite_eq_right h1, ite_eq_right h1] at e1
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := isL L pr) (x := "ctr") (e := .bin .shl 1
    (.prm .beta - 1))
    (v := 1 <<< (s.P.beta - 1)) (by
      simp [Exp.ev, Machine.BinOp.eval, PF.get, hb1, Nat.shiftLeft_eq])
  obtain ⟨c3, e3, hc3⟩ := isNode_ok (κ := κ) (S := s) (L := L) (pr := pr) hN hrc hrt hcc hct
  set v := s.nodes.size
  set L3 := upd (isL2 L pr s.P.beta) "v" v
  have h3 : L3 "h" = pr.h ∧ L3 "v" = v ∧ L3 "bl" = pr.below ∧ L3 "tg" = pr.tag ∧
      L3 "ctr" = 1 <<< (s.P.beta - 1) := by simp [L3, isL2, isL, Machine.State.upd]
  obtain ⟨h3h, h3v, h3bl, h3tg, h3ctr⟩ := h3
  have hbs' : pr.below < (nodeS s pr).nodes.size := by simp [nodeS]; omega
  obtain ⟨c4, e4, hc4⟩ := isLink_mid (κ := κ) (S := nodeS s pr) (L := L3) (v := v) (bl := pr.below)
    (by
      rw [h3h]
      exact h1) h3v h3bl hbs' hbr  hci
  set S4 : Core := {
    nodeS s pr with
    nodes := (nodeS s pr).nodes.modify pr.below fun n => {
      n with
      inTables := [v]
      livePar := v
    }
  }
  have hp4 : S4.prep = some pr := hp
  obtain ⟨c5, e5, hc5⟩ := isUp_ok (κ := κ) (S := S4) (L := L3) (pr := pr) (v := v) hp4 h3h h3v
    h3tg h3ctr hh0 hw htag
  have e6 := evalF_assign_ok (κ := κ) (s := {
    S4 with
    prep := some (prepNext S4.P pr v)
  }) (L :=
    L3) (x := "done")
    (e := (0 : Exp)) (v := 0) rfl
  have hc : ("h" ≤ₑ .prm .H : Exp).ev κ s (isL L pr) = some 1 := by
    simp [Exp.ev, isL, Machine.State.upd, Machine.BinOp.eval,
      PF.get, hH]
  have hfin : ({
    S4 with
    prep := some (prepNext S4.P pr v)
  } : Core) = {
    s with
    nodes := ((s.nodes.push {
      height := pr.h
    }).modify s.nodes.size (chainNew s.P pr)).modify pr.below (fun n => {
      n with
      inTables := [s.nodes.size]
      livePar := s.nodes.size
    })
    prep := some (prepNext s.P pr s.nodes.size)
  } := rfl
  rw [hfin] at e6
  exact ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, OF.get, hp, b2n]) one_ne_zero
    (evalF_seq_ok2 e1 (evalF_ite_t hc one_ne_zero (evalF_seq_ok2 a2 (evalF_seq_ok2 e3
      (evalF_seq_ok2 e4
      (evalF_seq_ok2 e5 e6)))))), by simp [Machine.State.upd], by
        simp [Exp.cost] at hc3 hc4 hc5 ⊢
        omega⟩

theorem initStepP_first {κ : Caps} {s : Core} {L : Loc} {pr : Prep} (hp : s.prep = some pr) (h1
  : pr.h = 1)
    (hH : 1 ≤ s.P.H) (htag : pr.tag < 1) (hb1 : 1 ≤ s.P.beta)
    (hn : s.nodes = #[default]) (hpa : s.path = #[]) (hci : s.cin = #[]) (hlp : s.lpar = #[])
    (hw : 1 < κ.pw) (hN : 1 < κ.tbl .N) (hrc : 1 < κ.lrec .children) (hrt : 1 < κ.lrec .table)
    (hcc : 1 ≤ κ.lcap .children) (hct : 1 ≤ κ.lcap .table) (hcr : pr.chunk < κ.lrec .cin) (hcl :
      1 ≤ κ.lcap .cin)
    (hca : pr.chunk < κ.arr .lpar) :
    ∃ L' c, evalF κ initStepP.body s L = .ok {
      s with
      nodes := (#[default].push {
        height := 1
      }).modify 1 (chainNew s.P pr)
      path := #[]
      cin := ((#[] : Array (List Nat)).setX pr.chunk []).setX pr.chunk [1]
      lpar := (#[] : Array Nat).setX pr.chunk 1
      prep := some (prepNext s.P pr 1)
    } L' c ∧ L' "done" = 0 ∧ c ≤ 400 := by
  have e1 := isPre_ok (κ := κ) (L := L) hp (fun _ => hcr)
  rw [ite_eq_left h1, ite_eq_left h1] at e1
  set S0 : Core := {
    s with
    cin := s.cin.setX pr.chunk []
  }
  have a2 := evalF_assign_ok (κ := κ) (s := S0) (L := isL L pr) (x := "ctr") (e := .bin .shl 1
    (.prm .beta - 1))
    (v := 1 <<< (s.P.beta - 1)) (by
      simp [Exp.ev, Machine.BinOp.eval, PF.get, hb1, Nat.shiftLeft_eq, S0])
  have hS0n : S0.nodes.size = 1 := by simp [S0, hn]
  obtain ⟨c3, e3, hc3⟩ := isNode_ok (κ := κ) (S := S0) (L := L) (pr := pr) (by omega) (by omega)
    (by omega) hcc hct
  rw [hS0n] at e3
  set L3 := upd (isL2 L pr S0.P.beta) "v" 1
  have h3 : L3 "h" = 1 ∧ L3 "v" = 1 ∧ L3 "c" = pr.chunk ∧ L3 "tg" = pr.tag ∧
      L3 "ctr" = 1 <<< (s.P.beta - 1) := by simp [L3, isL2, isL, Machine.State.upd, h1, S0]
  obtain ⟨h3h, h3v, h3c, h3tg, h3ctr⟩ := h3
  obtain ⟨c4, e4, hc4⟩ := isLink_first (κ := κ) (S := nodeS S0 pr) (L := L3) (v := 1) (c :=
    pr.chunk) h3h h3v h3c
    hcr hcl hca
  set S4 := linkFirstS (nodeS S0 pr) pr.chunk 1
  have hp4 : S4.prep = some pr := hp
  obtain ⟨c5, e5, hc5⟩ := isUp_ok (κ := κ) (S := S4) (L := L3) (pr := pr) (v := 1) hp4 (by
    rw [h3h, h1]) h3v h3tg
    h3ctr (by omega) (by
      rw [h1]
      exact hw) (by
      rw [h1]
      simpa using htag)
  have e6 := evalF_assign_ok (κ := κ) (s := {
    S4 with
    prep := some (prepNext S4.P pr 1)
  }) (L :=
    L3) (x := "done")
    (e := (0 : Exp)) (v := 0) rfl
  have hfin : ({
    S4 with
    prep := some (prepNext S4.P pr 1)
  } : Core) = {
    s with
    nodes := (#[default].push {
      height := 1
    }).modify 1 (chainNew s.P pr)
    path := #[]
    cin := ((#[] : Array (List Nat)).setX pr.chunk []).setX pr.chunk [1]
    lpar := (#[] : Array Nat).setX pr.chunk 1
    prep := some (prepNext s.P pr 1)
  } := by
    simp only [S4, linkFirstS, nodeS, S0, hn, hpa, hci, hlp, setX_setX, h1]
    rfl
  have hc : ("h" ≤ₑ .prm .H : Exp).ev κ S0 (isL L pr) = some 1 := by
    simp [Exp.ev, isL, Machine.State.upd, Machine.BinOp.eval,
      PF.get, h1, S0, hH]
  have e := evalF_ite_t (c := .opt .prepOn) (v := 1) (f := "done" ::= 1) (by
    simp [Exp.ev, OF.get, hp, b2n]) one_ne_zero
    (evalF_seq_ok2 e1 (evalF_ite_t (f := isFinish) hc one_ne_zero (evalF_seq_ok2 a2
      (evalF_seq_ok2 e3
      (evalF_seq_ok2 e4 (evalF_seq_ok2 e5 e6))))))
  rw [hfin] at e
  exact ⟨_, _, e, by simp [Machine.State.upd], by simp [Exp.cost] at hc3 hc4 hc5 ⊢; omega⟩

/-! ### `initStep` along Level F's stages -/

/-- The program agrees with Level F's `initStep` from `s` (within `D` steps). -/
def ISAgree (κ : Caps) (s : Core) (D : Nat) : Prop :=
  ∀ b s', initStep.run s = .ok b s' →
    ∃ L' c, evalF κ initStepP.body s (Machine.State.setLocs (fun _ => 0) [] []) = .ok s' L' c ∧
      L' "done" = b2n b ∧ c ≤ D

/-- The capacities the construction needs. -/
structure InitCaps (κ : Caps) (P : Params) : Prop where
  pw : κ.pw = P.H + 1
  N : P.H + 2 ≤ κ.tbl .N
  C : 2 ≤ κ.tbl .C
  rc : P.H + 2 ≤ κ.lrec .children
  rt : P.H + 2 ≤ κ.lrec .table
  ri : P.H + 2 ≤ κ.lrec .inTab
  rcin : 2 ≤ κ.lrec .cin
  alp : 2 ≤ κ.arr .lpar
  cc : 1 ≤ κ.lcap .children
  ct : 1 ≤ κ.lcap .table
  ci : 1 ≤ κ.lcap .inTab
  ccin : 1 ≤ κ.lcap .cin

theorem isAgree_stage {κ : Caps} {P : Params} {h : Nat} {s : Core} (S : Stage P h s) (h1 : 1 ≤ h)
    (hle : h ≤ P.H + 1) (hb : 1 ≤ P.beta) (hH : 1 ≤ P.H) (hK : InitCaps κ P)
    (hfirst : h = 1 → s.nodes = #[default] ∧ s.path = #[] ∧ s.cin = #[] ∧ s.lpar = #[]) :
    ISAgree κ s 400 := by
  intro b s' hr
  have hP := S.P
  obtain ⟨pa, hp, hsz, hpa⟩ := S.pr
  set pr : Prep := {
    chunk := 1
    h := h
    below := if h = 1 then 1 else h - 1
    tag := chainTag P (h - 1)
    path := pa
  }
  by_cases e1 : h = 1
  · obtain ⟨hn, hpth, hci, hlp⟩ := hfirst e1
    have hpr1 : pr.h = 1 := e1
    have hrun := initStep_first s pr hp hpr1 (by
      rw [hP]
      exact hH)
    rw [hrun] at hr; injection hr with hb' hs'; subst hb'; subst hs'
    obtain ⟨L', c, ev, hd, hc⟩ := initStepP_first (κ := κ) (L := Machine.State.setLocs (fun _ =>
      0) [] []) hp hpr1
      (by
        rw [hP]
        exact hH) (by simp [pr, e1, chainTag]) (by
        rw [hP]
        exact hb) hn hpth hci hlp
      (by
        rw [hK.pw]
        omega) (by
        have := hK.N
        omega) (by
        have := hK.rc
        omega) (by
        have := hK.rt
        omega) hK.cc hK.ct
      (by
        have := hK.rcin
        simp [pr]
        omega) hK.ccin (by
        have := hK.alp
        simp [pr]
        omega)
    exact ⟨L', c, ev, by simp [hd, b2n], by omega⟩
  · by_cases e2 : h ≤ P.H
    · have hsn : s.nodes.size = h := S.nsz (by omega)
      have hrun := initStep_mid s pr hp e1 (by
        rw [hP]
        exact e2)
      rw [hrun] at hr; injection hr with hb' hs'; subst hb'; subst hs'
      obtain ⟨L', c, ev, hd, hc⟩ := initStepP_mid (κ := κ) (L := Machine.State.setLocs (fun _ =>
        0) [] []) hp e1
        (by
          rw [hP]
          exact e2) (by
          simp [pr]
          omega) (by
          rw [hP]
          exact chainTag_lt hb _) (by
          rw [hP]
          exact hb)
        (by
          simp [pr, e1, hsn]
          omega) (by
            rw [hK.pw]
            simp [pr]
            omega) (by
            rw [hsn]
            have := hK.N
            omega)
        (by
          rw [hsn]
          have := hK.rc
          omega) (by
          rw [hsn]
          have := hK.rt
          omega) hK.cc hK.ct
        (by
          have := hK.ri
          simp [pr, e1]
          omega) hK.ci
      exact ⟨L', c, ev, by simp [hd, b2n], hc⟩
    · have e3 : h = P.H + 1 := by omega
      have hCs : s.C.size = 2 := by rw [S.low.Csize]; rfl
      have hrun := initStep_last s pr hp e1 (by
        rw [hP]
        simp [pr]
        omega)
      rw [hrun] at hr; injection hr with hb' hs'; subst hb'; subst hs'
      obtain ⟨L', c, ev, hd, hc⟩ := initStepP_last (κ := κ) (L := Machine.State.setLocs (fun _
        => 0) [] []) hp e1
        (by
          rw [hP]
          simp [pr]
          omega) (by simp [pr, hCs])
      exact ⟨L', c, ev, by simp [hd, b2n], by omega⟩

/-! ### The eager construction loop -/

/-- The body of Level F's construction loop (as elaborated). -/
def initF : Nat → PUnit → CM (ForInStep PUnit) := fun _ _ => do
  let b ← initStep
  if b = true then pure (ForInStep.done PUnit.unit) else pure (ForInStep.yield PUnit.unit)

/-- Run one preparation step unless an earlier iteration finished initialization. -/
def initLoopBody : Stm := cm{ if dn = 0 then { d ← initStepP(); if d then dn := 1 } }
/-- Complete eager preparation in at most the configured height plus one iterations. -/
def initLoopS : Stm := cm{ dn := 0; for ii < P.H + 1 do initLoopBody }

theorem initLoopS_agree (κ : Caps) (s : Core) (L : Loc) {D : Nat} (I : Nat → Core → Prop) (h0 :
  I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.H + 1 → ∃ b t', initStep.run t = .ok b t' ∧ (b = false → I
      (j + 1) t') ∧
      ISAgree κ t D ∧ t'.P = s.P) :
    ∃ t' L' n, (forIn (List.range (s.P.H + 1)) PUnit.unit initF).run s = .ok () t' ∧
      evalF κ initLoopS s L = .ok t' L' n ∧ n ≤ 10 + (s.P.H + 1) * (D + 12) := by
  set K := s.P.H + 1
  set R := fun (l : List Nat) (t : Core) => (forIn l PUnit.unit initF).run t
  have hF : ∀ (n j : Nat) (t : Core), I j t → j + n = K → ∃ tF, R ((List.range K).drop j) t =
    .ok () tF := by
    intro n; induction n with
    | zero =>
      intro j t _ hj; refine ⟨t, ?_⟩
      simp only [R, show j = K by omega]; rw [List.drop_of_length_le (by simp)]; rfl
    | succ n ih =>
      intro j t hI hj
      have hjK : j < K := by omega
      rw [List.drop_eq_getElem_cons (by simpa using hjK), List.getElem_range]
      obtain ⟨b, t', hr, hI', -, -⟩ := hstep j t hI hjK
      cases b
      · obtain ⟨tF, h⟩ := ih (j + 1) t' (hI' rfl) (by omega)
        exact ⟨tF, by
          simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, initF, hr]; exact h⟩
      · exact ⟨_, by
          simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, initF, hr]
          rfl⟩
  obtain ⟨tF, hR0⟩ := hF K 0 s h0 (by omega)
  simp only [List.drop_zero] at hR0
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "dn") (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨S', L', c, he, hc, hI⟩ := evalF_loop (κ := κ) (x := "ii") (n := .prm .H + 1) (b :=
    initLoopBody) (s := s)
    (L := upd L "dn" 0) (N := K) (by simp [Exp.ev, PF.get, K, Machine.BinOp.eval])
    (fun j S L' => (L' "dn" = 0 ∧ I j S ∧ R ((List.range K).drop j) S = .ok () tF) ∨ (L' "dn" =
      1 ∧ S = tF)) (D + 11)
    (Or.inl ⟨by simp [Machine.State.upd], h0, by simpa using hR0⟩)
    (by
      intro j hj S L1 hcase
      set L2 := upd L1 "ii" j
      rcases hcase with ⟨hdn, hIj, hR⟩ | ⟨hdn, hSF⟩
      · have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 1 := by simp [Exp.ev, Machine.BinOp.eval, L2,
          Machine.State.upd, hdn]
        obtain ⟨b, t', hr, hI', hA, -⟩ := hstep j S hIj hj
        obtain ⟨Lg, ng, eg, hd, hng⟩ := hA b t' hr
        have ec := evalF_call_ok (q := initStepP) (args := []) (ds := ["d"]) (L := L2) (by
          simp [evList]) eg
        set L3 := Machine.State.setLocs L2 ["d"] (initStepP.rets.map Lg)
        have h3d : L3 "d" = b2n b := by
          simp [L3, initStepP, Machine.State.setLocs, Machine.State.upd, hd]
        have h3dn : L3 "dn" = 0 := by
          simp [L3, L2, initStepP, Machine.State.setLocs, Machine.State.upd, hdn]
        rw [List.drop_eq_getElem_cons (by simpa using hj), List.getElem_range] at hR
        cases b
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, initF, hr] at hR
          refine ⟨t', _, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 ec (evalF_ite_f
            (by simp [Exp.ev, h3d, b2n]) evalF_skip)), ?_, Or.inl ⟨h3dn, hI' rfl, hR⟩⟩
          simp [Exp.cost, costList] at hng ⊢; omega
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, initF, hr] at hR
          injection hR with _ hT; subst hT
          have e4 := evalF_assign_ok (κ := κ) (s := t') (L := L3) (x := "dn") (e := (1 : Exp))
            (v := 1) rfl
          refine ⟨t', _, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 ec (evalF_ite_t (v := 1)
            (by
              simp [Exp.ev, h3d, b2n]) one_ne_zero e4)), ?_, Or.inr ⟨by simp [Machine.State.upd],
              rfl⟩⟩
          simp [Exp.cost, costList] at hng ⊢; omega
      · subst hSF
        have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 0 := by simp [Exp.ev, Machine.BinOp.eval, L2,
          Machine.State.upd, hdn]
        exact ⟨S, L2, _, evalF_ite_f hc0 evalF_skip, by simp [Exp.cost],
          Or.inr ⟨by simp [L2, Machine.State.upd, hdn], rfl⟩⟩)
  have hS' : S' = tF := by
    rcases hI with ⟨hdn, hIK, hR⟩ | ⟨hdn, h⟩
    · rw [List.drop_of_length_le (by simp)] at hR
      simp only [R] at hR
      injection hR
    · exact h
  subst hS'
  refine ⟨S', L', _, hR0, evalF_seq_ok2 a1 he, ?_⟩
  have e : K * (1 + (D + 11)) = K * (D + 12) := by ring
  simp only [Exp.cost] at hc ⊢; omega

/-! ### `initCore` -/

/-- `initCore lz` (local `lz`), from fresh memory. -/
def initCoreS : Stm := cm{
  initStateS; prepInit(1, 1)
  if lz then S.notReady := 1 else { initLoopS; S.notReady := 0 } }

/-- The state after `prepInit 1 1` on `initState P`. -/
def prepStart (P : Params) (r : Bool) : Core :=
  {
    initState P with
    prep := some {
      chunk := 1
      below := 1
      path := Array.replicate (P.H + 1) NIL
    }
    ready := r
  }

theorem prepInit_ok {κ : Caps} {P : Params} {L : Loc} (hK : InitCaps κ P) :
    evalF κ (.prepInit 1 1) (initState P) L = .ok (prepStart P true) L 18 := by
  have hz : rowZero κ (initState P) 1 := fun j _ => by
    change ((#[] : Array (Array Nat)).getX 1).getX j = 0
    rfl
  have hc : (initState P).prep.isNone = true ∧ 1 < κ.tbl .C ∧ rowZero κ (initState P) 1 ∧
      (initState P).P.H + 1 ≤ κ.pw := ⟨rfl, by have := hK.C; omega, hz, by rw [hK.pw]; rfl⟩
  simp only [evalF, Exp.ev]
  rw [ite_eq_left hc]
  rfl

theorem initCoreS_lazy {κ : Caps} {P : Params} {L : Loc} (hL : L "lz" = 1) (hBe : 1 ≤
  P.elementBits) (hBg : 1 ≤ P.groupBits)
    (hK : InitCaps κ P) (hE : 2 ≤ κ.tbl .E) (hG : 2 ≤ κ.tbl .G) :
    ∃ L' c, evalF κ initCoreS (freshC P) L = .ok (prepStart P false) L' c ∧ c ≤ 400 := by
  obtain ⟨L1, c1, e1, hc1, hF1⟩ := initStateS_ok (κ := κ) (P := P) (L := L) hBe hBg hE hG hK.C
    (by
      have := hK.N
      omega)
  have e2 := prepInit_ok (κ := κ) (P := P) (L := L1) hK
  have e3 : evalF κ (.wr (.s .notReady) 0 1) (prepStart P true) L1 = .ok (prepStart P false) L1
    3 := by
    simp [evalF, Exp.ev, Fld.set, SF.ok, SF.set, prepStart, Exp.cost]
  have hlz : L1 "lz" = 1 := by rw [hF1 _ (by decide), hL]
  exact ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_ite_t (v := 1) (by simp [Exp.ev, hlz])
    one_ne_zero e3)),
    by simp [Exp.cost]; omega⟩

theorem initCore_lazy_eq (s : Core) : (initCore true).run s = .ok () (prepStart s.P false) := by
  rw [OrderMaintenance.Proof.Top.initCore_lazy_run]; rfl

theorem initCoreS_eager {κ : Caps} {P : Params} {L : Loc} (hL : L "lz" = 0) (hBe : 1 ≤
  P.elementBits) (hBg : 1 ≤ P.groupBits)
    (hb : 1 ≤ P.beta) (hH : 1 ≤ P.H) (hK : InitCaps κ P) (hE : 2 ≤ κ.tbl .E) (hG : 2 ≤ κ.tbl .G)
    {s s' : Core} (hsP : s.P = P) (h : (initCore false).run s = .ok () s') :
    ∃ L' c, evalF κ initCoreS (freshC P) L = .ok s' L' c ∧ c ≤ 1000 + (P.H + 1) * 412 := by
  obtain ⟨L1, c1, e1, hc1, hF1⟩ := initStateS_ok (κ := κ) (P := P) (L := L) hBe hBg hE hG hK.C
    (by
      have := hK.N
      omega)
  have e2 := prepInit_ok (κ := κ) (P := P) (L := L1) hK
  have hlz : L1 "lz" = 0 := by rw [hF1 _ (by decide), hL]
  -- Level F's loop, along the stages
  have S1 := stage_one (initState P) true
  have hs0 : prepStart P true = {
    initState (initState P).P with
    prep := some {
      chunk := 1
      below := 1
      path := Array.replicate ((initState P).P.H + 1) NIL
    }
    ready := true
  } := rfl
  obtain ⟨t', L2, n2, hR, e3, hn3⟩ := initLoopS_agree κ (prepStart P true) L1 (D := 400)
    (fun j t => Stage P (j + 1) t ∧ (j = 0 → t = prepStart P true))
    ⟨by rw [hs0]; exact S1, fun _ => rfl⟩
    (by
      intro j t ⟨St, h0⟩ hj
      have hjP : j < P.H + 1 := hj
      have hA : ISAgree κ t 400 := isAgree_stage St (by omega) (by omega) hb hH hK (fun e => by
        have := h0 (by omega); subst this; exact ⟨rfl, rfl, rfl, rfl⟩)
      by_cases hle : j + 1 ≤ P.H
      · obtain ⟨t', hr, St', -⟩ := stage_next St (by omega) hle hb
        exact ⟨false, t', hr, fun _ => ⟨St', fun e => absurd e (by omega)⟩, hA, by rw [St'.P]; rfl⟩
      · have e : j + 1 = P.H + 1 := by omega
        rw [e] at St
        obtain ⟨t', hr, F, -⟩ := stage_last St hH
        exact ⟨true, t', hr, fun h => absurd h (by simp), hA, by rw [F.low.rest.1]; rfl⟩)
  -- Level F's result
  have hEq : (initCore false).run s = ((forIn (List.range (P.H + 1)) PUnit.unit initF) >>=
      fun _ => (modify fun t => {
        t with
        ready := true
      } : CM PUnit)).run (prepStart P true) := by
    rw [OrderMaintenance.Proof.Top.initCore_eager_eq, hsP]; rfl
  have hR' : (forIn (List.range (P.H + 1)) PUnit.unit initF).run (prepStart P true) = .ok () t'
    := hR
  have hF : (initCore false).run s = .ok () {
    t' with
    ready := true
  } := by
    rw [hEq, OrderMaintenance.Proof.run_bind, hR']; rfl
  rw [hF] at h; injection h with _ h; subst h
  have e4 : evalF κ (.wr (.s .notReady) 0 0) t' L2 = .ok {
    t' with
    ready := true
  } L2 3 := by
    simp [evalF, Exp.ev, Fld.set, SF.ok, SF.set, Exp.cost]
  exact ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_ite_f (by simp [Exp.ev, hlz])
    (evalF_seq_ok2 e3 e4))),
    by simp [Exp.cost, prepStart, initState] at hn3 ⊢; omega⟩

/-! ### `prepareStep` -/

/-- `r := prepareStep`. -/
def prepP : Proc where
  name := "prepareStep"
  params := []
  rets := ["r"]
  body := cm{
    if ‹.rd (.s .notReady) 0› then { d ← initStepP(); if d then S.notReady := 0 }
    r := !‹.rd (.s .notReady) 0› }

theorem prepP_agree {κ : Caps} {s : Core} {L : Loc} {D : Nat} (hA : s.ready = false → ISAgree κ s D)
    (hrd : ∀ b s1, initStep.run s = .ok b s1 → s1.ready = s.ready)
    {r : Bool} {s' : Core} (h : prepareStep.run s = .ok r s') :
    ∃ L' c, evalF κ prepP.body s L = .ok s' L' c ∧ L' "r" = b2n r ∧ c ≤ D + 40 := by
  unfold prepareStep at h
  cases hr : s.ready
  · simp only [OrderMaintenance.Proof.run_get_bind, hr, Bool.not_false, ite_true] at h
    obtain ⟨b, s1, h1, h2⟩ := run_bind_ok h
    have hr1 := hrd b s1 h1
    obtain ⟨Lg, cg, eg, hd, hcg⟩ := hA hr b s1 h1
    have ec := evalF_call_ok (q := initStepP) (args := []) (ds := ["d"]) (L := L) (by
      simp [evList]) eg
    set L1 := Machine.State.setLocs L ["d"] (initStepP.rets.map Lg)
    have h1d : L1 "d" = b2n b := by
      simp [L1, initStepP, Machine.State.setLocs, Machine.State.upd, hd]
    cases b
    · change EStateM.Result.ok s1.ready s1 = EStateM.Result.ok r s' at h2
      rw [hr1, hr] at h2
      injection h2 with hrr hss
      subst r
      subst s'
      have e2 := evalF_assign_ok (κ := κ) (s := s1) (L := L1) (x := "r") (e := !ₑ (.rd (.s
        .notReady) 0)) (v := 0)
        (by
          simp [Exp.ev, Fld.cap, Fld.get, SF.get, hr1, hr, b2n, Machine.UnOp.eval])
      refine ⟨_, _, evalF_seq_ok2 (evalF_ite_t (v := 1) (by
        simp [Exp.ev, Fld.cap, Fld.get, SF.get, hr, b2n])
        one_ne_zero (evalF_seq_ok2 ec (evalF_ite_f (by simp [Exp.ev, h1d, b2n]) evalF_skip))) e2,
        by simp [Machine.State.upd,   b2n], ?_⟩
      simp [Exp.cost, costList] at hcg ⊢; omega
    · change EStateM.Result.ok true { s1 with ready := true } =
          EStateM.Result.ok r s' at h2
      injection h2 with hrr hss
      subst r
      subst s'
      have e3 : evalF κ (.wr (.s .notReady) 0 0) s1 L1 = .ok {
        s1 with
        ready := true
      } L1 3 := by
        simp [evalF, Exp.ev, Fld.set, SF.ok, SF.set, Exp.cost]
      have e2 := evalF_assign_ok (κ := κ) (s := {
        s1 with
        ready := true
      }) (L := L1) (x := "r")
        (e := !ₑ (.rd (.s .notReady) 0)) (v := 1)
        (by
          simp [Exp.ev, Fld.cap, Fld.get, SF.get, b2n, Machine.UnOp.eval])
      refine ⟨_, _, evalF_seq_ok2 (evalF_ite_t (v := 1) (by
        simp [Exp.ev, Fld.cap, Fld.get, SF.get, hr, b2n])
        one_ne_zero (evalF_seq_ok2 ec (evalF_ite_t (v := 1) (by simp [Exp.ev, h1d, b2n])
          one_ne_zero e3))) e2,
        by simp [Machine.State.upd, b2n], ?_⟩
      simp [Exp.cost, costList] at hcg ⊢; omega
  · simp only [OrderMaintenance.Proof.run_get_bind, hr, Bool.not_true, Bool.false_eq_true,
    ite_false] at h
    change EStateM.Result.ok true s = EStateM.Result.ok r s' at h
    injection h with hrr hss
    subst r
    subst s'
    have e2 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "r") (e := !ₑ (.rd (.s
      .notReady) 0)) (v := 1)
      (by
        simp [Exp.ev, Fld.cap, Fld.get, SF.get, hr, b2n, Machine.UnOp.eval])
    refine ⟨_, _, evalF_seq_ok2 (evalF_ite_f (by
      simp [Exp.ev, Fld.cap, Fld.get, SF.get, hr, b2n]) evalF_skip) e2,
      by simp [Machine.State.upd,  b2n], ?_⟩
    simp [Exp.cost]

end OrderMaintenance.Impl
