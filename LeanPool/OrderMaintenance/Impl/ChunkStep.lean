/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.GroupStep
public import LeanPool.OrderMaintenance.Proof.Cost.CDrive


/-!
# M6: chunk split steps (`removeChunk`, `moveUnit`, `chunkSplitStep`, `driveChunk`)

As for groups, the agreement lemmas cover the cases Level F's cost proof uses, and reach the states
it names (`cremoveState`, `cmoveLState`, `cmoveRState`). A unit has at most three groups, kept in
locals.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)
open OrderMaintenance.Proof.Top (getX_modify')

local notation "upd" => Machine.State.upd

/-! ### `removeChunk` -/

theorem pqEnterIfAbove_noop {σ : Core} {c : Nat} (h : (σ.C.getX c).size ≤ σ.P.theta) :
    (pqEnterIfAbove c).run σ = .ok () σ := by
  unfold pqEnterIfAbove
  simp [
    Nat.not_lt.mpr h]

/-- Test whether a chunk is an overflow sibling of the source in local `x`. -/
def cquietE (y : Reg) : Exp := cme{ C[‹y›].st = 1 && C[‹y›].src = x }
/-- Release an overflow sibling to the quiet state and reconsider its queue entry. -/
def cquietS (y : Reg) : Stm :=
  cm{ if ‹cquietE y› then { C[‹y›].st := 0; C[‹y›].src := 0; call pqEnterIfAboveP(‹y›) } }

/-- `removeChunk x`: `x` is dead, its overflow siblings quiet (and offered to the queue). -/
def removeChunkS : Stm := cm{
  C[x].st := 3; xl := C[x].l; xr := C[x].r; ‹cquietS "xl"›; ‹cquietS "xr"› }

theorem cquietS_ok {κ : Caps} {S0 : Core} {L : Loc} {y : Reg} {j x : Nat} (hy : L y = j) (hx : L
  "x" = x)
    (hst : (S0.C.getX j).st = .overflow) (hsrc : (S0.C.getX j).src = x) (hsz : (S0.C.getX
      j).size ≤ S0.P.theta)
    (hj : j < S0.C.size) (hjT : j < κ.tbl .C) :
    ∃ n, evalF κ (cquietS y) S0 L = .ok {
      S0 with
      C := S0.C.modify j OrderMaintenance.Proof.quietC
    } L n ∧ n ≤ 50 := by
  have hv : ∀ s' : Core, (Exp.var y).ev κ s' L = some j := fun _ => by simp [Exp.ev, hy]
  have w1 := evalF_wrC_ok (κ := κ) (s := S0) (L := L) (k := .st) (e := (0 : Exp)) (w := 0) (hv
    _) rfl hj  rfl
  have w2 := evalF_wrC_ok (κ := κ) (s := {
    S0 with
    C := S0.C.modify j (CF.set · 0 .st)
  }) (L :=
    L) (k := .src)
    (e := (0 : Exp)) (w := 0) (hv _) rfl (by simp [hj])  rfl
  have hfin : (S0.C.modify j (CF.set · 0 .st)).modify j (CF.set · 0 .src) = S0.C.modify j
    OrderMaintenance.Proof.quietC := by
    rw [Array.modify_modify_same]; rfl
  rw [hfin] at w2
  set S2 : Core := {
    S0 with
    C := S0.C.modify j OrderMaintenance.Proof.quietC
  }
  have hsz2 : (S2.C.getX j).size ≤ S2.P.theta := by
    simp only [S2, getX_modify', hj, and_self, ite_true]; exact hsz
  obtain ⟨Lq, cq, eq, hcq⟩ := pqEnterIfAbove_agree κ S2 (Machine.State.setLocs (fun _ => 0)
    ["c"] [j]) (c := j)
    (by simp [Machine.State.setLocs,
      Machine.State.upd]) hjT hsz2 (pqEnterIfAbove_noop hsz2)
  have ec := evalF_call_ok (q := pqEnterIfAboveP) (args := [.var y]) (ds := []) (L := L) (by
    simp [evList, Exp.ev, hy]) eq
  have hc : (cquietE y).ev κ S0 L = some 1 := by
    simp [cquietE, Exp.cF, Exp.ev, Machine.BinOp.eval, hy, hx, hjT, Fld.cap,
      Fld.get, CF.get, hst, hsrc]; rfl
  refine ⟨_, evalF_ite_t hc one_ne_zero (evalF_seq_ok2 (by
          simp only [Stm.wcF]
          exact w1)
    (evalF_seq_ok2 (by
          simp only [Stm.wcF]
          exact w2) ec)), ?_⟩
  simp [Exp.cost, cquietE, Exp.cF, costList] at hcq ⊢; omega

open OrderMaintenance.Proof in
theorem removeChunkS_agree (κ : Caps) (s : Core) (L : Loc) {x : Nat} (hx : L "x" = x)
    (hlr : cLl s x ≠ cRr s x) (hlx : cLl s x ≠ x) (hrx : cRr s x ≠ x) (hxs : x < s.C.size)
    (hl : cSt s (cLl s x) = .overflow ∧ cSrc s (cLl s x) = x)
    (hr : cSt s (cRr s x) = .overflow ∧ cSrc s (cRr s x) = x)
    (hszl : cSz s (cLl s x) ≤ s.P.theta) (hszr : cSz s (cRr s x) ≤ s.P.theta)
    (hlS : cLl s x < s.C.size) (hrS : cRr s x < s.C.size) (hC : s.C.size ≤ κ.tbl .C) :
    ∃ L' n, evalF κ removeChunkS s L = .ok (cremoveState s x) L' n ∧ n ≤ 150 := by
  set l := cLl s x
  set r := cRr s x
  have hxT : x < κ.tbl .C := by omega
  have w1 := evalF_wrC_ok (κ := κ) (s := s) (L := L) (k := .st) (i := .var "x") (e := (3 : Exp))
    (j := x) (w := 3)
    (by simp [Exp.ev, hx]) rfl hxs  rfl
  set S1 : Core := {
    s with
    C := s.C.modify x (CF.set · 3 .st)
  }
  have hd : s.C.modify x (CF.set · 3 .st) = s.C.modify x deadC := Array.modify_congr_getX _ _ _
    _ rfl
  have g1 : ∀ z, z ≠ x → S1.C.getX z = s.C.getX z := by
    intro z hz; simp only [S1, getX_modify']; rw [ite_eq_right (fun h => hz h.1)]
  have g1x : (S1.C.getX x).l = l ∧ (S1.C.getX x).r = r := by
    simp only [S1, getX_modify', hxs, and_self, ite_true]; exact ⟨rfl, rfl⟩
  have a2 := evalF_assign_ok (κ := κ) (s := S1) (L := L) (x := "xl") (e := .cF .l "x") (v := l)
    (by simp [Exp.cF, Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, g1x.1])
  have a3 := evalF_assign_ok (κ := κ) (s := S1) (L := upd L "xl" l) (x := "xr") (e := .cF .r
    "x") (v := r)
    (by simp [Exp.cF, Exp.ev, Machine.State.upd, hx, hxT, Fld.cap, Fld.get,
      CF.get, g1x.2])
  set L3 := upd (upd L "xl" l) "xr" r
  obtain ⟨n4, e4, hn4⟩ := cquietS_ok (κ := κ) (S0 := S1) (L := L3) (y := "xl") (j := l) (x := x)
    (by simp [L3,
      Machine.State.upd]) (by simp [L3, Machine.State.upd, hx])
    (by rw [g1 l hlx]; exact hl.1) (by rw [g1 l hlx]; exact hl.2) (by rw [g1 l hlx]; exact hszl)
    (by simp [S1, hlS]) (by omega)
  set S2 : Core := {
    S1 with
    C := S1.C.modify l quietC
  }
  have g2 : (S2.C.getX r) = s.C.getX r := by
    simp only [S2, getX_modify']; rw [ite_eq_right (fun h => hlr h.1.symm), g1 r hrx]
  obtain ⟨n5, e5, hn5⟩ := cquietS_ok (κ := κ) (S0 := S2) (L := L3) (y := "xr") (j := r) (x := x)
    (by simp [L3,
      Machine.State.upd]) (by simp [L3, Machine.State.upd, hx])
    (by rw [g2]; exact hr.1) (by rw [g2]; exact hr.2) (by rw [g2]; exact hszr) (by simp [S2, S1,
      hrS]) (by omega)
  have hfin : ({
    S2 with
    C := S2.C.modify r quietC
  } : Core) = cremoveState s x := by
    simp only [S2, S1, cremoveState, hd]; rfl
  rw [hfin] at e5
  refine ⟨L3, _, evalF_seq_ok2 (by
          simp only [Stm.wcF]
          exact w1) (evalF_seq_ok2 a2
    (evalF_seq_ok2 a3
    (evalF_seq_ok2 e4 e5))), ?_⟩
  simp only [Exp.cost, Exp.cF] at hn4 hn5 ⊢; omega

/-! ### The unit at an end of a chunk -/

/-- The unit held in locals: `[u0]`, or `[u0, u1, u2]` when `uk = 3`. -/
def unitOf (L : Loc) : List Nat := if L "uk" = 1 then [L "u0"] else [L "u0", L "u1", L "u2"]

/-- Test whether the left candidate is the source group's left overflow sibling. -/
def unitLE : Exp := cme{ lf && G[sr].l = g0 }
/-- Test whether the right candidate is the source group's right overflow sibling. -/
def unitRE : Exp := cme{ !lf && G[sr].r = g0 }
/-- `unitCand x (lf = 1)` into `uk, u0, u1, u2` (locals `x lf`). -/
def unitS : Stm := cm{
  if lf then g0 := C[x].first else g0 := C[x].last
  uk := 1; u0 := g0
  if G[g0].st = 1 then {
    sr := G[g0].src
    if ‹unitLE› then { uk := 3; u0 := g0; u1 := sr; u2 := G[sr].r }
    else if ‹unitRE› then { uk := 3; u0 := G[sr].l; u1 := sr; u2 := g0 } } }

theorem unitCand_eq (s : Core) (x : Nat) (left : Bool) :
    unitCand s x left =
      (let g0 := if left then (s.C.getX x).first else (s.C.getX x).last
       let G0 := s.Gs.getX g0
       if G0.st = .overflow then
         (let S := s.Gs.getX G0.src
          if left = true ∧ S.l = g0 then [g0, G0.src, S.r]
          else if left = false ∧ S.r = g0 then [S.l, G0.src, g0] else [g0])
       else [g0]) := by
  unfold unitCand
  dsimp only
  by_cases h : (s.Gs.getX (if left = true then (s.C.getX x).first else (s.C.getX x).last)).st =
    St.overflow
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
    cases left <;> simp
  · simp [h]

theorem unitS_ok {κ : Caps} {s : Core} {L : Loc} {x : Nat} {left : Bool} (hx : L "x" = x) (hlf :
  L "lf" = b2n left)
    (hxT : x < κ.tbl .C) (hg0T : (if left then (s.C.getX x).first else (s.C.getX x).last) <
      κ.tbl .G)
    (hsrT : (s.Gs.getX (if left then (s.C.getX x).first else (s.C.getX x).last)).st = .overflow →
      (s.Gs.getX (if left then (s.C.getX x).first else (s.C.getX x).last)).src < κ.tbl .G) :
    ∃ L' n, evalF κ unitS s L = .ok s L' n ∧ unitOf L' = unitCand s x left ∧ (L' "uk" = 1 ∨ L'
      "uk" = 3) ∧
      n ≤ 80 ∧ ∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → r ≠ "u1" → r ≠ "u2" → r ≠ "sr" → L' r = L r
        := by
  set g0 := if left then (s.C.getX x).first else (s.C.getX x).last
  set G0 := s.Gs.getX g0
  have e1 : ∃ c1, evalF κ (.ite "lf" ("g0" ::= .cF .first "x") ("g0" ::= .cF .last "x")) s L =
      .ok s (upd L "g0" g0) c1 ∧ c1 ≤ 6 := by
    cases left
    · exact ⟨_, evalF_ite_f (by simp [Exp.ev, hlf, b2n]) (evalF_assign_ok (by simp [Exp.cF,
        Exp.ev, hx, hxT, Fld.cap,
        Fld.get, CF.get, g0])), by simp [Exp.cost, Exp.cF]⟩
    · exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, hlf, b2n]) one_ne_zero (evalF_assign_ok
        (by simp [Exp.cF,
        Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, g0])), by simp [Exp.cost, Exp.cF]⟩
  obtain ⟨c1, e1, hc1⟩ := e1
  set L1 := upd L "g0" g0
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "uk") (e := (1 : Exp)) (v := 1) rfl
  have a3 := evalF_assign_ok (κ := κ) (s := s) (L := upd L1 "uk" 1) (x := "u0") (e := .var "g0")
    (v := g0)
    (by simp [Exp.ev, L1, Machine.State.upd])
  set L3 := upd (upd L1 "uk" 1) "u0" g0
  have h3 : ∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → L3 r = L r := fun r h1 h2 h3 => by
    simp [L3, L1, Machine.State.upd, h1, h2, h3]
  have h3g0 : L3 "g0" = g0 := by simp [L3, L1, Machine.State.upd]
  have h3lf : L3 "lf" = b2n left := by rw [h3 "lf" (by decide) (by decide) (by decide), hlf]
  have hc4 : (.gF .st "g0" =ₑ 1 : Exp).ev κ s L3 = some (if G0.st.toN = 1 then 1 else 0) := by
    simp [Exp.gF, Exp.ev, Machine.BinOp.eval, h3g0, hg0T, Fld.cap, Fld.get,
      GF.get, G0]
  have hfr3 : ∀ L' : Loc, (∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → r ≠ "u1" → r ≠ "u2" → r ≠ "sr"
    → L' r = L3 r) →
      ∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → r ≠ "u1" → r ≠ "u2" → r ≠ "sr" → L' r = L r :=
    fun L' hL' r h1 h2 hx3 h4 h5 h6 => (hL' r h1 h2 hx3 h4 h5 h6).trans (h3 r h1 h2 hx3)
  by_cases hov : G0.st = .overflow
  · have hc4' : (.gF .st "g0" =ₑ 1 : Exp).ev κ s L3 = some 1 := by rw [hc4, hov]; rfl
    set sr := G0.src
    set S := s.Gs.getX sr
    have a5 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "sr") (e := .gF .src "g0") (v
      := sr)
      (by simp [Exp.gF, Exp.ev, h3g0, hg0T, Fld.cap, Fld.get, GF.get, sr, G0])
    set L5 := upd L3 "sr" sr
    have h5 : L5 "sr" = sr := by simp [L5, Machine.State.upd]
    have h5g0 : L5 "g0" = g0 := by simp [L5, Machine.State.upd, h3g0]
    have h5lf : L5 "lf" = b2n left := by simp [L5, Machine.State.upd, h3lf]
    have hsrT' : sr < κ.tbl .G := hsrT hov
    have hcL : unitLE.ev κ s L5 = some (if left = true ∧ S.l = g0 then 1 else 0) := by
      cases left <;> by_cases e : S.l = g0 <;>
        simp [unitLE, Exp.gF, Exp.ev, Machine.BinOp.eval, h5, h5g0, h5lf, hsrT',
          Fld.cap, Fld.get, GF.get, b2n, e, S]
    have hcR : unitRE.ev κ s L5 = some (if left = false ∧ S.r = g0 then 1 else 0) := by
      cases left <;> by_cases e : S.r = g0 <;>
        simp [unitRE, Exp.gF, Exp.ev, Machine.BinOp.eval,
          Machine.UnOp.eval, h5, h5g0, h5lf, hsrT', Fld.cap,
          Fld.get, GF.get, b2n, e, S]
    have hcand : unitCand s x left = if left = true ∧ S.l = g0 then [g0, sr, S.r]
        else if left = false ∧ S.r = g0 then [S.l, sr, g0] else [g0] := by
      rw [unitCand_eq]; exact ite_eq_left hov
    by_cases hL : left = true ∧ S.l = g0
    · rw [ite_eq_left hL] at hcL hcand
      have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "uk") (e := (3 : Exp)) (v :=
        3) rfl
      have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L5 "uk" 3) (x := "u0") (e := .var
        "g0") (v := g0)
        (by simp [Exp.ev, Machine.State.upd, h5g0])
      have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L5 "uk" 3) "u0" g0) (x :=
        "u1") (e := .var "sr")
        (v := sr) (by simp [Exp.ev, Machine.State.upd, h5])
      have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L5 "uk" 3) "u0" g0) "u1"
        sr) (x := "u2")
        (e := .gF .r "sr") (v := S.r) (by simp [Exp.gF, Exp.ev, Machine.State.upd, h5, hsrT',
          Fld.cap, Fld.get,
          GF.get, S])
      refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_t hc4'
        one_ne_zero
        (evalF_seq_ok2 a5 (evalF_ite_t hcL one_ne_zero (evalF_seq_ok2 b1 (evalF_seq_ok2 b2
          (evalF_seq_ok2 b3 b4)))))))),
        by rw [hcand]; simp [unitOf, Machine.State.upd], by simp [Machine.State.upd], ?_,
        hfr3 _ fun r h1 h2 h3 h4 h5 h6 => by simp [L5, Machine.State.upd, h2, h3, h4, h5, h6]⟩
      simp [Exp.cost, Exp.gF, unitLE] at hc1 ⊢; omega
    · rw [ite_eq_right hL] at hcL hcand
      by_cases hR : left = false ∧ S.r = g0
      · rw [ite_eq_left hR] at hcR hcand
        have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "uk") (e := (3 : Exp)) (v
          := 3) rfl
        have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L5 "uk" 3) (x := "u0") (e := .gF
          .l "sr") (v := S.l)
          (by simp [Exp.gF, Exp.ev, Machine.State.upd, h5, hsrT', Fld.cap,
            Fld.get, GF.get, S])
        have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L5 "uk" 3) "u0" S.l) (x :=
          "u1") (e := .var "sr")
          (v := sr) (by simp [Exp.ev, Machine.State.upd, h5])
        have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L5 "uk" 3) "u0" S.l)
          "u1" sr) (x := "u2")
          (e := .var "g0") (v := g0) (by simp [Exp.ev, Machine.State.upd, h5g0])
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_t hc4'
          one_ne_zero
          (evalF_seq_ok2 a5 (evalF_ite_f hcL (evalF_ite_t hcR one_ne_zero (evalF_seq_ok2 b1
            (evalF_seq_ok2 b2
          (evalF_seq_ok2 b3 b4))))))))),
          by rw [hcand]; simp [unitOf, Machine.State.upd], by simp [Machine.State.upd], ?_,
          hfr3 _ fun r h1 h2 h3 h4 h5 h6 => by simp [L5, Machine.State.upd, h2, h3, h4, h5, h6]⟩
        simp [Exp.cost, Exp.gF, unitLE, unitRE] at hc1 ⊢; omega
      · rw [ite_eq_right hR] at hcR hcand
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_t hc4'
          one_ne_zero
          (evalF_seq_ok2 a5 (evalF_ite_f hcL (evalF_ite_f hcR evalF_skip)))))),
          by rw [hcand]; simp [unitOf, L5, L3, Machine.State.upd], by simp [L5, L3,
            Machine.State.upd], ?_,
          hfr3 _ fun r h1 h2 h3 h4 h5 h6 => by simp [L5, Machine.State.upd, h6]⟩
        simp [Exp.cost, Exp.gF, unitLE, unitRE] at hc1 ⊢; omega
  · have hc4' : (.gF .st "g0" =ₑ 1 : Exp).ev κ s L3 = some 0 := by
      rw [hc4]; cases h : G0.st <;> simp_all [St.toN]
    have hcand : unitCand s x left = [g0] := by
      rw [unitCand_eq]; exact ite_eq_right hov
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_f hc4'
      evalF_skip))),
      by rw [hcand]; simp [unitOf, L3, Machine.State.upd], by simp [L3, Machine.State.upd], ?_,
      hfr3 _ fun r _ _ _ _ _ _ => rfl⟩
    simp [Exp.cost, Exp.gF] at hc1 ⊢; omega

/-! ### Labels for a moved unit -/

theorem pushBackLabs_inv {c D B k : Nat} {prev : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushBackLabs c D B prev (k + 1)).run s = .ok labs s') :
    ∃ l rest, labs = l :: rest ∧ (pushBackLabs c D B (some l) k).run s = .ok rest s' ∧
      (prev = none → l = c) ∧ (∀ p, prev = some p → p + D < 1 <<< B ∧ p < p + D ∧ l = p + D) := by
  unfold pushBackLabs at h
  cases prev with
  | none =>
    simp only [OrderMaintenance.Proof.run_pure_bind] at h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OrderMaintenance.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    exact ⟨_, _, rfl, h2, fun _ => rfl, fun _ h => absurd h (by simp)⟩
  | some p =>
    dsimp only at h
    obtain ⟨l, s1, h1, h⟩ := run_bind_ok h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OrderMaintenance.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    obtain ⟨hs, ha, hb, rfl⟩ := after_inv h1
    subst s1
    exact ⟨_, _, rfl, h2, fun h => absurd h (by simp), fun q hq => by
      simp only [Option.some.injEq] at hq; subst hq; exact ⟨ha, hb, rfl⟩⟩

theorem pushFrontLabs_inv {c D k : Nat} {nxt : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushFrontLabs c D nxt (k + 1)).run s = .ok labs s') :
    ∃ l rest, labs = rest ++ [l] ∧ (pushFrontLabs c D (some l) k).run s = .ok rest s' ∧
      (nxt = none → l = c) ∧ (∀ n, nxt = some n → D ≤ n ∧ D ≠ 0 ∧ l = n - D) := by
  unfold pushFrontLabs at h
  cases nxt with
  | none =>
    simp only [OrderMaintenance.Proof.run_pure_bind] at h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OrderMaintenance.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    exact ⟨_, _, rfl, h2, fun _ => rfl, fun _ h => absurd h (by simp)⟩
  | some n =>
    dsimp only at h
    obtain ⟨l, s1, h1, h⟩ := run_bind_ok h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OrderMaintenance.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    obtain ⟨hs, ha, hb, rfl⟩ := before_inv h1
    subst s1
    exact ⟨_, _, rfl, h2, fun h => absurd h (by simp), fun q hq => by
      simp only [Option.some.injEq] at hq; subst hq; exact ⟨ha, hb, rfl⟩⟩

theorem pushBackLabs_zero {c D B : Nat} {prev : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushBackLabs c D B prev 0).run s = .ok labs s') : labs = [] ∧ s' = s := by
  unfold pushBackLabs at h; simp only [OrderMaintenance.Proof.run_pure] at h; injection h with
    h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem pushFrontLabs_zero {c D : Nat} {nxt : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushFrontLabs c D nxt 0).run s = .ok labs s') : labs = [] ∧ s' = s := by
  unfold pushFrontLabs at h; simp only [OrderMaintenance.Proof.run_pure] at h; injection h with
    h1 h2; exact ⟨h1.symm, h2.symm⟩

/-- The labels held in locals: `[l0]`, or `[l0, l1, l2]` when `uk = 3`. -/
def labsOf (L : Loc) : List Nat := if L "uk" = 1 then [L "l0"] else [L "l0", L "l1", L "l2"]

/-- The central group label at the configured group-label width. -/
def centreG : Exp := cme{ 1 <<< (P.Bg ∸ 1) }

theorem centreG_ev {κ : Caps} {S0 : Core} {L : Loc} : centreG.ev κ S0 L = some (1 <<<
  (S0.P.groupBits - 1)) := by
  have hm := Exp.ev_monus κ S0 L (a := .prm .Bg) (b := (1 : Exp)) (x := S0.P.groupBits) (y := 1)
    (by simp [Exp.ev, PF.get]) rfl
  simp only [centreG, Exp.ev, Option.bind_some]
  rw [hm]; simp [Machine.BinOp.eval, Nat.shiftLeft_eq]

/-- `pushBackLabs` after the last group of chunk `y` (locals `y uk`). -/
def labLS : Stm := cm{
  D := P.Dg; B := P.Bg
  if C[y].first = 0 then l0 := ‹centreG› else { a := G[C[y].last].lab; afterS; l0 := lab }
  if uk = 3 then { a := l0; afterS; l1 := lab; a := l1; afterS; l2 := lab } }

/-- `pushFrontLabs` before the first group of chunk `y` (locals `y uk`). -/
def labRS : Stm := cm{
  D := P.Dg
  if C[y].first = 0 then m := ‹centreG› else { b := G[C[y].first].lab; beforeS; m := lab }
  if uk = 3 then { l2 := m; b := m; beforeS; l1 := lab; b := l1; beforeS; l0 := lab }
  else l0 := m }

theorem labLS_ok {κ : Caps} {s : Core} {L : Loc} {y k : Nat} {labs : List Nat} (hy : L "y" = y)
    (hk : (L "uk" = 1 ∧ k = 1) ∨ (L "uk" = 3 ∧ k = 3)) (hyT : y < κ.tbl .C) (hlT : (s.C.getX
      y).last < κ.tbl .G)
    (hlabs : (pushBackLabs (1 <<< (s.P.groupBits - 1)) s.P.groupSpacing s.P.groupBits (if
      (s.C.getX y).first = NIL then none
      else some (s.Gs.getX (s.C.getX y).last).lab) k).run s = .ok labs s) :
    ∃ L' n, evalF κ labLS s L = .ok s L' n ∧ labsOf L' = labs ∧ L' "uk" = L "uk" ∧ n ≤ 150 ∧
      ∀ r, r ≠ "D" → r ≠ "B" → r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "a" → r ≠ "v" → r ≠ "lab" →
        L' r = L r := by
  set c := 1 <<< (s.P.groupBits - 1)
  set prev := if (s.C.getX y).first = NIL then none else some (s.Gs.getX (s.C.getX y).last).lab
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "D") (e := .prm .Dg) (v :=
    s.P.groupSpacing) (by simp [Exp.ev, PF.get])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "D" s.P.groupSpacing) (x := "B") (e
    := .prm .Bg) (v := s.P.groupBits)
    (by simp [Exp.ev, PF.get])
  set L2 := upd (upd L "D" s.P.groupSpacing) "B" s.P.groupBits
  have h2 : ∀ r, r ≠ "D" → r ≠ "B" → L2 r = L r := fun r h1 h2 => by simp [L2,
    Machine.State.upd, h1, h2]
  have h2y : L2 "y" = y := by rw [h2 "y" (by decide) (by decide), hy]
  -- the first label
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨l0, rest, hlabs0, hrest, hnone, hsome⟩ := pushBackLabs_inv hlabs
  have b3 : ∃ L3 c3, evalF κ (.ite (.cF .first "y" =ₑ 0) ("l0" ::= centreG)
      ("a" ::= .gF .lab (.cF .last "y");; afterS;; "l0" ::= "lab")) s L2 = .ok s L3 c3 ∧ L3 "l0"
        = l0 ∧
      (∀ r, r ≠ "l0" → r ≠ "a" → r ≠ "v" → r ≠ "lab" → L3 r = L2 r) ∧ c3 ≤ 40 := by
    by_cases hf : (s.C.getX y).first = NIL
    · have hl0 : l0 = c := hnone (by simp [prev, hf])
      have hc : (.cF .first "y" =ₑ 0 : Exp).ev κ s L2 = some 1 := by
        simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h2y, hyT, Fld.cap, Fld.get,
          CF.get]; simpa [NIL] using hf
      exact ⟨_, _, evalF_ite_t hc one_ne_zero (evalF_assign_ok centreG_ev), by simp
        [Machine.State.upd, hl0, c],
        fun r h1 _ _ _ => by simp [Machine.State.upd, h1], by simp [Exp.cost, centreG, Exp.cF]⟩
    · obtain ⟨hpa, hpb, hl0⟩ := hsome (s.Gs.getX (s.C.getX y).last).lab (by simp [prev, hf])
      have hc : (.cF .first "y" =ₑ 0 : Exp).ev κ s L2 = some 0 := by
        simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h2y, hyT, Fld.cap, Fld.get,
          CF.get]; simpa [NIL] using hf
      set p := (s.Gs.getX (s.C.getX y).last).lab
      have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "a") (e := .gF .lab (.cF
        .last "y")) (v := p)
        (by simp [Exp.gF, Exp.cF, Exp.ev, h2y, hyT, hlT, Fld.cap, Fld.get, CF.get, GF.get]; rfl)
      obtain ⟨c2, b2, hc2⟩ := afterS_ok (κ := κ) (s := s) (L := upd L2 "a" p) (a := p) (D :=
        s.P.groupSpacing) (B := s.P.groupBits)
        (by simp [Machine.State.upd]) (by simp [Machine.State.upd, L2]) (by simp
          [Machine.State.upd, L2])
        hpa hpb
      have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L2 "a" p) "v" (p +
        s.P.groupSpacing)) "lab" (p + s.P.groupSpacing))
        (x := "l0") (e := .var "lab") (v := p + s.P.groupSpacing) (by simp [Exp.ev,
          Machine.State.upd])
      exact ⟨_, _, evalF_ite_f hc (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 b3)), by simp
        [Machine.State.upd, hl0],
        fun r h1 h2 h3 h4 => by simp [Machine.State.upd, h1, h2, h3, h4],
        by simp [Exp.cost, Exp.gF, Exp.cF] at hc2 ⊢; omega⟩
  obtain ⟨L3, c3, e3, h3l0, h3F, hc3⟩ := b3
  have h3uk : L3 "uk" = L "uk" := by
    rw [h3F "uk" (by decide) (by decide) (by decide) (by decide), h2 "uk" (by decide) (by decide)]
  have h3D : L3 "D" = s.P.groupSpacing := by
    rw [h3F "D" (by decide) (by decide) (by decide) (by decide)]; simp [L2, Machine.State.upd]
  have h3B : L3 "B" = s.P.groupBits := by
    rw [h3F "B" (by decide) (by decide) (by decide) (by decide)]; simp [L2, Machine.State.upd]
  have hfr : ∀ L' : Loc, (∀ r, r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "a" → r ≠ "v" → r ≠ "lab" →
    L' r = L3 r) →
      ∀ r, r ≠ "D" → r ≠ "B" → r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "a" → r ≠ "v" → r ≠ "lab" →
        L' r = L r :=
    fun L' hL' r h1 h2' h3 h4 h5 h6 h7 h8 => by
      rw [hL' r h3 h4 h5 h6 h7 h8, h3F r h3 h6 h7 h8, h2 r h1 h2']
  rcases hk with ⟨huk, hk'⟩ | ⟨huk, hk'⟩
  · obtain rfl : k' = 0 := by omega
    obtain ⟨rfl, -⟩ := pushBackLabs_zero hrest
    have hc : ("uk" =ₑ 3 : Exp).ev κ s L3 = some 0 := by
      simp [Exp.ev, Machine.BinOp.eval, h3uk, huk]
    refine ⟨L3, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_ite_f hc
      evalF_skip))),
      by simp [labsOf, h3uk, huk, h3l0, hlabs0], h3uk, by simp [Exp.cost] at hc3 ⊢; omega,
      hfr L3 fun _ _ _ _ _ _ _ => rfl⟩
  · obtain rfl : k' = 2 := by omega
    obtain ⟨l1, rest2, hr1, hrest2, -, hs1⟩ := pushBackLabs_inv hrest
    obtain ⟨hpa1, hpb1, hl1⟩ := hs1 l0 rfl
    obtain ⟨l2, rest3, hr2, hrest3, -, hs2⟩ := pushBackLabs_inv hrest2
    obtain ⟨hpa2, hpb2, hl2⟩ := hs2 l1 rfl
    obtain ⟨rfl, -⟩ := pushBackLabs_zero hrest3
    have hc : ("uk" =ₑ 3 : Exp).ev κ s L3 = some 1 := by
      simp [Exp.ev, Machine.BinOp.eval, h3uk, huk]
    have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "a") (e := .var "l0") (v := l0)
      (by simp [Exp.ev, h3l0])
    obtain ⟨c2, b2, hc2⟩ := afterS_ok (κ := κ) (s := s) (L := upd L3 "a" l0) (a := l0) (D :=
      s.P.groupSpacing) (B := s.P.groupBits)
      (by simp [Machine.State.upd]) (by simp [Machine.State.upd, h3D]) (by simp
        [Machine.State.upd, h3B])
      hpa1 hpb1
    set L5 := upd (upd (upd L3 "a" l0) "v" (l0 + s.P.groupSpacing)) "lab" (l0 + s.P.groupSpacing)
    have b3 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "l1") (e := .var "lab") (v := l1)
      (by simp [Exp.ev, L5, Machine.State.upd, hl1])
    have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd L5 "l1" l1) (x := "a") (e := .var
      "l1") (v := l1)
      (by simp [Exp.ev, Machine.State.upd])
    obtain ⟨c5, b5, hc5⟩ := afterS_ok (κ := κ) (s := s) (L := upd (upd L5 "l1" l1) "a" l1) (a :=
      l1) (D := s.P.groupSpacing)
      (B := s.P.groupBits) (by simp [Machine.State.upd]) (by simp [Machine.State.upd, L5, h3D])
      (by simp [Machine.State.upd, L5, h3B]) hpa2 hpb2
    set L6 := upd (upd (upd (upd L5 "l1" l1) "a" l1) "v" (l1 + s.P.groupSpacing)) "lab" (l1 +
      s.P.groupSpacing)
    have b6 := evalF_assign_ok (κ := κ) (s := s) (L := L6) (x := "l2") (e := .var "lab") (v := l2)
      (by simp [Exp.ev, L6, Machine.State.upd, hl2])
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_ite_t hc one_ne_zero
      (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 (evalF_seq_ok2 b5
        b6)))))))),
      ?_, ?_, ?_, hfr _ fun r h3 h4 h5 h6 h7 h8 => by simp [L6, L5, Machine.State.upd,  h4,
        h5, h6, h7, h8]⟩
    · simp [labsOf, L6, L5, Machine.State.upd, h3uk, huk, h3l0, hlabs0, hr1, hr2]
    · simp [L6, L5, Machine.State.upd, h3uk]
    · simp [Exp.cost] at hc2 hc3 hc5 ⊢; omega

theorem labRS_ok {κ : Caps} {s : Core} {L : Loc} {y k : Nat} {labs : List Nat} (hy : L "y" = y)
    (hk : (L "uk" = 1 ∧ k = 1) ∨ (L "uk" = 3 ∧ k = 3)) (hyT : y < κ.tbl .C) (hfT : (s.C.getX
      y).first < κ.tbl .G)
    (hlabs : (pushFrontLabs (1 <<< (s.P.groupBits - 1)) s.P.groupSpacing (if (s.C.getX y).first
      = NIL then none
      else some (s.Gs.getX (s.C.getX y).first).lab) k).run s = .ok labs s) :
    ∃ L' n, evalF κ labRS s L = .ok s L' n ∧ labsOf L' = labs ∧ L' "uk" = L "uk" ∧ n ≤ 150 ∧
      ∀ r, r ≠ "D" → r ≠ "m" → r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "b" → r ≠ "lab" → L' r = L r
        := by
  set c := 1 <<< (s.P.groupBits - 1)
  set nxt := if (s.C.getX y).first = NIL then none else some (s.Gs.getX (s.C.getX y).first).lab
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "D") (e := .prm .Dg) (v :=
    s.P.groupSpacing) (by simp [Exp.ev, PF.get])
  set L1 := upd L "D" s.P.groupSpacing
  have h1 : ∀ r, r ≠ "D" → L1 r = L r := fun r h1 => by simp [L1, Machine.State.upd, h1]
  have h1y : L1 "y" = y := by rw [h1 "y" (by decide), hy]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨m1, rest, hlabs0, hrest, hnone, hsome⟩ := pushFrontLabs_inv hlabs
  have b3 : ∃ L3 c3, evalF κ (.ite (.cF .first "y" =ₑ 0) ("m" ::= centreG)
      ("b" ::= .gF .lab (.cF .first "y");; beforeS;; "m" ::= "lab")) s L1 = .ok s L3 c3 ∧ L3 "m"
        = m1 ∧
      (∀ r, r ≠ "m" → r ≠ "b" → r ≠ "lab" → L3 r = L1 r) ∧ c3 ≤ 40 := by
    by_cases hf : (s.C.getX y).first = NIL
    · have hm1 : m1 = c := hnone (by simp [nxt, hf])
      have hc : (.cF .first "y" =ₑ 0 : Exp).ev κ s L1 = some 1 := by
        simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1y, hyT, Fld.cap, Fld.get,
          CF.get]; simpa [NIL] using hf
      exact ⟨_, _, evalF_ite_t hc one_ne_zero (evalF_assign_ok centreG_ev), by simp
        [Machine.State.upd, hm1, c],
        fun r h1 _ _ => by simp [Machine.State.upd, h1], by simp [Exp.cost, centreG, Exp.cF]⟩
    · obtain ⟨hpa, hpb, hm1⟩ := hsome (s.Gs.getX (s.C.getX y).first).lab (by simp [nxt, hf])
      have hc : (.cF .first "y" =ₑ 0 : Exp).ev κ s L1 = some 0 := by
        simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1y, hyT, Fld.cap, Fld.get,
          CF.get]; simpa [NIL] using hf
      set p := (s.Gs.getX (s.C.getX y).first).lab
      have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "b") (e := .gF .lab (.cF
        .first "y")) (v := p)
        (by simp [Exp.gF, Exp.cF, Exp.ev, h1y, hyT, hfT, Fld.cap, Fld.get, CF.get, GF.get]; rfl)
      have b2 := beforeS_ok (κ := κ) (s := s) (L := upd L1 "b" p) (b := p) (D := s.P.groupSpacing)
        (by simp [Machine.State.upd]) (by simp [Machine.State.upd, L1]) hpa hpb
      have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L1 "b" p) "lab" (p -
        s.P.groupSpacing))
        (x := "m") (e := .var "lab") (v := p - s.P.groupSpacing) (by simp [Exp.ev,
          Machine.State.upd])
      exact ⟨_, _, evalF_ite_f hc (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 b3)), by simp
        [Machine.State.upd, hm1],
        fun r h1 h2 h3 => by simp [Machine.State.upd, h1, h2, h3], by simp [Exp.cost, Exp.gF,
          Exp.cF]⟩
  obtain ⟨L3, c3, e3, h3m, h3F, hc3⟩ := b3
  have h3uk : L3 "uk" = L "uk" := by
    rw [h3F "uk" (by decide) (by decide) (by decide), h1 "uk" (by decide)]
  have h3D : L3 "D" = s.P.groupSpacing := by
    rw [h3F "D" (by decide) (by decide) (by decide)]; simp [L1, Machine.State.upd]
  have hfr : ∀ L' : Loc, (∀ r, r ≠ "m" → r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "b" → r ≠ "lab" →
    L' r = L3 r) →
      ∀ r, r ≠ "D" → r ≠ "m" → r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "b" → r ≠ "lab" → L' r = L r :=
    fun L' hL' r h1' h2 h3 h4 h5 h6 h7 => by rw [hL' r h2 h3 h4 h5 h6 h7, h3F r h2 h6 h7, h1 r h1']
  rcases hk with ⟨huk, hk'⟩ | ⟨huk, hk'⟩
  · obtain rfl : k' = 0 := by omega
    obtain ⟨rfl, -⟩ := pushFrontLabs_zero hrest
    have hc : ("uk" =ₑ 3 : Exp).ev κ s L3 = some 0 := by
      simp [Exp.ev, Machine.BinOp.eval, h3uk, huk]
    have b := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "l0") (e := .var "m") (v := m1)
      (by simp [Exp.ev, h3m])
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e3 (evalF_ite_f hc b)),
      by simp [labsOf, Machine.State.upd, h3uk, huk,
        hlabs0], by simp [Machine.State.upd, h3uk], ?_,
      hfr _ fun r h2 h3 h4 h5 h6 h7 => by simp [Machine.State.upd, h3]⟩
    simp [Exp.cost] at hc3 ⊢; omega
  · obtain rfl : k' = 2 := by omega
    obtain ⟨m2, rest2, hr1, hrest2, -, hs1⟩ := pushFrontLabs_inv hrest
    obtain ⟨hpa1, hpb1, hm2⟩ := hs1 m1 rfl
    obtain ⟨m3, rest3, hr2, hrest3, -, hs2⟩ := pushFrontLabs_inv hrest2
    obtain ⟨hpa2, hpb2, hm3⟩ := hs2 m2 rfl
    obtain ⟨rfl, -⟩ := pushFrontLabs_zero hrest3
    have hc : ("uk" =ₑ 3 : Exp).ev κ s L3 = some 1 := by
      simp [Exp.ev, Machine.BinOp.eval, h3uk, huk]
    have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "l2") (e := .var "m") (v := m1)
      (by simp [Exp.ev, h3m])
    have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L3 "l2" m1) (x := "b") (e := .var
      "m") (v := m1)
      (by simp [Exp.ev, Machine.State.upd, h3m])
    have b3 := beforeS_ok (κ := κ) (s := s) (L := upd (upd L3 "l2" m1) "b" m1) (b := m1) (D :=
      s.P.groupSpacing)
      (by simp [Machine.State.upd]) (by simp [Machine.State.upd, h3D]) hpa1 hpb1
    set L5 := upd (upd (upd L3 "l2" m1) "b" m1) "lab" (m1 - s.P.groupSpacing)
    have b4 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "l1") (e := .var "lab") (v := m2)
      (by simp [Exp.ev, L5, Machine.State.upd, hm2])
    have b5 := evalF_assign_ok (κ := κ) (s := s) (L := upd L5 "l1" m2) (x := "b") (e := .var
      "l1") (v := m2)
      (by simp [Exp.ev, Machine.State.upd])
    have b6 := beforeS_ok (κ := κ) (s := s) (L := upd (upd L5 "l1" m2) "b" m2) (b := m2) (D :=
      s.P.groupSpacing)
      (by simp [Machine.State.upd]) (by simp [Machine.State.upd, L5, h3D]) hpa2 hpb2
    set L7 := upd (upd (upd L5 "l1" m2) "b" m2) "lab" (m2 - s.P.groupSpacing)
    have b7 := evalF_assign_ok (κ := κ) (s := s) (L := L7) (x := "l0") (e := .var "lab") (v := m3)
      (by simp [Exp.ev, L7, Machine.State.upd, hm3])
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e3 (evalF_ite_t hc one_ne_zero (evalF_seq_ok2
      b1 (evalF_seq_ok2 b2
      (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 (evalF_seq_ok2 b5 (evalF_seq_ok2 b6 b7)))))))), ?_,
        ?_, ?_,
      hfr _ fun r h2 h3 h4 h5 h6 h7 => by simp [L7, L5, Machine.State.upd, h3, h4, h5, h6, h7]⟩
    · simp [labsOf, L7, L5, Machine.State.upd, h3uk, huk, hlabs0, hr1, hr2]
    · simp [L7, L5, Machine.State.upd, h3uk]
    · simp [Exp.cost] at hc3 ⊢; omega

/-! ### Moving a unit's groups -/

/-- The moved groups join chunk `y` with their labels. -/
def mgPair (xg xl : Reg) : Stm := cm{ G[‹xg›].chk := y; G[‹xg›].lab := ‹xl› }
/-- Update chunk indices and labels for the one or three groups in a moving unit. -/
def mgGS : Stm := cm{
  ‹mgPair "u0" "l0"›; if uk = 3 then { ‹mgPair "u1" "l1"›; ‹mgPair "u2" "l2"› } }

/-- Join groups `u` to chunk `y` with `labs`, matching the Level F group update. -/
def moveGs (y : Nat) (u labs : List Nat) (A : Array Group) : Array Group :=
  (u.zip labs).foldl (fun a p => a.modify p.1 fun G => {
    G with
    chk := y
    lab := p.2
  }) A

/-- Change a group's containing chunk and order label. -/
def chkLabF (y l : Nat) (G : Group) : Group := {
  G with
  chk := y
  lab := l
}

theorem mgGS_ok {κ : Caps} {S0 : Core} {L : Loc} {y : Nat} (hy : L "y" = y) (hk : L "uk" = 1 ∨ L
  "uk" = 3)
    (hu : ∀ g ∈ unitOf L, g < S0.Gs.size ∧ g < κ.tbl .G) :
    ∃ n, evalF κ mgGS S0 L = .ok {
      S0 with
      Gs := moveGs y (unitOf L) (labsOf L) S0.Gs
    } L n ∧ n
      ≤ 40 := by
  have w : ∀ (S1 : Core) (g l : Nat) (xg xl : Reg), L xg = g → L xl = l → g < S1.Gs.size → g <
    κ.tbl .G →
      evalF κ (mgPair xg xl) S1 L = .ok {
        S1 with
        Gs := S1.Gs.modify g (chkLabF y l)
      } L 6 := by
    intro S1 g l xg xl hg hl hgs hgT
    have w1 := evalF_wrG_ok (κ := κ) (s := S1) (L := L) (k := .chk) (i := .var xg) (e := .var
      "y") (j := g) (w := y)
      (by simp [Exp.ev, hg]) (by simp [Exp.ev, hy]) hgs  rfl
    have w2 := evalF_wrG_ok (κ := κ) (s := {
      S1 with
      Gs := S1.Gs.modify g (GF.set · y .chk)
    })
      (L := L) (k := .lab)
      (i := .var xg) (e := .var xl) (j := g) (w := l) (by simp [Exp.ev, hg]) (by simp [Exp.ev,
        hl]) (by simp [hgs])  rfl
    rw [Array.modify_modify_same] at w2
    simp only [mgPair, Stm.wgF]; exact evalF_seq_ok2 w1 w2
  rcases hk with hk | hk
  · have hu0 := hu (L "u0") (by simp [unitOf, hk])
    have e1 := w S0 (L "u0") (L "l0") "u0" "l0" rfl rfl hu0.1 hu0.2
    have hc : ("uk" =ₑ 3 : Exp).ev κ { S0 with Gs := S0.Gs.modify (L "u0") (chkLabF y (L "l0"))
      } L = some 0 := by
      simp [Exp.ev, Machine.BinOp.eval, hk]
    have hfin : moveGs y (unitOf L) (labsOf L) S0.Gs = S0.Gs.modify (L "u0") (chkLabF y (L
      "l0")) := by
      simp [moveGs, unitOf, labsOf, hk]; rfl
    rw [hfin]
    exact ⟨_, evalF_seq_ok2 e1 (evalF_ite_f hc evalF_skip), by simp [Exp.cost]⟩
  · have hu0 := hu (L "u0") (by simp [unitOf, hk])
    have hu1 := hu (L "u1") (by simp [unitOf, hk])
    have hu2 := hu (L "u2") (by simp [unitOf, hk])
    set A1 := S0.Gs.modify (L "u0") (chkLabF y (L "l0"))
    set A2 := A1.modify (L "u1") (chkLabF y (L "l1"))
    set A3 := A2.modify (L "u2") (chkLabF y (L "l2"))
    have e1 := w S0 (L "u0") (L "l0") "u0" "l0" rfl rfl hu0.1 hu0.2
    have e2 := w {
      S0 with
      Gs := A1
    } (L "u1") (L "l1") "u1" "l1" rfl rfl (by simp [A1, hu1.1])
      hu1.2
    have e3 := w {
      S0 with
      Gs := A2
    } (L "u2") (L "l2") "u2" "l2" rfl rfl (by simp [A2, A1,
      hu2.1]) hu2.2
    have hc : ("uk" =ₑ 3 : Exp).ev κ {
      S0 with
      Gs := A1
    } L = some 1 := by
      simp [Exp.ev, Machine.BinOp.eval, hk]
    have hfin : moveGs y (unitOf L) (labsOf L) S0.Gs = A3 := by
      simp [moveGs, unitOf, labsOf, hk]; rfl
    rw [hfin]
    exact ⟨_, evalF_seq_ok2 e1 (evalF_ite_t hc one_ne_zero (evalF_seq_ok2 e2 e3)), by simp
      [Exp.cost]⟩

/-- Select the last group of a moving unit, according to whether it has one or three groups. -/
def ulS : Stm := cm{ if uk = 1 then ul := u0 else ul := u2 }
/-- Remove the moving prefix from the source chunk's endpoint registers. -/
def mgLx : Stm := cm{
  if C[x].last = ul then { C[x].first := 0; C[x].last := 0 } else C[x].first := G[ul].next }
/-- Append the moving prefix to the destination chunk's endpoints. -/
def mgLy : Stm := cm{ if C[y].first = 0 then C[y].first := u0; C[y].last := ul }
/-- `moveGroupsLeft x y unit labels` (locals `x y uk u0 u1 u2 l0 l1 l2`). -/
def mgLS : Stm := ulS;; mgLx;; mgLy;; mgGS

theorem ulS_ok {κ : Caps} {S0 : Core} {L : Loc} (hk : L "uk" = 1 ∨ L "uk" = 3) :
    evalF κ ulS S0 L = .ok S0 (upd L "ul" ((unitOf L).getLastD NIL)) 6 := by
  rcases hk with hk | hk
  · have : (unitOf L).getLastD NIL = L "u0" := by simp [unitOf, hk]
    rw [this]; simp [ulS, evalF, Exp.ev, Machine.BinOp.eval, hk, Exp.cost, Res.addCost]
  · have : (unitOf L).getLastD NIL = L "u2" := by simp [unitOf, hk]
    rw [this]; simp [ulS, evalF, Exp.ev, Machine.BinOp.eval, hk, Exp.cost, Res.addCost]

theorem mgLS_ok {κ : Caps} {s : Core} {L : Loc} {x y : Nat} (hx : L "x" = x) (hy : L "y" = y)
    (hk : L "uk" = 1 ∨ L "uk" = 3) (hxy : x ≠ y) (hxs : x < s.C.size) (hys : y < s.C.size) (hC :
      s.C.size ≤ κ.tbl .C)
    (hu : ∀ g ∈ unitOf L, g < s.Gs.size ∧ g < κ.tbl .G) :
    ∃ L' n, evalF κ mgLS s L = .ok (moveGroupsLeft s x y (unitOf L) (labsOf L)) L' n ∧ n ≤ 100 ∧
      ∀ r, r ≠ "ul" → L' r = L r := by
  set u := unitOf L
  set ul := u.getLastD NIL
  have hxT : x < κ.tbl .C := by omega
  have hyT : y < κ.tbl .C := by omega
  have hul : ul < s.Gs.size ∧ ul < κ.tbl .G := by
    apply hu; rcases hk with hk | hk <;> simp [ul, u, unitOf, hk]
  have e1 := ulS_ok (κ := κ) (S0 := s) hk
  set L1 := upd L "ul" ul
  have h1 : ∀ r, r ≠ "ul" → L1 r = L r := fun r h => by simp [L1, Machine.State.upd, h]
  have h1x : L1 "x" = x := by rw [h1 "x" (by decide), hx]
  have h1y : L1 "y" = y := by rw [h1 "y" (by decide), hy]
  have h1ul : L1 "ul" = ul := by simp [L1, Machine.State.upd]
  have hvx : ∀ s' : Core, (Exp.var "x").ev κ s' L1 = some x := fun _ => by simp [Exp.ev, h1x]
  have hvy : ∀ s' : Core, (Exp.var "y").ev κ s' L1 = some y := fun _ => by simp [Exp.ev, h1y]
  set X := s.C.getX x
  -- the source chunk
  set C1 := s.C.modify x fun Z => if X.last == ul then {
    Z with
    first := NIL
    last := NIL
  }
    else {
      Z with
      first := (s.Gs.getX ul).next
    }
  have e2 : ∃ c2, evalF κ mgLx s L1 = .ok {
    s with
    C := C1
  } L1 c2 ∧ c2 ≤ 20 := by
    by_cases hl : X.last = ul
    · have w1 := evalF_wrC_ok (κ := κ) (s := s) (L := L1) (k := .first) (e := (0 : Exp)) (w :=
        0) (hvx _) rfl hxs  rfl
      have w2 := evalF_wrC_ok (κ := κ) (s := {
        s with
        C := s.C.modify x (CF.set · 0 .first)
      })
        (L := L1) (k := .last)
        (e := (0 : Exp)) (w := 0) (hvx _) rfl (by simp [hxs])  rfl
      have hC1 : (s.C.modify x (CF.set · 0 .first)).modify x (CF.set · 0 .last) = C1 := by
        rw [Array.modify_modify_same]; apply Array.modify_congr_getX; simp [hl]; rfl
      rw [hC1] at w2
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1x, h1ul,
        hxT, Fld.cap, Fld.get,
        CF.get, X, hl]) one_ne_zero (evalF_seq_ok2 (by
          simp only [Stm.wcF]
          exact w1) (by
          simp only [Stm.wcF]
          exact w2)),
        by simp [Exp.cost, Exp.cF]⟩
    · have w1 := evalF_wrC_ok (κ := κ) (s := s) (L := L1) (k := .first) (e := .gF .next "ul") (w
        := (s.Gs.getX ul).next)
        (hvx _) (by simp [Exp.gF, Exp.ev, h1ul, hul.2, Fld.cap, Fld.get, GF.get]) hxs  rfl
      have hC1 : s.C.modify x (CF.set · (s.Gs.getX ul).next .first) = C1 := by
        apply Array.modify_congr_getX; simp [hl]; rfl
      rw [hC1] at w1
      exact ⟨_, evalF_ite_f (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1x, h1ul, hxT,
        Fld.cap, Fld.get,
        CF.get, X, hl]) (by
          simp only [Stm.wcF]
          exact w1), by simp [Exp.cost, Exp.cF, Exp.gF]⟩
  obtain ⟨c2, e2, hc2⟩ := e2
  -- the target chunk
  have hhead : u.headD NIL = L "u0" := by rcases hk with hk | hk <;> simp [u, unitOf, hk]
  set Z := C1.getX y
  have hZ : Z = s.C.getX y := by
    simp only [Z, C1, getX_modify']; rw [ite_eq_right (fun h => hxy h.1.symm)]
  set C2 := C1.modify y fun Z => {
    Z with
    first := if Z.first == NIL then L "u0" else Z.first
    last := ul
  }
  have e3 : ∃ c3, evalF κ mgLy {
    s with
    C := C1
  } L1 = .ok {
    s with
    C := C2
  } L1 c3 ∧ c3 ≤ 20 := by
    have hu0 : L1 "u0" = L "u0" := h1 "u0" (by decide)
    by_cases hf : Z.first = 0
    · have hf' : (C1.getX y).first = 0 := hf
      have w1 := evalF_wrC_ok (κ := κ) (s := {
        s with
        C := C1
      }) (L := L1) (k := .first) (e :=
        .var "u0") (w := L "u0")
        (hvy _) (by simp [Exp.ev, hu0]) (by simp [C1, hys])  rfl
      have w2 := evalF_wrC_ok (κ := κ) (s := { s with C := C1.modify y (CF.set · (L "u0")
        .first) }) (L := L1)
        (k := .last) (e := .var "ul") (w := ul) (hvy _) (by simp [Exp.ev, h1ul]) (by simp [C1,
          hys])  rfl
      have hC2 : (C1.modify y (CF.set · (L "u0") .first)).modify y (CF.set · ul .last) = C2 := by
        rw [Array.modify_modify_same]; apply Array.modify_congr_getX
        simp [hf', NIL]; rfl
      rw [hC2] at w2
      exact ⟨_, evalF_seq_ok2 (evalF_ite_t (v := 1) (by simp [Exp.cF, Exp.ev,
        Machine.BinOp.eval, h1y, hyT,
        Fld.cap, Fld.get, CF.get, hf']) one_ne_zero (by
          simp only [Stm.wcF]
          exact w1))
        (by
          simp only [Stm.wcF]
          exact w2), by simp [Exp.cost, Exp.cF]⟩
    · have hf' : ¬(C1.getX y).first = 0 := hf
      have w2 := evalF_wrC_ok (κ := κ) (s := {
        s with
        C := C1
      }) (L := L1)
        (k := .last) (e := .var "ul") (w := ul) (hvy _) (by simp [Exp.ev, h1ul]) (by simp [C1,
          hys])  rfl
      have hC2 : C1.modify y (CF.set · ul .last) = C2 := by
        apply Array.modify_congr_getX
        simp [hf', NIL]; rfl
      rw [hC2] at w2
      exact ⟨_, evalF_seq_ok2 (evalF_ite_f (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1y, hyT,
        Fld.cap, Fld.get, CF.get, hf']) evalF_skip) (by
          simp only [Stm.wcF]
          exact w2), by simp
          [Exp.cost, Exp.cF]⟩
  obtain ⟨c3, e3, hc3⟩ := e3
  -- the groups
  have hk1 : L1 "uk" = 1 ∨ L1 "uk" = 3 := by rw [h1 "uk" (by decide)]; exact hk
  have hU : unitOf L1 = u := by
    simp [unitOf, u, h1 "uk" (by decide), h1 "u0" (by decide), h1 "u1" (by decide),
    h1 "u2" (by decide)]
  have hLb : labsOf L1 = labsOf L := by
    simp [labsOf, h1 "uk" (by decide), h1 "l0" (by decide), h1 "l1" (by decide),
    h1 "l2" (by decide)]
  obtain ⟨c4, e4, hc4⟩ := mgGS_ok (κ := κ) (S0 := {
    s with
    C := C2
  }) (L := L1) (y := y) h1y hk1
    (by rw [hU]; exact hu)
  rw [hU, hLb] at e4
  have hfin : ({
    {
      s with
      C := C2
    } with
    Gs := moveGs y u (labsOf L) s.Gs
  } : Core) =
      moveGroupsLeft s x y u (labsOf L) := by
    unfold moveGroupsLeft; rw [hhead]; rfl
  rw [hfin] at e4
  refine ⟨L1, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4)), by omega, h1⟩

/-- Remove the moving suffix from the source chunk's endpoints. -/
def mgRx : Stm := cm{
  if C[x].first = u0 then { C[x].first := 0; C[x].last := 0 } else C[x].last := G[u0].prev }
/-- Prepend the moving suffix to the destination chunk's endpoints. -/
def mgRy : Stm := cm{ if C[y].first = 0 then C[y].last := ul; C[y].first := u0 }
/-- `moveGroupsRight x y unit labels` (locals `x y uk u0 u1 u2 l0 l1 l2`). -/
def mgRS : Stm := ulS;; mgRx;; mgRy;; mgGS

theorem mgRS_ok {κ : Caps} {s : Core} {L : Loc} {x y : Nat} (hx : L "x" = x) (hy : L "y" = y)
    (hk : L "uk" = 1 ∨ L "uk" = 3) (hxy : x ≠ y) (hxs : x < s.C.size) (hys : y < s.C.size) (hC :
      s.C.size ≤ κ.tbl .C)
    (hu : ∀ g ∈ unitOf L, g < s.Gs.size ∧ g < κ.tbl .G) :
    ∃ L' n, evalF κ mgRS s L = .ok (moveGroupsRight s x y (unitOf L) (labsOf L)) L' n ∧ n ≤ 100 ∧
      ∀ r, r ≠ "ul" → L' r = L r := by
  set u := unitOf L
  set ul := u.getLastD NIL
  have hxT : x < κ.tbl .C := by omega
  have hyT : y < κ.tbl .C := by omega
  have hul : ul < s.Gs.size ∧ ul < κ.tbl .G := by
    apply hu; rcases hk with hk | hk <;> simp [ul, u, unitOf, hk]
  have e1 := ulS_ok (κ := κ) (S0 := s) hk
  set L1 := upd L "ul" ul
  have h1 : ∀ r, r ≠ "ul" → L1 r = L r := fun r h => by simp [L1, Machine.State.upd, h]
  have h1x : L1 "x" = x := by rw [h1 "x" (by decide), hx]
  have h1y : L1 "y" = y := by rw [h1 "y" (by decide), hy]
  have h1ul : L1 "ul" = ul := by simp [L1, Machine.State.upd]
  have hvx : ∀ s' : Core, (Exp.var "x").ev κ s' L1 = some x := fun _ => by simp [Exp.ev, h1x]
  have hvy : ∀ s' : Core, (Exp.var "y").ev κ s' L1 = some y := fun _ => by simp [Exp.ev, h1y]
  set X := s.C.getX x
  -- the source chunk
  have hhead : u.headD NIL = L "u0" := by rcases hk with hk | hk <;> simp [u, unitOf, hk]
  have hu0 : (L "u0") < s.Gs.size ∧ (L "u0") < κ.tbl .G := by
    apply hu; rcases hk with hk | hk <;> simp [u, unitOf, hk]
  have h1u0 : L1 "u0" = L "u0" := h1 "u0" (by decide)
  set C1 := s.C.modify x fun Z => if X.first == L "u0" then {
    Z with
    first := NIL
    last := NIL
  }
    else { Z with last := (s.Gs.getX (L "u0")).prev }
  have e2 : ∃ c2, evalF κ mgRx s L1 = .ok {
    s with
    C := C1
  } L1 c2 ∧ c2 ≤ 20 := by
    by_cases hl : X.first = L "u0"
    · have w1 := evalF_wrC_ok (κ := κ) (s := s) (L := L1) (k := .first) (e := (0 : Exp)) (w :=
        0) (hvx _) rfl hxs  rfl
      have w2 := evalF_wrC_ok (κ := κ) (s := {
        s with
        C := s.C.modify x (CF.set · 0 .first)
      })
        (L := L1) (k := .last)
        (e := (0 : Exp)) (w := 0) (hvx _) rfl (by simp [hxs])  rfl
      have hC1 : (s.C.modify x (CF.set · 0 .first)).modify x (CF.set · 0 .last) = C1 := by
        rw [Array.modify_modify_same]; apply Array.modify_congr_getX; simp [hl]; rfl
      rw [hC1] at w2
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1x, h1u0,
        hxT, Fld.cap, Fld.get,
        CF.get, X, hl]) one_ne_zero (evalF_seq_ok2 (by
          simp only [Stm.wcF]
          exact w1) (by
          simp only [Stm.wcF]
          exact w2)),
        by simp [Exp.cost, Exp.cF]⟩
    · have w1 := evalF_wrC_ok (κ := κ) (s := s) (L := L1) (k := .last) (e := .gF .prev "u0")
        (w := (s.Gs.getX (L "u0")).prev)
        (hvx _) (by simp [Exp.gF, Exp.ev, h1u0, hu0.2, Fld.cap, Fld.get, GF.get]) hxs  rfl
      have hC1 : s.C.modify x (CF.set · (s.Gs.getX (L "u0")).prev .last) = C1 := by
        apply Array.modify_congr_getX; simp [hl]; rfl
      rw [hC1] at w1
      exact ⟨_, evalF_ite_f (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1x, h1u0, hxT,
        Fld.cap, Fld.get,
        CF.get, X, hl]) (by
          simp only [Stm.wcF]
          exact w1), by simp [Exp.cost, Exp.cF, Exp.gF]⟩
  obtain ⟨c2, e2, hc2⟩ := e2
  -- the target chunk
  set Z := C1.getX y
  have hZ : Z = s.C.getX y := by
    simp only [Z, C1, getX_modify']; rw [ite_eq_right (fun h => hxy h.1.symm)]
  set C2 := C1.modify y fun Z => {
    Z with
    last := if Z.first == NIL then ul else Z.last
    first := L "u0"
  }
  have e3 : ∃ c3, evalF κ mgRy {
    s with
    C := C1
  } L1 = .ok {
    s with
    C := C2
  } L1 c3 ∧ c3 ≤ 20 := by
    have hu0 : L1 "u0" = L "u0" := h1 "u0" (by decide)
    by_cases hf : Z.first = 0
    · have hf' : (C1.getX y).first = 0 := hf
      have w1 := evalF_wrC_ok (κ := κ) (s := {
        s with
        C := C1
      }) (L := L1) (k := .last) (e :=
        .var "ul") (w := ul)
        (hvy _) (by simp [Exp.ev, h1ul]) (by simp [C1, hys])  rfl
      have w2 := evalF_wrC_ok (κ := κ) (s := {
        s with
        C := C1.modify y (CF.set · ul .last)
      }) (L
        := L1)
        (k := .first) (e := .var "u0") (w := L "u0") (hvy _) (by simp [Exp.ev, hu0]) (by simp
          [C1, hys])  rfl
      have hC2 : (C1.modify y (CF.set · ul .last)).modify y (CF.set · (L "u0") .first) = C2 := by
        rw [Array.modify_modify_same]; apply Array.modify_congr_getX
        simp [hf', NIL]; rfl
      rw [hC2] at w2
      exact ⟨_, evalF_seq_ok2 (evalF_ite_t (v := 1) (by simp [Exp.cF, Exp.ev,
        Machine.BinOp.eval, h1y, hyT,
        Fld.cap, Fld.get, CF.get, hf']) one_ne_zero (by
          simp only [Stm.wcF]
          exact w1))
        (by
          simp only [Stm.wcF]
          exact w2), by simp [Exp.cost, Exp.cF]⟩
    · have hf' : ¬(C1.getX y).first = 0 := hf
      have w2 := evalF_wrC_ok (κ := κ) (s := {
        s with
        C := C1
      }) (L := L1)
        (k := .first) (e := .var "u0") (w := L "u0") (hvy _) (by simp [Exp.ev, hu0]) (by simp
          [C1, hys])  rfl
      have hC2 : C1.modify y (CF.set · (L "u0") .first) = C2 := by
        apply Array.modify_congr_getX
        simp [hf', NIL]; rfl
      rw [hC2] at w2
      exact ⟨_, evalF_seq_ok2 (evalF_ite_f (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1y, hyT,
        Fld.cap, Fld.get, CF.get, hf']) evalF_skip) (by
          simp only [Stm.wcF]
          exact w2), by simp
          [Exp.cost, Exp.cF]⟩
  obtain ⟨c3, e3, hc3⟩ := e3
  -- the groups
  have hk1 : L1 "uk" = 1 ∨ L1 "uk" = 3 := by rw [h1 "uk" (by decide)]; exact hk
  have hU : unitOf L1 = u := by
    simp [unitOf, u, h1 "uk" (by decide), h1 "u0" (by decide), h1 "u1" (by decide),
    h1 "u2" (by decide)]
  have hLb : labsOf L1 = labsOf L := by
    simp [labsOf, h1 "uk" (by decide), h1 "l0" (by decide), h1 "l1" (by decide),
    h1 "l2" (by decide)]
  obtain ⟨c4, e4, hc4⟩ := mgGS_ok (κ := κ) (S0 := {
    s with
    C := C2
  }) (L := L1) (y := y) h1y hk1
    (by rw [hU]; exact hu)
  rw [hU, hLb] at e4
  have hfin : ({
    {
      s with
      C := C2
    } with
    Gs := moveGs y u (labsOf L) s.Gs
  } : Core) =
      moveGroupsRight s x y u (labsOf L) := by
    unfold moveGroupsRight; rw [hhead]; rfl
  rw [hfin] at e4
  refine ⟨L1, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4)), by omega, h1⟩

/-! ### Sizes after a move -/

/-- `moveSizes x y unit` (locals `x y uk u0 u1 u2`). -/
def msMv : Stm := cm{ mv := G[u0].size; if uk = 3 then mv := mv + G[u1].size + G[u2].size }
/-- Transfer the moving unit's element count between its source and destination chunks. -/
def msS : Stm := cm{ msMv; C[x].size := C[x].size ∸ mv; C[y].size := C[y].size + mv }

theorem msS_ok {κ : Caps} {s : Core} {L : Loc} {x y : Nat} (hx : L "x" = x) (hy : L "y" = y)
    (hk : L "uk" = 1 ∨ L "uk" = 3) (hxs : x < s.C.size) (hys : y < s.C.size) (hC : s.C.size ≤
      κ.tbl .C)
    (hu : ∀ g ∈ unitOf L, g < κ.tbl .G) :
    ∃ L' n, evalF κ msS s L = .ok (OrderMaintenance.Proof.cmoveSizes s x y (unitOf L)) L' n ∧ n
      ≤ 80 ∧
      ∀ r, r ≠ "mv" → L' r = L r := by
  set mv := ((unitOf L).map fun g => (s.Gs.getX g).size).sum
  have hxT : x < κ.tbl .C := by omega
  have hyT : y < κ.tbl .C := by omega
  have b1 : ∃ L1 c1, evalF κ msMv s L = .ok s L1 c1 ∧ L1 "mv" = mv ∧
      (∀ r, r ≠ "mv" → L1 r = L r) ∧ c1 ≤ 30 := by
    rcases hk with hk | hk
    · have hu0 := hu (L "u0") (by simp [unitOf, hk])
      have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "mv") (e := .gF .size "u0") (v
        := mv)
        (by simp [Exp.gF, Exp.ev, hu0, Fld.cap, Fld.get, GF.get, mv, unitOf, hk])
      exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval,
        Machine.State.upd, hk])
        evalF_skip), by simp [Machine.State.upd], fun r h => by simp [Machine.State.upd, h],
        by simp [Exp.cost, Exp.gF]⟩
    · have hu0 := hu (L "u0") (by simp [unitOf, hk])
      have hu1 := hu (L "u1") (by simp [unitOf, hk])
      have hu2 := hu (L "u2") (by simp [unitOf, hk])
      have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "mv") (e := .gF .size "u0")
        (v := (s.Gs.getX (L "u0")).size) (by simp [Exp.gF, Exp.ev, hu0, Fld.cap, Fld.get, GF.get])
      have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "mv" (s.Gs.getX (L "u0")).size)
        (x := "mv")
        (e := "mv" + .gF .size "u1" + .gF .size "u2") (v := mv)
        (by simp [Exp.gF, Exp.ev, Machine.State.upd,
          Machine.BinOp.eval, hu1, hu2, Fld.cap, Fld.get, GF.get, mv,
          unitOf, hk]; omega)
      exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval,
        Machine.State.upd, hk]) one_ne_zero a2), by simp [Machine.State.upd],
        fun r h => by simp [Machine.State.upd, h], by simp [Exp.cost, Exp.gF]⟩
  obtain ⟨L1, c1, e1, h1mv, h1F, hc1⟩ := b1
  have h1x : L1 "x" = x := by rw [h1F "x" (by decide), hx]
  have h1y : L1 "y" = y := by rw [h1F "y" (by decide), hy]
  have hm := Exp.ev_monus κ s L1 (a := .cF .size "x") (b := .var "mv") (x := (s.C.getX x).size)
    (y := mv)
    (by simp [Exp.cF, Exp.ev, h1x, hxT, Fld.cap, Fld.get, CF.get]) (by simp [Exp.ev, h1mv])
  have w1 := evalF_wrC_ok (κ := κ) (s := s) (L := L1) (k := .size) (i := .var "x") (e :=
    Exp.monus (.cF .size "x") "mv")
    (j := x) (w := (s.C.getX x).size - mv) (by simp [Exp.ev, h1x]) hm hxs  rfl
  set C1 := s.C.modify x (CF.set · ((s.C.getX x).size - mv) .size)
  have w2 := evalF_wrC_ok (κ := κ) (s := {
    s with
    C := C1
  }) (L := L1) (k := .size) (i := .var "y")
    (e := .cF .size "y" + "mv") (j := y) (w := (C1.getX y).size + mv) (by simp [Exp.ev, h1y])
    (by simp [Exp.cF, Exp.ev, Machine.BinOp.eval, h1y, h1mv, hyT, Fld.cap,
      Fld.get, CF.get]) (by simp [C1, hys])  rfl
  have hfin : ({
    s with
    C := C1.modify y (CF.set · ((C1.getX y).size + mv) .size)
  } : Core) =
      OrderMaintenance.Proof.cmoveSizes s x y (unitOf L) := by
    simp only [OrderMaintenance.Proof.cmoveSizes]
    congr 1
    rw [show C1 = s.C.modify x fun X => {
      X with
      size := X.size - mv
    } from
      Array.modify_congr_getX _ _ _ _ rfl]
    apply Array.modify_congr_getX; rfl
  rw [hfin] at w2
  refine ⟨L1, _, evalF_seq_ok2 e1 (evalF_seq_ok2 (by
          simp only [Stm.wcF]
          exact w1) (by
          simp only [Stm.wcF]
          exact w2)),
    ?_, h1F⟩
  simp [Exp.cost, Exp.cF] at hc1 ⊢; omega

/-! ### `chunkSplitStep` -/

/-- Choose the lighter overflow sibling, breaking equal-size ties to the left. -/
def cssDirE : Exp := cme{ C[C[x].l].size ≤ C[C[x].r].size }
/-- Label and move a unit to the left overflow sibling. -/
def cssL : Stm := cm{ y := C[x].l; labLS; mgLS }
/-- Label and move a unit to the right overflow sibling. -/
def cssR : Stm := cm{ y := C[x].r; labRS; mgRS }
/-- Choose a unit and destination, move it, and update the two chunk sizes. -/
def cssMove : Stm := cm{ lf := ‹cssDirE›; unitS; if lf then cssL else cssR; msS }
/-- Move one unit to the lighter sibling, or remove an empty chunk, returning `ok`. -/
def chunkSplitStepS : Stm := cm{
  xf := C[x].first
  if xf = 0 then { removeChunkS; ok := 0 } else { cssMove; ok := 1 } }

theorem moveGroupsLeft_C_size (s : Core) (x y : Nat) (u labs : List Nat) :
    (moveGroupsLeft s x y u labs).C.size = s.C.size := by simp [moveGroupsLeft]

theorem moveGroupsRight_C_size (s : Core) (x y : Nat) (u labs : List Nat) :
    (moveGroupsRight s x y u labs).C.size = s.C.size := by simp [moveGroupsRight]

open OrderMaintenance.Proof in
theorem chunkSplitStepS_left (κ : Caps) (s : Core) (L : Loc) {x : Nat} {labs : List Nat} (hx : L
  "x" = x)
    (hne : cF s x ≠ NIL) (hdir : cSz s (cLl s x) ≤ cSz s (cRr s x))
    (hlabs : (pushLabsL s x (unitCand s x true).length).run s = .ok labs s)
    (hxs : x < s.C.size) (hlS : cLl s x < s.C.size) (hrS : cRr s x < s.C.size) (hxl : x ≠ cLl s x)
    (hC : s.C.size ≤ κ.tbl .C) (hG : s.Gs.size ≤ κ.tbl .G)
    (hu : ∀ g ∈ unitCand s x true, g < s.Gs.size) (hg0 : cF s x < κ.tbl .G)
    (hsr : (s.Gs.getX (cF s x)).st = .overflow → (s.Gs.getX (cF s x)).src < κ.tbl .G)
    (hyl : cLs s (cLl s x) < κ.tbl .G) :
    ∃ L' n, evalF κ chunkSplitStepS s L = .ok (cmoveLState s x (unitCand s x true) labs) L' n ∧
      L' "ok" = 1 ∧
      L' "x" = x ∧ n ≤ 700 := by
  have hxT : x < κ.tbl .C := by omega
  set l := cLl s x
  set r := cRr s x
  set u := unitCand s x true
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "xf") (e := .cF .first "x") (v :=
    cF s x)
    (by simp [Exp.cF, Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, cF])
  set L1 := upd L "xf" (cF s x)
  have hc1 : ("xf" =ₑ 0 : Exp).ev κ s L1 = some 0 := by
    simp [Exp.ev, Machine.BinOp.eval, L1,
      Machine.State.upd]; simpa [NIL] using hne
  have h1x : L1 "x" = x := by simp [L1, Machine.State.upd, hx]
  have hlT : (s.C.getX x).l < κ.tbl .C := (show l < κ.tbl .C by omega)
  have hrT : (s.C.getX x).r < κ.tbl .C := (show r < κ.tbl .C by omega)
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "lf") (e := cssDirE) (v := b2n true)
    (by have hdir' : (s.C.getX (s.C.getX x).l).size ≤ (s.C.getX (s.C.getX x).r).size := hdir
        simp [cssDirE, Exp.cF, Exp.ev, Machine.BinOp.eval, h1x, hxT, Fld.cap,
          Fld.get, CF.get, hlT, hrT, hdir', b2n])
  set L2 := upd L1 "lf" (b2n true)
  obtain ⟨L3, c3, e3, hU3, hk3, hc3, hF3⟩ := unitS_ok (κ := κ) (s := s) (L := L2) (x := x) (left
    := true)
    (by simp [L2, Machine.State.upd,
      h1x]) (by simp [L2, Machine.State.upd]) hxT (by simpa using hg0)
    (by simpa using hsr)
  have h3x : L3 "x" = x := by
    rw [hF3 "x" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp
      [L2, Machine.State.upd, h1x]
  have h3lf : L3 "lf" = 1 := by
    rw [hF3 "lf" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [L2, Machine.State.upd, b2n]
  have a4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "y") (e := .cF .l "x") (v := l)
    (by simp [Exp.cF, Exp.ev, h3x, hxT, Fld.cap, Fld.get, CF.get, l, cLl])
  set L4 := upd L3 "y" l
  have h4uk : L4 "uk" = 1 ∨ L4 "uk" = 3 := by simpa [L4, Machine.State.upd] using hk3
  have hlen : (L4 "uk" = 1 ∧ u.length = 1) ∨ (L4 "uk" = 3 ∧ u.length = 3) := by
    have : unitOf L4 = u := by
      rw [show u = unitOf L3 from hU3.symm]; simp [unitOf, L4, Machine.State.upd]
    rcases h4uk with h | h
    · left; refine ⟨h, ?_⟩; rw [← this]; simp [unitOf, h]
    · right; refine ⟨h, ?_⟩; rw [← this]; simp [unitOf, h]
  obtain ⟨L5, c5, e5, hlab5, huk5, hc5, hF5⟩ := labLS_ok (κ := κ) (s := s) (L := L4) (y := l) (k
    := u.length)
    (labs := labs) (by simp [L4, Machine.State.upd]) hlen (by omega) hyl hlabs
  have h5 : ∀ r, r = "x" ∨ r = "y" ∨ r = "uk" ∨ r = "u0" ∨ r = "u1" ∨ r = "u2" → L5 r = L4 r := by
    intro r hr
    exact hF5 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hU4 : unitOf L4 = u := by
    rw [show u = unitOf L3 from hU3.symm]; simp [unitOf, L4, Machine.State.upd]
  have hU5 : unitOf L5 = u := by
    rw [← hU4]; simp [unitOf, h5 "uk" (by simp), h5 "u0" (by simp), h5 "u1" (by simp), h5 "u2"
      (by simp)]
  have h5x : L5 "x" = x := by rw [h5 "x" (by simp)]; simp [L4, Machine.State.upd, h3x]
  have h5y : L5 "y" = l := by rw [h5 "y" (by simp)]; simp [L4, Machine.State.upd]
  have h5k : L5 "uk" = 1 ∨ L5 "uk" = 3 := by rw [h5 "uk" (by simp)]; exact h4uk
  obtain ⟨L6, c6, e6, hc6, hF6⟩ := mgLS_ok (κ := κ) (s := s) (L := L5) (x := x) (y := l) h5x h5y
    h5k hxl hxs hlS hC
    (by rw [hU5]; intro g hg; exact ⟨hu g hg, by have := hu g hg; omega⟩)
  rw [hU5, hlab5] at e6
  set S1 := moveGroupsLeft s x l u labs
  have h6 : ∀ r, r ≠ "ul" → L6 r = L5 r := hF6
  have hU6 : unitOf L6 = u := by
    rw [← hU5]; simp [unitOf, h6 "uk" (by decide), h6 "u0" (by decide), h6 "u1" (by decide), h6
      "u2" (by decide)]
  obtain ⟨L7, c7, e7, hc7, hF7⟩ := msS_ok (κ := κ) (s := S1) (L := L6) (x := x) (y := l)
    (by rw [h6 "x" (by decide),
      h5x]) (by rw [h6 "y" (by decide), h5y]) (by rw [h6 "uk" (by decide)]; exact h5k)
    (by simp [S1, moveGroupsLeft_C_size, hxs]) (by simp [S1, moveGroupsLeft_C_size, hlS])
    (by simp [S1, moveGroupsLeft_C_size, hC]) (by rw [hU6]; intro g hg; have := hu g hg; omega)
  rw [hU6] at e7
  have e8 := evalF_assign_ok (κ := κ) (s := cmoveSizes S1 x l u) (L := L7) (x := "ok") (e := (1
    : Exp)) (v := 1) rfl
  have hc3' : (Exp.var "lf").ev κ s L3 = some 1 := by simp [Exp.ev, h3lf]
  refine ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f hc1 (evalF_seq_ok2 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3
    (evalF_seq_ok2 (evalF_ite_t hc3' one_ne_zero (evalF_seq_ok2 a4 (evalF_seq_ok2 e5 e6))) e7)))
      e8)),
    by simp [Machine.State.upd], ?_, ?_⟩
  · simp only [Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
    rw [hF7 "x" (by decide), h6 "x" (by decide), h5x]
  · simp only [Exp.cost, cssDirE, Exp.cF] at hc3 hc5 hc6 hc7 ⊢; omega

open OrderMaintenance.Proof in
theorem chunkSplitStepS_right (κ : Caps) (s : Core) (L : Loc) {x : Nat} {labs : List Nat} (hx :
  L "x" = x)
    (hne : cF s x ≠ NIL) (hdir : cSz s (cRr s x) < cSz s (cLl s x))
    (hlabs : (pushLabsR s x (unitCand s x false).length).run s = .ok labs s)
    (hxs : x < s.C.size) (hlS : cLl s x < s.C.size) (hrS : cRr s x < s.C.size) (hxl : x ≠ cRr s x)
    (hC : s.C.size ≤ κ.tbl .C) (hG : s.Gs.size ≤ κ.tbl .G)
    (hu : ∀ g ∈ unitCand s x false, g < s.Gs.size) (hg0 : cLs s x < κ.tbl .G)
    (hsr : (s.Gs.getX (cLs s x)).st = .overflow → (s.Gs.getX (cLs s x)).src < κ.tbl .G)
    (hyl : cF s (cRr s x) < κ.tbl .G) :
    ∃ L' n, evalF κ chunkSplitStepS s L = .ok (cmoveRState s x (unitCand s x false) labs) L' n ∧
      L' "ok" = 1 ∧
      L' "x" = x ∧ n ≤ 700 := by
  have hxT : x < κ.tbl .C := by omega
  set l := cLl s x
  set r := cRr s x
  set u := unitCand s x false
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "xf") (e := .cF .first "x") (v :=
    cF s x)
    (by simp [Exp.cF, Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, cF])
  set L1 := upd L "xf" (cF s x)
  have hc1 : ("xf" =ₑ 0 : Exp).ev κ s L1 = some 0 := by
    simp [Exp.ev, Machine.BinOp.eval, L1,
      Machine.State.upd]; simpa [NIL] using hne
  have h1x : L1 "x" = x := by simp [L1, Machine.State.upd, hx]
  have hlT : (s.C.getX x).l < κ.tbl .C := (show l < κ.tbl .C by omega)
  have hrT : (s.C.getX x).r < κ.tbl .C := (show r < κ.tbl .C by omega)
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "lf") (e := cssDirE) (v := b2n false)
    (by have hdir' : (s.C.getX (s.C.getX x).r).size < (s.C.getX (s.C.getX x).l).size := hdir
        have : ¬ (s.C.getX (s.C.getX x).l).size ≤ (s.C.getX (s.C.getX x).r).size := by omega
        simp [cssDirE, Exp.cF, Exp.ev, Machine.BinOp.eval, h1x, hxT, Fld.cap,
          Fld.get, CF.get, hlT, hrT, this, b2n])
  set L2 := upd L1 "lf" (b2n false)
  obtain ⟨L3, c3, e3, hU3, hk3, hc3, hF3⟩ := unitS_ok (κ := κ) (s := s) (L := L2) (x := x) (left
    := false)
    (by simp [L2, Machine.State.upd,
      h1x]) (by simp [L2, Machine.State.upd]) hxT (by simpa using hg0)
    (by simpa using hsr)
  have h3x : L3 "x" = x := by
    rw [hF3 "x" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp
      [L2, Machine.State.upd, h1x]
  have h3lf : L3 "lf" = 0 := by
    rw [hF3 "lf" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [L2, Machine.State.upd, b2n]
  have a4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "y") (e := .cF .r "x") (v := r)
    (by simp [Exp.cF, Exp.ev, h3x, hxT, Fld.cap, Fld.get, CF.get, r, cRr])
  set L4 := upd L3 "y" r
  have h4uk : L4 "uk" = 1 ∨ L4 "uk" = 3 := by simpa [L4, Machine.State.upd] using hk3
  have hlen : (L4 "uk" = 1 ∧ u.length = 1) ∨ (L4 "uk" = 3 ∧ u.length = 3) := by
    have : unitOf L4 = u := by
      rw [show u = unitOf L3 from hU3.symm]; simp [unitOf, L4, Machine.State.upd]
    rcases h4uk with h | h
    · left; refine ⟨h, ?_⟩; rw [← this]; simp [unitOf, h]
    · right; refine ⟨h, ?_⟩; rw [← this]; simp [unitOf, h]
  obtain ⟨L5, c5, e5, hlab5, huk5, hc5, hF5⟩ := labRS_ok (κ := κ) (s := s) (L := L4) (y := r) (k
    := u.length)
    (labs := labs) (by simp [L4, Machine.State.upd]) hlen (by omega) hyl hlabs
  have h5 : ∀ r, r = "x" ∨ r = "y" ∨ r = "uk" ∨ r = "u0" ∨ r = "u1" ∨ r = "u2" → L5 r = L4 r := by
    intro rr hr
    exact hF5 _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hU4 : unitOf L4 = u := by
    rw [show u = unitOf L3 from hU3.symm]; simp [unitOf, L4, Machine.State.upd]
  have hU5 : unitOf L5 = u := by
    rw [← hU4]; simp [unitOf, h5 "uk" (by simp), h5 "u0" (by simp), h5 "u1" (by simp), h5 "u2"
      (by simp)]
  have h5x : L5 "x" = x := by rw [h5 "x" (by simp)]; simp [L4, Machine.State.upd, h3x]
  have h5y : L5 "y" = r := by rw [h5 "y" (by simp)]; simp [L4, Machine.State.upd]
  have h5k : L5 "uk" = 1 ∨ L5 "uk" = 3 := by rw [h5 "uk" (by simp)]; exact h4uk
  obtain ⟨L6, c6, e6, hc6, hF6⟩ := mgRS_ok (κ := κ) (s := s) (L := L5) (x := x) (y := r) h5x h5y
    h5k hxl hxs hrS hC
    (by rw [hU5]; intro g hg; exact ⟨hu g hg, by have := hu g hg; omega⟩)
  rw [hU5, hlab5] at e6
  set S1 := moveGroupsRight s x r u labs
  have h6 : ∀ r, r ≠ "ul" → L6 r = L5 r := hF6
  have hU6 : unitOf L6 = u := by
    rw [← hU5]; simp [unitOf, h6 "uk" (by decide), h6 "u0" (by decide), h6 "u1" (by decide), h6
      "u2" (by decide)]
  obtain ⟨L7, c7, e7, hc7, hF7⟩ := msS_ok (κ := κ) (s := S1) (L := L6) (x := x) (y := r)
    (by rw [h6 "x" (by decide),
      h5x]) (by rw [h6 "y" (by decide), h5y]) (by rw [h6 "uk" (by decide)]; exact h5k)
    (by simp [S1, moveGroupsRight_C_size, hxs]) (by simp [S1, moveGroupsRight_C_size, hrS])
    (by simp [S1, moveGroupsRight_C_size, hC]) (by rw [hU6]; intro g hg; have := hu g hg; omega)
  rw [hU6] at e7
  have e8 := evalF_assign_ok (κ := κ) (s := cmoveSizes S1 x r u) (L := L7) (x := "ok") (e := (1
    : Exp)) (v := 1) rfl
  have hc3' : (Exp.var "lf").ev κ s L3 = some 0 := by simp [Exp.ev, h3lf]
  refine ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f hc1 (evalF_seq_ok2 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3
    (evalF_seq_ok2 (evalF_ite_f hc3' (evalF_seq_ok2 a4 (evalF_seq_ok2 e5 e6))) e7))) e8)),
    by simp [Machine.State.upd], ?_, ?_⟩
  · simp only [Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
    rw [hF7 "x" (by decide), h6 "x" (by decide), h5x]
  · simp only [Exp.cost, cssDirE, Exp.cF] at hc3 hc5 hc6 hc7 ⊢; omega

open OrderMaintenance.Proof in
theorem chunkSplitStepS_remove (κ : Caps) (s : Core) (L : Loc) {x : Nat} (hx : L "x" = x) (he :
  cF s x = NIL)
    (hlr : cLl s x ≠ cRr s x) (hlx : cLl s x ≠ x) (hrx : cRr s x ≠ x) (hxs : x < s.C.size)
    (hl : cSt s (cLl s x) = .overflow ∧ cSrc s (cLl s x) = x)
    (hr : cSt s (cRr s x) = .overflow ∧ cSrc s (cRr s x) = x)
    (hszl : cSz s (cLl s x) ≤ s.P.theta) (hszr : cSz s (cRr s x) ≤ s.P.theta)
    (hlS : cLl s x < s.C.size) (hrS : cRr s x < s.C.size) (hC : s.C.size ≤ κ.tbl .C) :
    ∃ L' n, evalF κ chunkSplitStepS s L = .ok (cremoveState s x) L' n ∧ L' "ok" = 0 ∧ n ≤ 200 := by
  have hxT : x < κ.tbl .C := by omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "xf") (e := .cF .first "x") (v :=
    cF s x)
    (by simp [Exp.cF, Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, cF])
  obtain ⟨L2, c2, e2, hc2⟩ := removeChunkS_agree κ s (upd L "xf" (cF s x)) (x := x)
    (by simp [Machine.State.upd, hx]) hlr hlx hrx hxs hl hr hszl hszr hlS hrS hC
  have hc : ("xf" =ₑ 0 : Exp).ev κ s (upd L "xf" (cF s x)) = some 1 := by
    simp [Exp.ev, Machine.BinOp.eval,
      Machine.State.upd]; simpa [NIL] using he
  exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t hc one_ne_zero (evalF_seq_ok2 e2 (evalF_assign_ok
    (v := 0) rfl))),
    by simp [Machine.State.upd], by simp [Exp.cost, Exp.cF] at hc2 ⊢; omega⟩

/-! ### The drive loop -/

/-- Procedure moving one chunk-split unit and reporting whether work remains. -/
def chunkSplitStepP : Proc := { name := "chunkSplitStep", params := ["x"], rets := ["ok"], body
  := chunkSplitStepS }
/-- Perform one chunk-split step unless an earlier iteration finished the split. -/
def cdriveBody : Stm := cm{ if dn = 0 then { ok ← chunkSplitStepP(x); if ok = 0 then dn := 1 } }
/-- `driveChunkFrom g`: up to `chunkBudget` split steps, stopping once `g` is removed. -/
def driveChunkFromS : Stm := cm{ dn := 0; for jj < P.KC do cdriveBody }

/-- A Level M split step that agrees with a Level F one (`b` = Level F's result). -/
def CStepAgree (κ : Caps) (p : Nat) (t t' : Core) (b : Bool) : Prop :=
  ∀ L : Loc, L "x" = p → ∃ L' n, evalF κ chunkSplitStepS t L = .ok t' L' n ∧ L' "ok" = b2n b ∧ n
    ≤ 700

/-- The body of Level F's drive loop. -/
def cdriveF (p : Nat) : Nat → Option Unit × Unit → CM (ForInStep (Option Unit × Unit)) :=
  fun _ _ => do
    let b ← chunkSplitStep p
    if (!b) = true then pure (ForInStep.done (some (), ())) else pure (ForInStep.yield (none, ()))

theorem cdriveF_run_true {p j : Nat} {t t' : Core} {a : Option Unit × Unit} (h : (chunkSplitStep
  p).run t = .ok true t') :
    (cdriveF p j a).run t = .ok (.yield (none, ())) t' := by
  simp only [cdriveF, OrderMaintenance.Proof.run_bind, h]; rfl

theorem cdriveF_run_false {p j : Nat} {t t' : Core} {a : Option Unit × Unit} (h :
  (chunkSplitStep p).run t = .ok false t') :
    (cdriveF p j a).run t = .ok (.done (some (), ())) t' := by
  simp only [cdriveF, OrderMaintenance.Proof.run_bind, h]; rfl

theorem driveChunkFromS_agree (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "x" = p)
    (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.chunkBudget → ∃ b t', (chunkSplitStep p).run t = .ok b t' ∧
      (b = true → I (j + 1) t') ∧ CStepAgree κ p t t' b) :
    ∃ t' L' n, (driveChunkFrom p).run s = .ok () t' ∧ evalF κ driveChunkFromS s L = .ok t' L' n ∧
      n ≤ 5 + s.P.chunkBudget * 751 := by
  set K := s.P.chunkBudget
  set R := fun (l : List Nat) (t : Core) => (forIn l ((none : Option Unit), ()) (cdriveF p)).run t
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
      · exact ⟨_, _, by
        simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, cdriveF_run_false hr]; rfl⟩
      · obtain ⟨c, tF, h⟩ := ih (j + 1) t' (hI' rfl) (by omega)
        exact ⟨c, tF, by
          simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, cdriveF_run_true hr]
          exact h⟩
  obtain ⟨c0, tF, hR0⟩ := hF K 0 s h0 (by omega)
  simp only [List.drop_zero] at hR0
  -- Level F's result
  have hFrun : (driveChunkFrom p).run s = .ok () tF := by
    unfold driveChunkFrom
    rw [OrderMaintenance.Proof.run_getP_bind, OrderMaintenance.Proof.run_bind]
    have hR0' : (forIn (List.range s.P.chunkBudget) ((none : Option Unit), ()) (fun (_ : Nat) (_
      : Option Unit × Unit) => do
        let b ← chunkSplitStep p
        if (!b) = true then pure (ForInStep.done (some (), ())) else pure (ForInStep.yield
          (none, ())))).run s =
        .ok c0 tF := hR0
    rw [hR0']
    dsimp only
    split <;> rfl
  -- Level M's loop
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "dn") (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨S', L', c, he, hc, -, hI⟩ := evalF_loop (κ := κ) (x := "jj") (n := .prm .KC) (b :=
    cdriveBody) (s := s)
    (L := upd L "dn" 0) (N := K) (by simp [Exp.ev, PF.get, K])
    (fun j S L' => L' "x" = p ∧ ((L' "dn" = 0 ∧ I j S ∧ ∃ c, R ((List.range K).drop j) S = .ok c
      tF) ∨
      (L' "dn" = 1 ∧ S = tF))) 750
    ⟨by simp [Machine.State.upd,
      hg], Or.inl ⟨by simp [Machine.State.upd], h0, c0, by simpa using hR0⟩⟩
    (by
      intro j hj S L1 ⟨h1x, hcase⟩
      set L2 := upd L1 "jj" j
      have h2x : L2 "x" = p := by simp [L2, Machine.State.upd, h1x]
      rcases hcase with ⟨hdn, hIj, c1, hR⟩ | ⟨hdn, hSF⟩
      · have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 1 := by simp [Exp.ev, Machine.BinOp.eval, L2,
          Machine.State.upd, hdn]
        obtain ⟨b, t', hr, hI', hSA⟩ := hstep j S hIj hj
        obtain ⟨Lg, ng, eg, hok, hng⟩ := hSA (Machine.State.setLocs (fun _ => 0) ["x"] [p])
          (by simp [Machine.State.setLocs, Machine.State.upd])
        have ec := evalF_call_ok (q := chunkSplitStepP) (args := [.var "x"]) (ds := ["ok"]) (L
          := L2)
          (by simp [evList, Exp.ev, h2x]) eg
        set L3 := Machine.State.setLocs L2 ["ok"] (chunkSplitStepP.rets.map Lg)
        have h3ok : L3 "ok" = b2n b := by
          simp [L3, chunkSplitStepP, Machine.State.setLocs, Machine.State.upd, hok]
        have h3x : L3 "x" = p := by
          simp [L3, chunkSplitStepP, Machine.State.setLocs, Machine.State.upd, h2x]
        have h3dn : L3 "dn" = 0 := by
          simp [L3, L2, chunkSplitStepP, Machine.State.setLocs, Machine.State.upd, hdn]
        rw [List.drop_eq_getElem_cons (by simpa using hj), List.getElem_range] at hR
        cases b
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind,
          cdriveF_run_false hr] at hR
          injection hR with _ hT; subst hT
          have e4 := evalF_assign_ok (κ := κ) (s := t') (L := L3) (x := "dn") (e := (1 : Exp))
            (v := 1) rfl
          refine ⟨t', _, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 ec (evalF_ite_t (v := 1)
            (by simp [Exp.ev, Machine.BinOp.eval, h3ok, b2n]) one_ne_zero e4)), ?_,
            by simp [Machine.State.upd,
              h3x], Or.inr ⟨by simp [Machine.State.upd], rfl⟩⟩
          simp [Exp.cost, costList] at hng ⊢; omega
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, cdriveF_run_true hr] at hR
          refine ⟨t', _, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 ec (evalF_ite_f
            (by simp [Exp.ev, Machine.BinOp.eval, h3ok,
              b2n]) evalF_skip)), ?_, h3x,
            Or.inl ⟨h3dn, hI' rfl, c1, hR⟩⟩
          simp [Exp.cost, costList] at hng ⊢; omega
      · subst hSF
        have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 0 := by simp [Exp.ev, Machine.BinOp.eval, L2,
          Machine.State.upd, hdn]
        exact ⟨S, L2, _, evalF_ite_f hc0 evalF_skip, by simp [Exp.cost], h2x,
          Or.inr ⟨by simp [L2, Machine.State.upd, hdn], rfl⟩⟩)
  have hS' : S' = tF := by
    rcases hI with ⟨hdn, hIK, c2, hR⟩ | ⟨hdn, h⟩
    · rw [List.drop_of_length_le (by simp)] at hR
      simp only [R] at hR
      injection hR
    · exact h
  subst hS'
  refine ⟨S', L', _, hFrun, evalF_seq_ok2 a1 he, ?_⟩
  simp only [Exp.cost] at hc ⊢; omega

/-! ### `driveChunk` -/

/-- Procedure performing at most the configured chunk-split budget. -/
def cdriveP : Proc := { name := "driveChunkFrom", params := ["x"], rets := [], body :=
  driveChunkFromS }
/-- `driveChunk g`: drive the split `g` belongs to, if any (local `g`). -/
def driveChunkS : Stm := cm{
  st := C[x].st
  if st = 2 then call cdriveP(x)
  else if st = 1 then call cdriveP(C[x].src) }

/-- The drive of the split rooted at `q` agrees at Level M, ending in `t'`. -/
def CDriveAgree (κ : Caps) (q : Nat) (s t' : Core) : Prop :=
  (driveChunkFrom q).run s = .ok () t' ∧
    ∀ L : Loc, L "x" = q → ∃ L' n, evalF κ driveChunkFromS s L = .ok t' L' n ∧ n ≤ 5 +
      s.P.chunkBudget * 751

theorem driveChunkFromS_agree' (κ : Caps) (s : Core) {p : Nat} (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.chunkBudget → ∃ b t', (chunkSplitStep p).run t = .ok b t' ∧
      (b = true → I (j + 1) t') ∧ CStepAgree κ p t t' b) : ∃ t', CDriveAgree κ p s t' := by
  obtain ⟨t', L1, n1, hF, -, -⟩ := driveChunkFromS_agree κ s (fun _ => p) (p := p) rfl I h0 hstep
  refine ⟨t', hF, fun L hL => ?_⟩
  obtain ⟨t'', L', n, hF', he, hn⟩ := driveChunkFromS_agree κ s L (p := p) hL I h0 hstep
  rw [hF] at hF'; injection hF' with _ h; subst h; exact ⟨L', n, he, hn⟩

theorem driveChunk_split {s : Core} {g : Nat} (h : (s.C.getX g).st = .splitting) :
    (driveChunk g).run s = (driveChunkFrom g).run s := by
  unfold driveChunk; rw [OrderMaintenance.Proof.run_getC_bind, h]

theorem driveChunk_ovf {s : Core} {g : Nat} (h : (s.C.getX g).st = .overflow) :
    (driveChunk g).run s = (driveChunkFrom (s.C.getX g).src).run s := by
  unfold driveChunk; rw [OrderMaintenance.Proof.run_getC_bind, h]

theorem driveChunk_quiet {s : Core} {g : Nat} (h : (s.C.getX g).st = .quiet) : (driveChunk
  g).run s = .ok () s := by
  unfold driveChunk; rw [OrderMaintenance.Proof.run_getC_bind, h]; rfl

theorem driveChunk_dead {s : Core} {g : Nat} (h : (s.C.getX g).st = .dead) : (driveChunk g).run
  s = .ok () s := by
  unfold driveChunk; rw [OrderMaintenance.Proof.run_getC_bind, h]; rfl

theorem driveChunkS_agree (κ : Caps) (s : Core) (L : Loc) {g : Nat} (hg : L "x" = g) (hgT : g <
  κ.tbl .C)
    {σ' : Core} (h : (driveChunk g).run s = .ok () σ')
    (hA : ∀ q, ((s.C.getX g).st = .splitting ∧ q = g ∨ (s.C.getX g).st = .overflow ∧ q =
      (s.C.getX g).src) →
      CDriveAgree κ q s σ') :
    ∃ L' n, evalF κ driveChunkS s L = .ok σ' L' n ∧ n ≤ 30 + s.P.chunkBudget * 751 := by
  set G := s.C.getX g
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "st") (e := .cF .st "x") (v :=
    G.st.toN)
    (by simp [Exp.cF, Exp.ev, hg, hgT, Fld.cap, Fld.get, CF.get, G])
  set L1 := upd L "st" G.st.toN
  have h1x : L1 "x" = g := by simp [L1, Machine.State.upd, hg]
  have c1 : ("st" =ₑ 2 : Exp).ev κ s L1 = some (if G.st.toN = 2 then 1 else 0) := by
    simp [Exp.ev, Machine.BinOp.eval, L1, Machine.State.upd]
  have c2 : ("st" =ₑ 1 : Exp).ev κ s L1 = some (if G.st.toN = 1 then 1 else 0) := by
    simp [Exp.ev, Machine.BinOp.eval, L1, Machine.State.upd]
  cases hst : G.st with
  | splitting =>
    rw [hst] at c1; simp only [St.toN, ite_true] at c1
    obtain ⟨-, hM⟩ := hA g (Or.inl ⟨hst, rfl⟩)
    obtain ⟨Ld, nd, ed, hnd⟩ := hM (Machine.State.setLocs (fun _ => 0) ["x"] [g])
      (by simp [Machine.State.setLocs, Machine.State.upd])
    have ec := evalF_call_ok (q := cdriveP) (args := [.var "x"]) (ds := []) (L := L1) (by simp
      [evList, Exp.ev, h1x]) ed
    exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t c1 one_ne_zero ec), by
      simp [Exp.cost, costList, Exp.cF] at hnd ⊢
      omega⟩
  | overflow =>
    rw [hst] at c1 c2; simp only [St.toN, ite_true] at c1 c2
    obtain ⟨-, hM⟩ := hA G.src (Or.inr ⟨hst, rfl⟩)
    obtain ⟨Ld, nd, ed, hnd⟩ := hM (Machine.State.setLocs (fun _ => 0) ["x"] [G.src])
      (by simp [Machine.State.setLocs, Machine.State.upd])
    have ec := evalF_call_ok (q := cdriveP) (args := [.cF .src "x"]) (ds := []) (L := L1)
      (by simp [evList, Exp.cF, Exp.ev, h1x, hgT, Fld.cap, Fld.get, CF.get, G]) ed
    exact ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_f (by simpa using c1) (evalF_ite_t c2 one_ne_zero ec)),
      by simp [Exp.cost, costList, Exp.cF] at hnd ⊢; omega⟩
  | quiet =>
    rw [driveChunk_quiet hst] at h
    injection h with _ hs; subst hs
    rw [hst] at c1 c2; simp only [St.toN] at c1 c2
    have i2 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 1 : Exp)) (t := cdriveP.call [.cF .src "x"]
      []) (by simpa using c2)
      evalF_skip
    have i1 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 2 : Exp)) (t := cdriveP.call [.var "x"] [])
      (by simpa using c1) i2
    exact ⟨_, _, evalF_seq_ok2 a1 i1, by simp [Exp.cost, Exp.cF]; omega⟩
  | dead =>
    rw [driveChunk_dead hst] at h
    injection h with _ hs; subst hs
    rw [hst] at c1 c2; simp only [St.toN] at c1 c2
    have i2 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 1 : Exp)) (t := cdriveP.call [.cF .src "x"]
      []) (by simpa using c2)
      evalF_skip
    have i1 := evalF_ite_f (κ := κ) (c := ("st" =ₑ 2 : Exp)) (t := cdriveP.call [.var "x"] [])
      (by simpa using c1) i2
    exact ⟨_, _, evalF_seq_ok2 a1 i1, by simp [Exp.cost, Exp.cF]; omega⟩

end OrderMaintenance.Impl
