/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.ArrayLemmas
public import LeanPool.OrderMaintenance.Impl.PQ
public import LeanPool.OrderMaintenance.Impl.CM


/-!
# M6: elements (`Model/Core.lean`: insertion, deletion, order)
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)


/-- `linkElem`: link the new element `y` after `x` (locals `x g glast nx lab h`). -/
def linkElemS : Stm := cm{
  y := new E
  E[y].grp := g; E[y].lab := lab; E[y].h := h; E[y].prev := x
  E[y].next := nx
  if nx ≠ 0 then E[nx].prev := y
  E[x].next := y
  if S.tail = x then S.tail := y
  if glast = x then G[g].last := y
  G[g].size := G[g].size + 1
  S.count := S.count + 1 }

theorem linkElemS_agree (κ : Caps) (σ : Core) (L : Loc) {x lab hh : Nat} (hx : L "x" = x)
    (hg : L "g" = (σ.E.getX x).grp) (hgl : L "glast" = (σ.Gs.getX (σ.E.getX x).grp).last)
    (hnx : L "nx" = (σ.E.getX x).next) (hlab : L "lab" = lab) (hl : L "h" = hh)
    (hxE : x < σ.E.size) (hgG : (σ.E.getX x).grp < σ.Gs.size)
    (hnE : (σ.E.getX x).next = 0 ∨ (σ.E.getX x).next < σ.E.size)
    (hE : σ.E.size < κ.tbl .E) (hG : σ.Gs.size ≤ κ.tbl .G) :
    ∃ L' n, evalF κ linkElemS σ L = .ok (linkElem σ x σ.E.size lab hh) L' n ∧
      L' "y" = σ.E.size ∧ n ≤ 120 := by
  have hgC : (σ.E.getX x).grp < κ.tbl .G := by omega
  have hxs : x < σ.E.size + 1 := by omega
  have hxne : x ≠ σ.E.size := by omega
  have hxC : x < κ.tbl .E := by omega
  by_cases hn0 : (σ.E.getX x).next = 0 <;> by_cases ht : σ.tail = x <;>
    by_cases hlast : (σ.Gs.getX (σ.E.getX x).grp).last = x
  all_goals (try have hnlt : (σ.E.getX x).next < σ.E.size := by omega)
  all_goals (try have hnC : (σ.E.getX x).next < κ.tbl .E := by omega)
  all_goals (try have hnx' : (σ.E.getX x).next < σ.E.size + 1 := by omega)
  all_goals (try have hnle : (σ.E.getX x).next ≤ σ.E.size := by omega)
  all_goals simp only [linkElemS, Stm.weF, Exp.ofNat_def, Exp.sc, Stm.wsc, Stm.wgF, Exp.gF,
      Exp.add_def, evalF, Res.bind, Tbl.size, hE, ↓reduceIte, Tbl.push, ht, pushCost,
      Res.addCost, Exp.ev, Machine.State.upd, String.reduceEq, hg, Fld.set,
      Array.size_push, lt_add_iff_pos_right, zero_lt_one, EF.ok, and_self, Exp.cost,
      Nat.reduceAdd, hlab, Array.size_modify, hl, hx, hnx, hn0, BinOp.eval,
      Option.bind_some, Option.map_some, UnOp.eval, one_ne_zero, ne_eq,
      not_true_eq_false, hxs, Fld.cap, Nat.lt_one_iff, Fld.get, SF.get,
      not_false_eq_true, SF.ok, SF.set, hgl, hlast, hgG, GF.ok, GF.get,
      Proof.Array.getX_modify, and_true, hgC, Res.ok.injEq, ↓existsAndEq,
      Nat.reduceLeDiff, hnx']
  all_goals
    simp only [linkElem, NIL, Array.modify_modify_same, Array.modify_push_size, hn0, ht,
      bne_iff_ne, ne_eq,
      beq_iff_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
  all_goals
    congr 1
  all_goals (try (apply Array.modify_congr_getX; simp only [GF.set, Function.comp_apply, hlast,
      ↓reduceIte]))

/-- The label of the new element, guarded. -/
def insertElemPre : Stm := cm{
  g := E[x].grp
  glast := G[g].last
  exlab := E[x].lab
  nx := E[x].next
  if x = glast then {
    v := exlab + P.De
    if 1 <<< P.Be ≤ v || v ≤ exlab then fail
    lab := v }
  else {
    b := E[nx].lab
    if b ≤ exlab + 1 then fail
    lab := (exlab + b) / 2 } }

/-- `insertElem x h`: a new element with handle `h` right after `x`. -/
def insertElemP : Proc where
  name := "insertElem"
  params := ["x", "h"]
  rets := ["y"]
  body := insertElemPre;; linkElemS

theorem insertElem_agree (κ : Caps) (σ : Core) (L : Loc) {x hh : Nat} (hx : L "x" = x) (hl : L
  "h" = hh)
    (hxE : x < σ.E.size) (hgG : (σ.E.getX x).grp < σ.Gs.size)
    (hnE : (σ.E.getX x).next = 0 ∨ (σ.E.getX x).next < σ.E.size)
    (hE : σ.E.size < κ.tbl .E) (hG : σ.Gs.size ≤ κ.tbl .G) {y : Nat} {σ' : Core}
    (h : (insertElem x hh).run σ = .ok y σ') :
    ∃ L' n, evalF κ insertElemP.body σ L = .ok σ' L' n ∧ L' "y" = y ∧ n ≤ 200 := by
  unfold insertElem at h
  simp only [getP, bind_pure_comp, getE, getG, beq_iff_eq, after, ge_iff_le,
      add_le_iff_nonpos_right, nonpos_iff_eq_zero, Bool.or_eq_true, decide_eq_true_eq,
      Model.guard, between, bind_map_left, EStateM.run_bind, EStateM.run_get, Proof.run_ite,
      EStateM.run_pure] at h
  have hgC : (σ.E.getX x).grp < κ.tbl .G := by omega
  have hxC : x < κ.tbl .E := by omega
  have hnC : (σ.E.getX x).next < κ.tbl .E := by omega
  -- the label and its guard, then the common linking
  suffices hpre : ∃ lab L1 c1, evalF κ insertElemPre σ L = .ok σ L1 c1 ∧
      L1 "x" = x ∧ L1 "g" = (σ.E.getX x).grp ∧ L1 "glast" = (σ.Gs.getX (σ.E.getX x).grp).last ∧
      L1 "nx" = (σ.E.getX x).next ∧ L1 "lab" = lab ∧ L1 "h" = hh ∧ c1 ≤ 80 ∧
      σ' = linkElem σ x σ.E.size lab hh ∧ y = σ.E.size by
    obtain ⟨lab, L1, c1, he, h1, h2, h3, h4, h5, h6, hc, rfl, rfl⟩ := hpre
    obtain ⟨L', n, he', hy, hn⟩ := linkElemS_agree κ σ L1 h1 h2 h3 h4 h5 h6 hxE hgG hnE hE hG
    simp only [insertElemP]
    rw [evalF_seq_ok he, he']
    exact ⟨L', c1 + n, rfl, hy, by omega⟩
  by_cases hlast : x = (σ.Gs.getX (σ.E.getX x).grp).last
  · rw [ite_eq_left hlast] at h
    by_cases hg : 1 <<< σ.P.elementBits ≤ (σ.E.getX x).lab + σ.P.elementSpacing ∨
      σ.P.elementSpacing = 0
    · rw [ite_eq_left hg] at h; cases h
    · rw [ite_eq_right hg] at h
      simp only [] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc1 : (x = (σ.Gs.getX (σ.E.getX x).grp).last) = True := eq_true hlast
      have hc2 : ((σ.E.getX x).lab + σ.P.elementSpacing < 2 ^ σ.P.elementBits ∧
        ¬σ.P.elementSpacing = 0) = True := by
        apply eq_true; rw [Nat.shiftLeft_eq, one_mul] at hg; omega
      refine ⟨(σ.E.getX x).lab + σ.P.elementSpacing, ?_⟩
      simp only [insertElemPre, Exp.eF, Exp.gF, Exp.add_def, Exp.ofNat_def, Exp.div_def, evalF,
          Res.bind, Exp.ev, hx, Fld.cap, Fld.get, EF.get, Option.bind_some, hxC,
          ↓reduceIte, Exp.cost, Nat.reduceAdd, Res.addCost, Machine.State.upd, GF.get, hgC,
          String.reduceEq, BinOp.eval, hc1, ne_eq, one_ne_zero, not_false_eq_true, PF.get,
          one_mul, add_le_iff_nonpos_right, nonpos_iff_eq_zero, ite_eq_right_iff,
          imp_false, Decidable.not_not, not_le, not_lt, not_or, hc2, not_true_eq_false,
          Res.ok.injEq, true_and, and_self, and_true, ↓existsAndEq, Nat.reduceLeDiff,
          exists_eq_left',  hl]
  · rw [ite_eq_right hlast] at h
    by_cases hg : (σ.E.getX (σ.E.getX x).next).lab ≤ (σ.E.getX x).lab + 1
    · rw [ite_eq_left hg] at h; cases h
    · rw [ite_eq_right hg] at h
      simp only [] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc1 : (x = (σ.Gs.getX (σ.E.getX x).grp).last) = False := eq_false hlast
      have hc2 : ((σ.E.getX x).lab + 1 < (σ.E.getX (σ.E.getX x).next).lab) = True := by
        apply eq_true; omega
      refine ⟨((σ.E.getX x).lab + (σ.E.getX (σ.E.getX x).next).lab) / 2, ?_⟩
      simp only [insertElemPre, Exp.eF, Exp.gF, Exp.add_def, Exp.ofNat_def, Exp.div_def, evalF,
          Res.bind, Exp.ev, hx, Fld.cap, Fld.get, EF.get, Option.bind_some, hxC,
          ↓reduceIte, Exp.cost, Nat.reduceAdd, Res.addCost, Machine.State.upd, GF.get, hgC,
          String.reduceEq, BinOp.eval, hc1, ne_eq, not_true_eq_false, hnC,
          ite_eq_right_iff, one_ne_zero, imp_false, not_le, hc2, Res.ok.injEq, true_and,
          and_self, and_true, ↓existsAndEq, Nat.reduceLeDiff, exists_eq_left', hl]

def markDeadP : Proc where
  name := "markDead"
  params := ["x"]
  rets := []
  body := cm{ E[x].dead := 1 }

theorem markDead_agree (κ : Caps) (σ : Core) (L : Loc) {x : Nat} (hx : L "x" = x) (hxE : x <
  σ.E.size)
    (_hE : σ.E.size ≤ κ.tbl .E) {σ' : Core} (h : (markDead x).run σ = .ok () σ') :
    ∃ L' n, evalF κ markDeadP.body σ L = .ok σ' L' n ∧ n ≤ 5 := by
  unfold markDead modE at h
  simp only [EStateM.run_modify, EStateM.Result.ok.injEq, true_and] at h; subst h
  simp only [markDeadP, Stm.weF, Exp.ofNat_def, evalF, Exp.ev, hx, Fld.set, hxE, EF.ok,
      Std.le_refl, decide_true, and_self, ↓reduceIte, Exp.cost, Nat.reduceAdd, Res.ok.injEq,
      Core.mk.injEq, and_true, true_and, ↓existsAndEq, Nat.reduceLeDiff, exists_and_left]
  rfl

/-- The key of element `e`: its chunk's tag, its group's label, its own label. -/
def keyS (e t g l : Reg) : Stm := cm{
  ‹g› := E[‹e›].grp
  ‹l› := E[‹e›].lab
  ‹t› := C[G[‹g›].chk].tag
  ‹g› := G[‹g›].lab }

def orderP : Proc where
  name := "order"
  params := ["x", "y"]
  rets := ["r"]
  body := cm{
    ‹keyS "x" "ta" "ga" "ea"›
    ‹keyS "y" "tb" "gb" "eb"›
    r := ta < tb || (ta = tb && (ga < gb || (ga = gb && ea < eb))) }

theorem order_agree (κ : Caps) (σ : Core) (L : Loc) {x y : Nat} (hx : L "x" = x) (hy : L "y" = y)
    (hxE : x < κ.tbl .E) (hyE : y < κ.tbl .E) (hxG : (σ.E.getX x).grp < κ.tbl .G)
    (hyG : (σ.E.getX y).grp < κ.tbl .G) (hxC : (σ.Gs.getX (σ.E.getX x).grp).chk < κ.tbl .C)
    (hyC : (σ.Gs.getX (σ.E.getX y).grp).chk < κ.tbl .C) {b : Bool} {σ' : Core}
    (h : (OrderMaintenance.Model.order x y).run σ = .ok b σ') :
    ∃ L' n, evalF κ orderP.body σ L = .ok σ' L' n ∧ L' "r" = b2n b ∧ n ≤ 80 := by
  unfold OrderMaintenance.Model.order key at h
  simp only [getE, bind_pure_comp, getG, getC, Functor.map_map, bind_map_left, map_bind,
      bind_assoc, EStateM.run_bind, EStateM.run_get] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [orderP, keyS, Exp.eF, Exp.cF, Exp.gF, evalF, Res.bind, Exp.ev, hx, Fld.cap, Fld.get,
      EF.get, Option.bind_some, hxE, ↓reduceIte, Exp.cost, Nat.reduceAdd, Res.addCost,
      Machine.State.upd, String.reduceEq, GF.get, hxG, CF.get, hxC, hy, hyE, hyG, hyC,
      BinOp.eval, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_lt, not_le,
      Decidable.not_not, not_and, not_imp, not_or, Res.ok.injEq, true_and, b2n, keyLt,
      Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, ↓existsAndEq, and_true,
      Nat.reduceLeDiff, exists_eq_left']
  congr 1
  apply propext
  omega

end OrderMaintenance.Impl
