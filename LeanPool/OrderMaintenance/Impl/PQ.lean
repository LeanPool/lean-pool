/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Notation


/-!
# M6: the priority queue in the core language (`Model/PQ.lean`)
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)

/-! ### Capacities

The queue's arrays are indexed by chunk (`pqNext`, `pqPrev`, `pqWhere`: capacity `κ.arr .pqNext`)
or by bucket (`pqHead`, `nbNext`, `nbPrev`: capacity `κ.arr .pqHead`), and hold chunks or
buckets. `PQCaps` says every stored value fits.
-/

/-- Capacity shared by the priority queue's chunk-indexed arrays. -/
abbrev Ccap (κ : Caps) : Nat := κ.arr .pqNext
/-- Capacity shared by the priority queue's bucket-indexed arrays. -/
abbrev Bcap (κ : Caps) : Nat := κ.arr .pqHead

/-- Compatible queue-array capacities covering every allocated chunk and bucket. -/
structure PQCaps (κ : Caps) (σ : Core) : Prop where
  cC : κ.arr .pqPrev = Ccap κ ∧ κ.arr .pqWhere = Ccap κ
  cB : κ.arr .nbNext = Bcap κ ∧ κ.arr .nbPrev = Bcap κ
  next : ∀ i, σ.pqNext.getX i < Ccap κ
  prev : ∀ i, σ.pqPrev.getX i < Ccap κ
  head : ∀ i, σ.pqHead.getX i < Ccap κ
  where_ : ∀ i, σ.pqWhere.getX i < Bcap κ
  nbN : ∀ i, σ.nbNext.getX i < Bcap κ
  nbP : ∀ i, σ.nbPrev.getX i < Bcap κ
  lo : σ.pqLo < Bcap κ
  hi : σ.pqHi < Bcap κ

theorem getX_setX_lt {a : Array Nat} {i v B : Nat} (ha : ∀ j, a.getX j < B) (hv : v < B) (j : Nat) :
    (a.setX i v).getX j < B := by
  rw [OrderMaintenance.Proof.Top.getX_setX']; split
  · exact hv
  · exact ha j

namespace PQCaps
variable {κ : Caps} {σ : Core} (h : PQCaps κ σ)
include h

theorem sNext {i v : Nat} (hv : v < Ccap κ) : PQCaps κ { σ with pqNext := σ.pqNext.setX i v } :=
  { h with next := getX_setX_lt h.next hv }
theorem sPrev {i v : Nat} (hv : v < Ccap κ) : PQCaps κ { σ with pqPrev := σ.pqPrev.setX i v } :=
  { h with prev := getX_setX_lt h.prev hv }
theorem sHead {i v : Nat} (hv : v < Ccap κ) : PQCaps κ { σ with pqHead := σ.pqHead.setX i v } :=
  { h with head := getX_setX_lt h.head hv }
theorem sWhere {i v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with pqWhere := σ.pqWhere.setX i v } :=
  { h with where_ := getX_setX_lt h.where_ hv }
theorem sNbN {i v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with nbNext := σ.nbNext.setX i v } :=
  { h with nbN := getX_setX_lt h.nbN hv }
theorem sNbP {i v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with nbPrev := σ.nbPrev.setX i v } :=
  { h with nbP := getX_setX_lt h.nbP hv }
theorem sLo {v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with pqLo := v } := { h with lo := hv }
theorem sHi {v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with pqHi := v } := { h with hi := hv }

end PQCaps

/-- Prove `PQCaps κ σ'` for a state obtained from `σ` (with `hq : PQCaps κ σ`) by bounded writes. -/
macro "pq_caps " hq:term : tactic => `(tactic| (
  refine ⟨($hq).cC, ($hq).cB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try intro i) <;>
  simp only [OrderMaintenance.Proof.Top.getX_setX', NIL] <;> (repeat' split) <;>
  first
  | exact ($hq).next _
  | exact ($hq).prev _
  | exact ($hq).head _
  | exact ($hq).where_ _
  | exact ($hq).nbN _
  | exact ($hq).nbP _
  | exact ($hq).lo
  | exact ($hq).hi
  | omega))

/-- Procedure linking a newly nonempty bucket after its predecessor. -/
def pqLinkAfterP : Proc where
  name := "pqLinkAfter"
  params := ["s", "p"]
  rets := []
  body :=
    .ite ("p" =ₑ 0) ("n" ::= .sc .pqLo) ("n" ::= .ar .nbNext "p");;
    .ite ("p" =ₑ 0) (.wsc .pqLo "s") (.war .nbNext "p" "s");;
    .war .nbPrev "s" "p";;
    .war .nbNext "s" "n";;
    .ite (!ₑ ("n" =ₑ 0)) (.war .nbPrev "n" "s") (.wsc .pqHi "s")

theorem pqLinkAfter_agree (κ : Caps) (σ : Core) (L : Loc) {s p : Nat} (hs : L "s" = s) (hp : L
  "p" = p)
    (hq : PQCaps κ σ) (hsB : s < Bcap κ) (hpB : p < Bcap κ) {σ' : Core}
    (h : (pqLinkAfter s p).run σ = .ok () σ') :
    (∃ L' c, evalF κ pqLinkAfterP.body σ L = .ok σ' L' c ∧ c ≤ 60) ∧ PQCaps κ σ' := by
  unfold pqLinkAfter at h
  simp only [pqLinkAfterP]
  have hcs : s < κ.arr .nbPrev ∧ s < κ.arr .nbNext := by rw [hq.cB.1, hq.cB.2]; exact ⟨hsB, hsB⟩
  have hcp : p < κ.arr .nbNext := by rw [hq.cB.1]; exact hpB
  by_cases hp0 : p = 0
  · subst hp0
    have hn : σ.pqLo < κ.arr .nbPrev := by rw [hq.cB.2]; exact hq.lo
    by_cases hn0 : σ.pqLo = 0
    · simp only [BEq.rfl, ↓reduceIte, bne_iff_ne, ne_eq, ite_not, EStateM.run_bind,
        EStateM.run_get, hn0, EStateM.run_modify, EStateM.Result.ok.injEq, true_and, evalF,
        Res.bind, Exp.ev, hp, BinOp.eval, Option.bind_some, Res.addCost, one_ne_zero,
        not_false_eq_true, Exp.sc, Exp.ofNat_def, Fld.cap, Nat.lt_one_iff, Fld.get, SF.get,
        Exp.cost, Nat.reduceAdd, Machine.State.upd, String.reduceEq, Stm.wsc, hs, Fld.set,
        zero_lt_one, SF.ok, and_self, SF.set, Stm.war, hcs.1, AF.set, AF.get, hcs.2,
        Option.map_some, UnOp.eval, not_true_eq_false, Res.ok.injEq, ↓existsAndEq,
        and_true, Nat.reduceLeDiff, exists_and_left] at h ⊢
      cases h
      exact ⟨by rfl, by
        pq_caps hq⟩
    · simp only [BEq.rfl, ↓reduceIte, bne_iff_ne, ne_eq, ite_not, EStateM.run_bind,
        EStateM.run_get, hn0, EStateM.run_modify, EStateM.Result.ok.injEq, true_and, evalF,
        Res.bind, Exp.ev, hp, BinOp.eval, Option.bind_some, Res.addCost, one_ne_zero,
        not_false_eq_true, Exp.sc, Exp.ofNat_def, Fld.cap, Nat.lt_one_iff, Fld.get, SF.get,
        Exp.cost, Nat.reduceAdd, Machine.State.upd, String.reduceEq, Stm.wsc, hs, Fld.set,
        zero_lt_one, SF.ok, and_self, SF.set, Stm.war, hcs.1, AF.set, AF.get, hcs.2,
        Option.map_some, UnOp.eval, hn, Res.ok.injEq, ↓existsAndEq, and_true,
        Nat.reduceLeDiff, exists_and_left] at h ⊢
      cases h
      exact ⟨by rfl, by
        pq_caps hq⟩
  · have hn : σ.nbNext.getX p < κ.arr .nbPrev := by rw [hq.cB.2]; exact hq.nbN p
    by_cases hn0 : σ.nbNext.getX p = 0
    · simp only [beq_iff_eq, hp0, ↓reduceIte, bne_iff_ne, ne_eq, ite_not, EStateM.run_bind,
        EStateM.run_get, hn0, EStateM.run_modify, EStateM.Result.ok.injEq, true_and, evalF,
        Res.bind, Exp.ev, hp, BinOp.eval, Option.bind_some, Res.addCost, not_true_eq_false,
        Exp.ar, Fld.cap, Fld.get, AF.get, hcp, Exp.cost, Nat.reduceAdd, Machine.State.upd,
        String.reduceEq, Stm.war, hs, Fld.set, AF.set, hcs.1, hcs.2, Option.map_some,
        UnOp.eval, one_ne_zero, Stm.wsc, Exp.ofNat_def, zero_lt_one, SF.ok, and_self,
        SF.set, Res.ok.injEq, ↓existsAndEq, and_true, Nat.reduceLeDiff, exists_and_left] at h ⊢
      cases h
      exact ⟨by rfl, by
        pq_caps hq⟩
    · simp only [beq_iff_eq, hp0, ↓reduceIte, bne_iff_ne, ne_eq, ite_not, EStateM.run_bind,
        EStateM.run_get, hn0, EStateM.run_modify, EStateM.Result.ok.injEq, true_and, evalF,
        Res.bind, Exp.ev, hp, BinOp.eval, Option.bind_some, Res.addCost, not_true_eq_false,
        Exp.ar, Fld.cap, Fld.get, AF.get, hcp, Exp.cost, Nat.reduceAdd, Machine.State.upd,
        String.reduceEq, Stm.war, hs, Fld.set, AF.set, hcs.1, hcs.2, Option.map_some,
        UnOp.eval, one_ne_zero, not_false_eq_true, hn, Res.ok.injEq, ↓existsAndEq,
        and_true, Nat.reduceLeDiff, exists_and_left] at h ⊢
      cases h
      exact ⟨by rfl, by
        pq_caps hq⟩

/-- Procedure inserting a chunk at the head of a size bucket. -/
def pqAddP : Proc where
  name := "pqAdd"
  params := ["c", "s", "p"]
  rets := []
  body :=
    "hd" ::= .ar .pqHead "s";;
    .ite (!ₑ ("hd" =ₑ 0))
      (.war .pqNext "c" "hd";; .war .pqPrev "hd" "c";; .war .pqPrev "c" 0;; .war .pqHead "s" "c")
      (.war .pqNext "c" 0;; .war .pqPrev "c" 0;; .war .pqHead "s" "c";;
        pqLinkAfterP.call ["s", "p"] []);;
    .war .pqWhere "c" "s"

@[simp] theorem pqLinkAfterP_params : pqLinkAfterP.params = ["s", "p"] := rfl
@[simp] theorem pqLinkAfterP_rets : pqLinkAfterP.rets = [] := rfl

theorem pqAdd_agree (κ : Caps) (σ : Core) (L : Loc) {c s p : Nat} (hc : L "c" = c) (hs : L "s" = s)
    (hp : L "p" = p) (hq : PQCaps κ σ) (hcC : c < Ccap κ) (hsB : s < Bcap κ) (hpB : p < Bcap κ)
    {σ' : Core} (h : (pqAdd c s p).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqAddP.body σ L = .ok σ' L' n ∧ n ≤ 140) ∧ PQCaps κ σ' := by
  have hcc : c < κ.arr .pqNext ∧ c < κ.arr .pqPrev ∧ c < κ.arr .pqWhere := by
    rw [hq.cC.1, hq.cC.2]; exact ⟨hcC, hcC, hcC⟩
  have hcs : s < κ.arr .pqHead := hsB
  have hhd : σ.pqHead.getX s < κ.arr .pqPrev := by rw [hq.cC.1]; exact hq.head s
  unfold pqAdd at h
  by_cases hd0 : σ.pqHead.getX s = 0
  · simp only [bne_iff_ne, ne_eq, ite_not, EStateM.run_bind, EStateM.run_get, hd0, ↓reduceIte,
      EStateM.run_modify] at h
    split at h
    · next u σ2 h2 =>
      cases h
      simp only [NIL] at h2
      have hq1 : PQCaps κ
          { σ with
            pqHead := σ.pqHead.setX s c, pqNext := σ.pqNext.setX c 0, pqPrev := σ.pqPrev.setX c
              0 } :=
        ((hq.sNext (i := c) (by omega)).sPrev (i := c) (by omega)).sHead (i := s) hcC
      obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqLinkAfter_agree κ _
        (Machine.State.setLocs (fun _ => 0) ["s", "p"] [s, p]) (by simp) (by simp) hq1 hsB hpB h2
      simp only [Machine.State.setLocs] at he2
      refine ⟨?_, by pq_caps hq2⟩
      simp only [pqAddP, Exp.ar, Exp.ofNat_def, Stm.war, Proc.call, pqLinkAfterP_params,
          pqLinkAfterP_rets, evalF, Res.bind, Exp.ev, hs, Fld.cap, Fld.get, AF.get,
          Option.bind_some, hcs, ↓reduceIte, hd0, Exp.cost, Nat.reduceAdd, Res.addCost,
          Machine.State.upd, BinOp.eval, Option.map_some, UnOp.eval, one_ne_zero, ne_eq,
          not_true_eq_false, String.reduceEq, hc, Fld.set, hcc.1, AF.set, hcc.2.1, evList,
          List.mapM_cons, hp, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
          Machine.State.setLocs, he2, costList, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, List.length_nil, hcc.2.2, Res.ok.injEq, true_and,
          ↓existsAndEq,  and_true, exists_and_right]
      omega
    · simp only [reduceCtorEq] at h
  · simp only [bne_iff_ne, ne_eq, ite_not, EStateM.run_bind, EStateM.run_get, hd0, ↓reduceIte,
      EStateM.run_modify, EStateM.Result.ok.injEq, true_and] at h
    cases h
    refine ⟨?_, by have := hq.head s; pq_caps hq⟩
    simp only [pqAddP, Exp.ar, Exp.ofNat_def, Stm.war, Proc.call, pqLinkAfterP_params,
        pqLinkAfterP_rets, evalF, Res.bind, Exp.ev, hs, Fld.cap, Fld.get, AF.get,
        Option.bind_some, hcs, ↓reduceIte, Exp.cost, Nat.reduceAdd, Res.addCost,
        Machine.State.upd, BinOp.eval, hd0, Option.map_some, UnOp.eval, ne_eq, one_ne_zero,
        not_false_eq_true, String.reduceEq, hc, Fld.set, hcc.1, AF.set, hhd, hcc.2.1,
        hcc.2.2, Res.ok.injEq, true_and, ↓existsAndEq, and_true, Nat.reduceLeDiff,
        exists_eq']

/-- Procedure removing a chunk and unlinking its bucket when it becomes empty. -/
def pqDelP : Proc where
  name := "pqDel"
  params := ["c"]
  rets := []
  body :=
    "s" ::= .ar .pqWhere "c";;
    .ite ("s" =ₑ 0) .fail .skip;;
    .war .pqWhere "c" 0;;
    "nx" ::= .ar .pqNext "c";;
    "pv" ::= .ar .pqPrev "c";;
    .ite (!ₑ ("pv" =ₑ 0)) (.war .pqNext "pv" "nx") (.war .pqHead "s" "nx");;
    .ite (!ₑ ("nx" =ₑ 0)) (.war .pqPrev "nx" "pv") .skip;;
    .ite (.ar .pqHead "s" =ₑ 0)
      ("p" ::= .ar .nbPrev "s";;
       "n" ::= .ar .nbNext "s";;
       .war .nbPrev "s" 0;;
       .war .nbNext "s" 0;;
       .ite (!ₑ ("p" =ₑ 0)) (.war .nbNext "p" "n") (.wsc .pqLo "n");;
       .ite (!ₑ ("n" =ₑ 0)) (.war .nbPrev "n" "p") (.wsc .pqHi "p"))
      .skip

@[simp] theorem pqAddP_params : pqAddP.params = ["c", "s", "p"] := rfl
@[simp] theorem pqAddP_rets : pqAddP.rets = [] := rfl
@[simp] theorem pqDelP_params : pqDelP.params = ["c"] := rfl
@[simp] theorem pqDelP_rets : pqDelP.rets = [] := rfl

theorem pqDel_agree (κ : Caps) (σ : Core) (L : Loc) {c : Nat} (hc : L "c" = c) (hq : PQCaps κ σ)
    (hcC : c < Ccap κ) {σ' : Core} (h : (pqDel c).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqDelP.body σ L = .ok σ' L' n ∧ n ≤ 200) ∧ PQCaps κ σ' := by
  have hcc : c < κ.arr .pqNext ∧ c < κ.arr .pqPrev ∧ c < κ.arr .pqWhere := by
    rw [hq.cC.1, hq.cC.2]; exact ⟨hcC, hcC, hcC⟩
  have hs := hq.where_ c
  have hnx := hq.next c
  have hpv := hq.prev c
  have hB1 := hq.cB.1
  have hB2 := hq.cB.2
  have hC1 := hq.cC.1
  unfold pqDel at h
  generalize hsd : σ.pqWhere.getX c = sv at hs
  generalize hnxd : σ.pqNext.getX c = nx at hnx
  generalize hpvd : σ.pqPrev.getX c = pv at hpv
  by_cases hs0 : sv = 0
  · simp only [beq_iff_eq, Model.guard, bne_iff_ne, ne_eq, ite_not, EStateM.run_bind,
      EStateM.run_get, hsd, hs0, ↓reduceIte, EStateM.run_throw, reduceCtorEq] at h
  have hsB : sv < κ.arr .pqHead := hs
  have hbn := hq.nbN sv
  have hbp := hq.nbP sv
  have hhs := hq.head sv
  simp only [beq_iff_eq, NIL, bne_iff_ne, ne_eq, ite_not, EStateM.run_bind, EStateM.run_get, hsd,
      hs0, ↓reduceIte, hpvd, hnxd, EStateM.run_modify, Proof.run_ite, Proof.Top.getX_setX',
      EStateM.run_pure] at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> cases h
  all_goals refine ⟨?_, by pq_caps hq⟩
  all_goals simp only [pqDelP, Exp.ar, Exp.ofNat_def, Stm.war, Stm.wsc, evalF, Res.bind, Exp.ev,
      Fld.cap, Fld.get, AF.get, Option.bind_some, ↓reduceIte, Exp.cost,
      Nat.reduceAdd, Res.addCost, Machine.State.upd, BinOp.eval, ne_eq,
      not_true_eq_false, String.reduceEq, Fld.set, AF.set, Option.map_some,
      UnOp.eval, one_ne_zero, Proof.Top.getX_setX', not_false_eq_true, zero_lt_one,
      SF.ok, and_self, SF.set, Res.ok.injEq, true_and, ↓existsAndEq, and_true,
      Nat.reduceLeDiff, exists_eq', *]

/-- Insert `c` at bucket `s`. The downward scan for the predecessor bucket (Level F's slow path)
runs only if bucket `s - 1` is above `θ` and empty; it is never needed (K2), and costs `O(s)`. -/
def pqInsertScanP : Proc where
  name := "pqInsertScan"
  params := ["c", "s"]
  rets := []
  body :=
    "th" ::= .prm .theta;;
    "p" ::= Exp.monus "s" 1;;
    .ite (("th" <ₑ "p") &&ₑ (.ar .pqHead "p" =ₑ 0))
      ("brk" ::= 0;;
       .loop "i" "s"
         (.ite (("brk" =ₑ 0) &&ₑ ("th" <ₑ "p") &&ₑ (.ar .pqHead "p" =ₑ 0))
           ("p" ::= Exp.monus "p" 1)
           ("brk" ::= 1)))
      .skip;;
    pqAddP.call ["c", "s", Exp.ifz ("th" <ₑ "p") "p"] []

/-- `pqInsertScan` when no scan is needed. -/
theorem pqInsertScan_agree (κ : Caps) (σ : Core) (L : Loc) {c s : Nat} (hc : L "c" = c) (hs : L
  "s" = s)
    (hq : PQCaps κ σ) (hcC : c < Ccap κ) (hsB : s < Bcap κ)
    (hfast : ¬(σ.P.theta < s - 1 ∧ σ.pqHead.getX (s - 1) = 0)) {σ' : Core}
    (h : (pqInsertScan c s).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqInsertScanP.body σ L = .ok σ' L' n ∧ n ≤ 250) ∧ PQCaps κ σ' := by
  have hpB : s - 1 < κ.arr .pqHead := by change s - 1 < Bcap κ; omega
  -- Level F: the loop stops at once
  have hrun : (pqInsertScan c s).run σ = (pqAdd c s (if σ.P.theta < s - 1 then s - 1 else
    0)).run σ := by
    unfold pqInsertScan
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · simp only [List.range_zero, zero_le, Nat.sub_eq_zero_of_le, gt_iff_lt, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq, List.forIn_nil, pure_bind, not_lt_zero, ↓reduceIte,
        EStateM.run_bind, EStateM.run_get]
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      simp only [OrderMaintenance.Proof.run_get_bind, List.range_succ_eq_map, List.forIn_cons]
      rw [OrderMaintenance.Proof.run_bind, OrderMaintenance.Proof.run_bind]
      have hc' : ¬((decide (k > σ.P.theta) && σ.pqHead.getX k == NIL) = true) := by
        simp only [Nat.add_sub_cancel] at hfast
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, NIL]
        exact hfast
      simp only [Nat.add_sub_cancel]
      rw [ite_eq_right hc']
      simp only [EStateM.run_pure, gt_iff_lt]
  rw [hrun] at h
  have hp' : (if σ.P.theta < s - 1 then s - 1 else 0) < Bcap κ := by split <;> omega
  obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqAdd_agree κ σ
    (Machine.State.setLocs (fun _ => 0) ["c", "s", "p"] [c, s, if σ.P.theta < s - 1 then s - 1
      else 0])
    (by simp) (by simp) (by simp) hq hcC hsB hp' h
  simp only [Machine.State.setLocs] at he2
  refine ⟨?_, hq2⟩
  have hm : (Exp.monus (.var "s") (.lit 1)).ev κ σ (Machine.State.upd L "th" σ.P.theta) = some
    (s - 1) :=
    Exp.ev_monus κ σ _ (by simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte,
      hs]) (by simp only [
        Exp.ev])
  have hfast' : ¬(σ.P.theta < s - 1 ∧ σ.pqHead.getX (s - 1) = 0) := hfast
  by_cases hlt : σ.P.theta < s - 1
  · have hh0 : σ.pqHead.getX (s - 1) ≠ 0 := fun e => hfast ⟨hlt, e⟩
    rw [ite_eq_left hlt] at he2
    simp only [pqInsertScanP, Exp.ofNat_def, Exp.ar, Proc.call, pqAddP_params, pqAddP_rets,
        Exp.ifz, Exp.mul_def, evalF, Res.bind, Exp.ev, PF.get, Exp.cost, Nat.reduceAdd,
        Res.addCost, hm, Exp.cost_monus, mul_one, Machine.State.upd, String.reduceEq,
        ↓reduceIte, BinOp.eval, Option.bind_some, hlt, Fld.cap, Fld.get, AF.get, hpB, hh0,
        ne_eq, not_true_eq_false, and_false, evList, List.mapM_cons, hc, hs, one_mul,
        List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Machine.State.setLocs, he2,
        costList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_nil, Res.ok.injEq, true_and, ↓existsAndEq,
        and_true, exists_and_right, ge_iff_le]
    omega
  · rw [ite_eq_right hlt] at he2
    simp only [pqInsertScanP, Exp.ofNat_def, Exp.ar, Proc.call, pqAddP_params, pqAddP_rets,
        Exp.ifz, Exp.mul_def, evalF, Res.bind, Exp.ev, PF.get, Exp.cost, Nat.reduceAdd,
        Res.addCost, hm, Exp.cost_monus, mul_one, Machine.State.upd, String.reduceEq,
        ↓reduceIte, BinOp.eval, Option.bind_some, hlt, Fld.cap, Fld.get, AF.get, hpB, ne_eq,
        ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, not_true_eq_false,
        false_and, evList, List.mapM_cons, hc, hs, zero_mul, List.mapM_nil, Option.pure_def,
        Option.bind_eq_bind, Machine.State.setLocs, he2, costList, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_nil, Res.ok.injEq,
        true_and, ↓existsAndEq,  and_true, exists_and_right,
        ge_iff_le]
    omega

@[simp] theorem pqInsertScanP_params : pqInsertScanP.params = ["c", "s"] := rfl
@[simp] theorem pqInsertScanP_rets : pqInsertScanP.rets = [] := rfl

/-- Procedure transferring a queued chunk after its size changes. -/
def pqAdjustP : Proc where
  name := "pqAdjust"
  params := ["c", "old", "new"]
  rets := []
  body :=
    "th" ::= .prm .theta;;
    .ite (("old" ≤ₑ "th") &&ₑ ("th" <ₑ "new")) (pqInsertScanP.call ["c", "new"] [])
      (.ite (("new" ≤ₑ "th") &&ₑ ("th" <ₑ "old")) (pqDelP.call ["c"] [])
        (.ite (("th" <ₑ "old") &&ₑ ("th" <ₑ "new"))
          (.ite ("new" =ₑ Exp.var "old" + 1)
            ("alone" ::= ((.ar .pqHead "old" =ₑ "c") &&ₑ (.ar .pqNext "c" =ₑ 0));;
             "p" ::= (Exp.ifz "alone" (.ar .nbPrev "old") + Exp.ifz (!ₑ "alone") "old");;
             pqDelP.call ["c"] [];;
             pqAddP.call ["c", "new", "p"] [])
            (.ite (Exp.var "new" + 1 =ₑ "old")
              ("p" ::= .ar .nbPrev "old";;
               pqDelP.call ["c"] [];;
               pqAddP.call ["c", "new", "p"] [])
              (pqDelP.call ["c"] [];; pqInsertScanP.call ["c", "new"] [])))
          .skip))

/-- `pqAdjust` for a `+1` change of size (the only one the algorithm makes). -/
theorem pqAdjust_agree (κ : Caps) (σ : Core) (L : Loc) {c old : Nat} (hc : L "c" = c)
    (ho : L "old" = old) (hn : L "new" = old + 1) (hq : PQCaps κ σ) (hcC : c < Ccap κ)
    (hnB : old + 1 < Bcap κ) {σ' : Core} (h : (pqAdjust c old (old + 1)).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqAdjustP.body σ L = .ok σ' L' n ∧ n ≤ 700) ∧ PQCaps κ σ' := by
  have hoB : old < κ.arr .pqHead := by change old < Bcap κ; omega
  have hcN : c < κ.arr .pqNext := hcC
  have hbP : old < κ.arr .nbPrev := by rw [hq.cB.2]; show old < Bcap κ; omega
  unfold pqAdjust at h
  simp only [OrderMaintenance.Proof.run_getP_bind] at h
  rcases lt_trichotomy old σ.P.theta with hlt | heq | hgt
  · -- below the queue: nothing
    rw [ite_eq_right (by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
      omega), ite_eq_right (by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
        omega), ite_eq_right (by
          simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
          omega)] at h
    cases h
    refine ⟨?_, hq⟩
    have h1 : old + 1 ≤ σ.P.theta := hlt
    simp only [pqAdjustP, Exp.ofNat_def, Exp.add_def, evalF, Res.bind, Exp.ev, PF.get, Exp.cost,
        Nat.reduceAdd, Res.addCost, Machine.State.upd, String.reduceEq, ↓reduceIte, ho,
        BinOp.eval, Option.bind_some, Nat.le_of_lt hlt, hn, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_lt, h1, not_true_eq_false, and_false,
        Nat.not_lt.mpr (Nat.le_of_lt hlt), Res.ok.injEq, true_and, ↓existsAndEq, and_true,
        Nat.reduceLeDiff, exists_eq']
  · -- entering at bucket `θ + 1`
    rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at h
    obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqInsertScan_agree κ σ
      (Machine.State.setLocs (fun _ => 0) ["c", "s"] [c, old + 1]) (by simp) (by simp) hq hcC hnB
      (by simp only [add_tsub_cancel_right, not_and]; omega) h
    simp only [Machine.State.setLocs] at he2
    rw [heq] at he2
    refine ⟨?_, hq2⟩
    simp only [pqAdjustP, Proc.call, pqInsertScanP_params, pqInsertScanP_rets, pqDelP_params,
        pqDelP_rets, Exp.ofNat_def, Exp.add_def, pqAddP_params, pqAddP_rets, evalF, Res.bind,
        Exp.ev, PF.get, Exp.cost, Nat.reduceAdd, Res.addCost, Machine.State.upd,
        String.reduceEq, ↓reduceIte, ho, heq, BinOp.eval, Option.bind_some, Std.le_refl, hn,
        lt_add_iff_pos_right, zero_lt_one, ne_eq, one_ne_zero, not_false_eq_true, and_true,
        ite_not, evList, List.mapM_cons, hc, List.mapM_nil, Option.pure_def,
        Option.bind_eq_bind, Machine.State.setLocs, he2, costList, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_nil, Res.ok.injEq,
        true_and, ↓existsAndEq,  exists_and_right]
    omega
  · -- moving up one bucket
    rw [ite_eq_right (by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
      omega), ite_eq_right (by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
        omega), ite_eq_left (by
          simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]
          omega)] at h
    simp only [OrderMaintenance.Proof.run_get_bind, beq_self_eq_true, ite_true] at h
    obtain ⟨u, σ1, h1, h2⟩ := run_bind_ok h
    obtain ⟨⟨L1, n1, he1, hn1⟩, hq1⟩ := pqDel_agree κ σ
      (Machine.State.setLocs (fun _ => 0) ["c"] [c]) (by simp) hq hcC h1
    simp only [Machine.State.setLocs] at he1
    have hlt1 : ¬(old + 1 ≤ σ.P.theta) := by omega
    have hlt2 : ¬(old ≤ σ.P.theta) := by omega
    have hlt3 : ¬(old < σ.P.theta) := by omega
    by_cases ha : σ.pqHead.getX old = c ∧ σ.pqNext.getX c = 0
    · rw [ite_eq_left (by simp only [ha.1, BEq.rfl, ha.2, NIL, Bool.and_self])] at h2
      obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqAdd_agree κ σ1
        (Machine.State.setLocs (fun _ => 0) ["c", "s", "p"] [c, old + 1, σ.nbPrev.getX old])
        (by simp) (by simp) (by simp) hq1 hcC hnB (hq.nbP old) h2
      simp only [Machine.State.setLocs] at he2
      refine ⟨?_, hq2⟩
      simp only [pqAdjustP, Proc.call, pqInsertScanP_params, pqInsertScanP_rets, pqDelP_params,
          pqDelP_rets, Exp.ofNat_def, Exp.add_def, Exp.ar, Exp.ifz, Exp.mul_def,
          pqAddP_params, pqAddP_rets, evalF, Res.bind, Exp.ev, PF.get, Exp.cost,
          Nat.reduceAdd, Res.addCost, Machine.State.upd, String.reduceEq, ↓reduceIte, ho,
          BinOp.eval, Option.bind_some, hlt2, hn, ne_eq, ite_eq_right_iff, one_ne_zero,
          imp_false, not_lt, hlt1, not_false_eq_true, and_true, ite_not, not_true_eq_false,
          hgt,  Fld.cap, Fld.get, AF.get, hoB, ha.1, hc, hcN, ha.2,
          hbP, one_mul, Option.map_some, UnOp.eval, zero_mul, add_zero,
          Option.bind_fun_some, evList, List.mapM_cons, List.mapM_nil, Option.pure_def,
          Option.bind_eq_bind, Machine.State.setLocs, he1, costList, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, List.length_nil, he2, Res.ok.injEq,
          true_and, ↓existsAndEq, exists_and_right]
      omega
    · rw [ite_eq_right (by simpa [NIL] using ha)] at h2
      obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqAdd_agree κ σ1
        (Machine.State.setLocs (fun _ => 0) ["c", "s", "p"] [c, old + 1, old])
        (by simp) (by simp) (by simp) hq1 hcC hnB (by omega) h2
      simp only [Machine.State.setLocs] at he2
      refine ⟨?_, hq2⟩
      have ha' : σ.pqHead.getX old = c → σ.pqNext.getX c ≠ 0 := fun e1 e2 => ha ⟨e1, e2⟩
      by_cases hh : σ.pqHead.getX old = c
      · simp only [pqAdjustP, Proc.call, pqInsertScanP_params, pqInsertScanP_rets, pqDelP_params,
          pqDelP_rets, Exp.ofNat_def, Exp.add_def, Exp.ar, Exp.ifz, Exp.mul_def,
          pqAddP_params, pqAddP_rets, evalF, Res.bind, Exp.ev, PF.get, Exp.cost,
          Nat.reduceAdd, Res.addCost, Machine.State.upd, String.reduceEq, ↓reduceIte, ho,
          BinOp.eval, Option.bind_some, hlt2, hn, ne_eq, ite_eq_right_iff, one_ne_zero,
          imp_false, not_lt, hlt1, not_false_eq_true, and_true, ite_not,
          not_true_eq_false, hgt,  Fld.cap, Fld.get, AF.get, hoB,
          hh, hc, hcN, ha' hh, and_false, hbP, zero_mul, Option.map_some, UnOp.eval,
          one_mul, zero_add, evList, List.mapM_cons, List.mapM_nil, Option.pure_def,
          Option.bind_eq_bind, Machine.State.setLocs, he1, costList, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_nil, he2,
          Res.ok.injEq, true_and, ↓existsAndEq, exists_and_right, ge_iff_le]
        omega
      · simp only [pqAdjustP, Proc.call, pqInsertScanP_params, pqInsertScanP_rets, pqDelP_params,
          pqDelP_rets, Exp.ofNat_def, Exp.add_def, Exp.ar, Exp.ifz, Exp.mul_def,
          pqAddP_params, pqAddP_rets, evalF, Res.bind, Exp.ev, PF.get, Exp.cost,
          Nat.reduceAdd, Res.addCost, Machine.State.upd, String.reduceEq, ↓reduceIte, ho,
          BinOp.eval, Option.bind_some, hlt2, hn, ne_eq, ite_eq_right_iff, one_ne_zero,
          imp_false, not_lt, hlt1, not_false_eq_true, and_true, ite_not,
          not_true_eq_false, hgt,  Fld.cap, Fld.get, AF.get, hoB,
          hc, hh, hcN, Decidable.not_not, false_and, hbP, zero_mul, Option.map_some,
          UnOp.eval, one_mul, zero_add, evList, List.mapM_cons, List.mapM_nil,
          Option.pure_def, Option.bind_eq_bind, Machine.State.setLocs, he1, costList,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          List.length_nil, he2, Res.ok.injEq, true_and, ↓existsAndEq, exists_and_right,
          ge_iff_le]
        omega

/-- Procedure queuing a chunk when its size exceeds the quiet threshold. -/
def pqEnterIfAboveP : Proc where
  name := "pqEnterIfAbove"
  params := ["c"]
  rets := []
  body :=
    "s" ::= .rd (.c .size) "c";;
    .ite (.prm .theta <ₑ "s") (pqInsertScanP.call ["c", "s"] []) .skip

private theorem pqEnterIfAbove_run_of_le (σ : Core) (c : Nat) (hle : (σ.C.getX c).size ≤
  σ.P.theta) :
    (pqEnterIfAbove c).run σ = .ok () σ := by
  unfold pqEnterIfAbove
  simp only [Proof.run_getC_bind, Proof.run_getP_bind]
  split
  · rename_i h
    exact False.elim ((Nat.not_lt.mpr hle) h)
  · rfl

/-- `pqEnterIfAbove` for a chunk not above `θ` (every freshly quiet chunk: `c_max ≤ θ`). -/
theorem pqEnterIfAbove_agree (κ : Caps) (σ : Core) (L : Loc) {c : Nat} (hc : L "c" = c)
    (hcT : c < κ.tbl .C) (hle : (σ.C.getX c).size ≤ σ.P.theta) {σ' : Core}
    (h : (pqEnterIfAbove c).run σ = .ok () σ') :
    ∃ L' n, evalF κ pqEnterIfAboveP.body σ L = .ok σ' L' n ∧ n ≤ 20 := by
  rw [pqEnterIfAbove_run_of_le σ c hle] at h
  cases h
  have : ¬ σ.P.theta < (σ.C.getX c).size := by omega
  simp only [pqEnterIfAboveP, evalF, Res.bind, Exp.ev, hc, Fld.cap, Fld.get, CF.get,
      Option.bind_some, hcT, ↓reduceIte, Exp.cost, Nat.reduceAdd, Res.addCost, PF.get,
      Machine.State.upd, BinOp.eval, this, ne_eq, not_true_eq_false, Res.ok.injEq, true_and,
      ↓existsAndEq, and_true, Nat.reduceLeDiff, exists_eq']

/-- Procedure removing and returning a chunk from the largest nonempty bucket. -/
def pqPopMaxP : Proc where
  name := "pqPopMax"
  params := []
  rets := ["c"]
  body :=
    "c" ::= .ar .pqHead (.sc .pqHi);;
    .ite ("c" =ₑ 0) .fail .skip;;
    pqDelP.call ["c"] []

private theorem pqPopMax_run_of_ne_zero (σ : Core) (c : Nat) (σ' : Core) (h0 : σ.pqHead.getX
  σ.pqHi ≠ 0)
    (h : pqPopMax.run σ = .ok c σ') :
    (pqDel (σ.pqHead.getX σ.pqHi)).run σ = .ok () σ' ∧ c = σ.pqHead.getX σ.pqHi := by
  unfold pqPopMax at h
  simp only [Proof.run_get_bind] at h
  simp only [NIL, beq_iff_eq, h0, ↓reduceIte, bind_pure_comp] at h
  change EStateM.map (fun _ => σ.pqHead.getX σ.pqHi) _ σ = _ at h
  cases hd : (pqDel (σ.pqHead.getX σ.pqHi)).run σ with
  | error e st => simp only [EStateM.run] at hd; simp only [EStateM.map, hd, reduceCtorEq] at h
  | ok u st =>
    cases u
    simp only [EStateM.run] at hd
    simp only [EStateM.map, hd, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem pqPopMax_agree (κ : Caps) (σ : Core) (L : Loc) (hq : PQCaps κ σ) {c : Nat} {σ' : Core}
    (h : pqPopMax.run σ = .ok c σ') :
    (∃ L' n, evalF κ pqPopMaxP.body σ L = .ok σ' L' n ∧ L' "c" = c ∧ n ≤ 240) ∧ PQCaps κ σ' := by
  have hhi : σ.pqHi < κ.arr .pqHead := hq.hi
  have hcC := hq.head σ.pqHi
  by_cases h0 : σ.pqHead.getX σ.pqHi = 0
  · simp [pqPopMax, h0, NIL, OrderMaintenance.Model.guard] at h
  · obtain ⟨h1, rfl⟩ := pqPopMax_run_of_ne_zero σ c σ' h0 h
    obtain ⟨⟨L1, n1, he1, hn1⟩, hq1⟩ := pqDel_agree κ σ
      (Machine.State.setLocs (fun _ => 0) ["c"] [σ.pqHead.getX σ.pqHi]) (by simp) hq hcC h1
    simp only [Machine.State.setLocs] at he1
    refine ⟨?_, hq1⟩
    simp only [pqPopMaxP, Exp.ar, Exp.sc, Exp.ofNat_def, Proc.call, pqDelP_params, pqDelP_rets,
        evalF, Res.bind, Exp.ev, Fld.cap, Nat.lt_one_iff, Fld.get, SF.get,
        Option.bind_some, ↓reduceIte, AF.get, hhi, Exp.cost, Nat.reduceAdd, Res.addCost,
        Machine.State.upd, BinOp.eval, h0, ne_eq, not_true_eq_false, evList,
        List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
        Machine.State.setLocs, he1, costList, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, List.length_nil, Res.ok.injEq, true_and, ↓existsAndEq,
         and_true, exists_eq_left']
    omega

/-- Procedure reporting whether every priority-queue bucket is empty. -/
def pqEmptyP : Proc where
  name := "pqEmpty"
  params := []
  rets := ["r"]
  body := "r" ::= (.sc .pqHi =ₑ 0)

theorem pqEmpty_agree (κ : Caps) (σ : Core) (L : Loc) {b : Bool} {σ' : Core}
    (h : pqEmpty.run σ = .ok b σ') :
    ∃ L' n, evalF κ pqEmptyP.body σ L = .ok σ' L' n ∧ L' "r" = b2n b ∧ n ≤ 10 := by
  unfold pqEmpty at h
  simp only [bind_pure_comp] at h; obtain ⟨rfl, rfl⟩ := h
  by_cases h0 : σ.pqHi = 0 <;>
    simp only [pqEmptyP, Exp.sc, Exp.ofNat_def, evalF, Exp.ev, Fld.cap, Nat.lt_one_iff, Fld.get,
        SF.get, h0, Option.bind_some, ↓reduceIte, BinOp.eval, Exp.cost, Nat.reduceAdd,
        Res.ok.injEq, true_and, b2n, BEq.rfl, ↓existsAndEq, and_true, Nat.reduceLeDiff,
        exists_eq_left', Machine.State.upd, beq_iff_eq]

end OrderMaintenance.Impl
