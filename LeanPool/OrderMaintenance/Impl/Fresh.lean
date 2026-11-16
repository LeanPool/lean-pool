/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Caps
public import LeanPool.OrderMaintenance.Impl.WCall
public import LeanPool.OrderMaintenance.Machine.Alloc


/-!
# M6: a fresh core in fresh memory

The wrapper builds a new core in the free slot `q`: it allocates the parameter array and writes
the parameters, computes the capacities into locals, and allocates every other array of the slot
(`allocSlot`). The arrays then read 0, so they hold the empty core `freshC P` (`fresh_enc`).
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr allocAll allocCost exec_allocAll)

/-! ### The arrays of a slot -/

def EF.all : List EF := [.next, .prev, .grp, .lab, .dead, .h]
def GF.all : List GF := [.next, .prev, .first, .last, .chk, .lab, .size, .st, .src, .l, .r, .dead]
def CF.all : List CF := [.next, .prev, .first, .last, .size, .st, .src, .l, .r, .tag, .dead]
def NF.all : List NF := [.height, .livePar, .weight, .first, .last, .draining, .t1, .t2, .overflow, .dead]
def AF.all : List AF := [.pqHead, .pqNext, .pqPrev, .pqWhere, .nbNext, .nbPrev, .lpar]
def SF.all : List SF := [.count, .head, .tail, .firstGroup, .firstChunk, .notReady, .fallbacks, .pqHi, .pqLo]
def Tbl.all : List Tbl := [.E, .G, .C, .N]
def LK.all : List LK := [.children, .table, .inTab, .side, .cin, .freeG]
def OF.all : List OF := [.prepOn, .prepChunk, .prepH, .prepBelow, .prepTag, .jobOn, .jobX, .jobY, .jobZ, .jobT,
  .jobA, .jobB, .jobC, .jobD]

def Fld.all : List Fld :=
  EF.all.map .e ++ GF.all.map .g ++ CF.all.map .c ++ NF.all.map .n ++ AF.all.map .a ++ SF.all.map .s

/-- Every array of a slot but the parameters. -/
def Slot.allNP : List Slot :=
  Fld.all.map .f ++ Tbl.all.map .sz ++ LK.all.flatMap (fun k => [.lst k false, .lst k true, .len k]) ++
    [.path] ++ OF.all.map .opt

theorem Fld.mem_all (f : Fld) : f ∈ Fld.all := by
  cases f with
  | e k => cases k <;> simp [Fld.all, EF.all]
  | g k => cases k <;> simp [Fld.all, GF.all]
  | c k => cases k <;> simp [Fld.all, CF.all]
  | n k => cases k <;> simp [Fld.all, NF.all]
  | a k => cases k <;> simp [Fld.all, AF.all]
  | s k => cases k <;> simp [Fld.all, SF.all]

theorem Slot.mem_allNP (sl : Slot) (h : sl ≠ .prm) : sl ∈ Slot.allNP := by
  cases sl with
  | f f => simp [Slot.allNP, Fld.mem_all f]
  | sz t => cases t <;> simp [Slot.allNP, Tbl.all]
  | prm => exact absurd rfl h
  | lst k b => cases k <;> cases b <;> simp [Slot.allNP, LK.all]
  | len k => cases k <;> simp [Slot.allNP, LK.all]
  | path => simp [Slot.allNP]
  | opt o => cases o <;> simp [Slot.allNP, OF.all]

theorem Slot.allNP_codes : (Slot.allNP.map Slot.code).Nodup := by decide

theorem Slot.allNP_nodup (q : Nat) : (Slot.allNP.map (arr q)).Nodup := by
  have h := Slot.allNP_codes
  have : Slot.allNP.map (arr q) = (Slot.allNP.map Slot.code).map (fun c => 1000 * q + c) := by
    simp [List.map_map, arr]
  rw [this]
  exact h.map (fun a b e => Nat.add_left_cancel e)

theorem Slot.prm_notMem : Slot.prm ∉ Slot.allNP := by
  intro h
  have := List.mem_map_of_mem (f := Slot.code) h
  revert this; decide

/-! ### Capacities -/

/-- The capacity `Enc` asks of each array. -/
def capOf (κ : Caps) : Slot → Nat
  | .f f => f.cap κ
  | .sz _ => 1
  | .prm => 16
  | .lst k _ => κ.lrec k * κ.lcap k
  | .len k => κ.lrec k
  | .path => κ.tbl .C * κ.pw
  | .opt _ => 1

/-- The record capacity of list kind `k`, from the locals. -/
def lrecE : LK → Expr
  | .children => .var "kR" | .table => .var "kR" | .inTab => .var "kR" | .side => .var "kR"
  | .cin => .var "kRc" | .freeG => .lit 1
/-- The list capacity of kind `k`, from the locals. -/
def lcapE : LK → Expr
  | .children => .lit 162 | .table => .lit 162 | .inTab => .lit 322 | .side => .lit 322 | .cin => .lit 322
  | .freeG => .var "kf"

/-- The capacity of each array, from the locals `kE … kW`. -/
def capE : Slot → Expr
  | .f (.e _) => .var "kE"
  | .f (.g _) => .var "kG"
  | .f (.c _) => .var "kC"
  | .f (.n _) => .var "kN"
  | .f (.a .pqHead) => .var "kB"
  | .f (.a .nbNext) => .var "kB"
  | .f (.a .nbPrev) => .var "kB"
  | .f (.a .pqNext) => .var "kCc"
  | .f (.a .pqPrev) => .var "kCc"
  | .f (.a .pqWhere) => .var "kCc"
  | .f (.a .lpar) => .var "kL"
  | .f (.s _) => .lit 1
  | .sz _ => .lit 1
  | .prm => .lit 16
  | .lst k _ => .bin .mul (lrecE k) (lcapE k)
  | .len k => lrecE k
  | .path => .bin .mul (.var "kC") (.var "kW")
  | .opt _ => .lit 1

theorem capE_noLoad (sl : Slot) : (capE sl).noLoad := by
  cases sl with
  | f f => cases f with
    | a k => cases k <;> rfl
    | _ k => rfl
  | lst k b => cases k <;> rfl
  | len k => cases k <;> rfl
  | _ => rfl

/-- The capacity locals hold the capacities of parameters `P`. -/
structure CapLocs (P : Params) (l : Reg → Nat) : Prop where
  kE : l "kE" = P.N + 2
  kG : l "kG" = 2 * P.N + 4
  kC : l "kC" = cb P + 2
  kN : l "kN" = nbMax P + cb P + 2
  kB : l "kB" = P.N + 3
  kCc : l "kCc" = cb P + 2
  kL : l "kL" = nbMax P + cb P + 2
  kR : l "kR" = nbMax P + 2
  kRc : l "kRc" = nbMax P + cb P + 2
  kf : l "kf" = 2 * P.N + 4
  kW : l "kW" = P.H + 1

theorem capE_eval {P : Params} {m : State} (h : CapLocs P m.loc) (sl : Slot) :
    (capE sl).eval m = some (capOf (capsOf P) sl) := by
  cases sl with
  | f f => cases f with
    | e k => simp [capE, capOf, Fld.cap, capsOf, Expr.eval, h.kE]
    | g k => simp [capE, capOf, Fld.cap, capsOf, Expr.eval, h.kG]
    | c k => simp [capE, capOf, Fld.cap, capsOf, Expr.eval, h.kC]
    | n k => simp [capE, capOf, Fld.cap, capsOf, Expr.eval, h.kN]
    | a k => cases k <;> simp [capE, capOf, Fld.cap, capsOf, Expr.eval, h.kB, h.kCc, h.kL]
    | s k => simp [capE, capOf, Fld.cap, capsOf, Expr.eval]
  | sz t => rfl
  | prm => rfl
  | lst k b => cases k <;> simp [capE, capOf, capsOf, lrecE, lcapE, Expr.eval, OrderMaintenance.Machine.BinOp.eval, h.kR,
      h.kRc, h.kf]
  | len k => cases k <;> simp [capE, capOf, capsOf, lrecE, Expr.eval, h.kR, h.kRc]
  | path => simp [capE, capOf, capsOf, Expr.eval, OrderMaintenance.Machine.BinOp.eval, h.kC, h.kW]
  | opt o => rfl

/-- Allocate every array of slot `q` but the parameters. -/
def allocSlot (q : Nat) : Stmt := allocAll (Slot.allNP.map fun sl => (arr q sl, capE sl))

/-! ### The empty core -/

theorem fresh_get (P : Params) (f : Fld) (i : Nat) : f.get (freshC P) i = 0 := by
  cases f with
  | e k => cases k <;> rfl
  | g k => cases k <;> rfl
  | c k => cases k <;> rfl
  | n k => cases k <;> rfl
  | a k => cases k <;> rfl
  | s k => cases k <;> rfl

theorem fresh_view (P : Params) (k : LK) (i : Nat) : (k.view (freshC P) i) = [] := by
  cases k <;> simp [LK.view, freshC] <;> rfl

theorem fresh_opt (P : Params) (o : OF) : o.get (freshC P) = 0 := by
  cases o <;> rfl

/-- **Fresh memory holds the empty core.** Slot `q`'s parameter array holds `P`, the capacity
locals hold `P`'s capacities, and every other array of the slot is allocated by `allocSlot`. -/
theorem fresh_enc {P : Params} {q : Nat} {m : State} (hpc : m.cap (arr q .prm) = 16)
    (hpm : ∀ k : PF, m.mem (arr q .prm) k.idx = k.get P) (hl : CapLocs P m.loc) :
    (exec (allocSlot q) m).status = .ok ∧ (exec (allocSlot q) m).cost = allocCost (Slot.allNP.map fun sl => (arr q sl, capE sl)) ∧
      (exec (allocSlot q) m).st.loc = m.loc ∧
      Enc q (capsOf P) (freshC P) (exec (allocSlot q) m).st ∧
      (∀ b, ¬ InSlot q b → Same b m (exec (allocSlot q) m).st) := by
  set l := Slot.allNP.map fun sl => (arr q sl, capE sl)
  rw [show allocSlot q = allocAll l from rfl]
  have hev : ∀ ae ∈ l, ae.2.noLoad ∧ (ae.2.eval m).isSome := by
    intro ae hae
    simp only [l, List.mem_map] at hae
    obtain ⟨sl, -, rfl⟩ := hae
    exact ⟨capE_noLoad sl, by rw [capE_eval hl]; rfl⟩
  have hnd : (l.map Prod.fst).Nodup := by
    simp only [l, List.map_map]; exact Slot.allNP_nodup q
  obtain ⟨r1, r2, r3, r4, r5⟩ := exec_allocAll l m hev hnd
  set m' := (exec (allocAll l) m).st
  have hS : ∀ sl, sl ≠ .prm → m'.cap (arr q sl) = capOf (capsOf P) sl ∧ ∀ i, m'.mem (arr q sl) i = 0 := by
    intro sl hsl
    obtain ⟨c1, c2⟩ := r4 (arr q sl, capE sl) (List.mem_map_of_mem (Slot.mem_allNP sl hsl))
    exact ⟨by rw [c1, capE_eval hl]; rfl, c2⟩
  have hP : Same (arr q .prm) m m' := r5 _ (by
    simp only [l, List.map_map, List.mem_map]
    rintro ⟨sl, hsl, he⟩
    have := arr_inj he; subst this; exact Slot.prm_notMem hsl)
  refine ⟨r1, r2, r3, ?_, fun b hb => r5 b ?_⟩
  · refine ⟨fun f => (hS (.f f) (by simp)).1, fun f i _ => by rw [(hS (.f f) (by simp)).2, fresh_get],
      fun t => (hS (.sz t) (by simp)).1, fun t => by rw [(hS (.sz t) (by simp)).2]; cases t <;> rfl,
      fun t => by cases t <;> simp [Tbl.size, freshC], by rw [hP.2]; exact hpc,
      fun k => by rw [hP.1]; exact hpm k, fun k b => (hS (.lst k b) (by simp)).1, fun k => (hS (.len k) (by simp)).1,
      fun k i _ => by rw [(hS (.len k) (by simp)).2, fresh_view]; simp,
      fun k i _ j hj => by rw [fresh_view] at hj; simp at hj,
      (hS .path (by simp)).1, fun c _ j _ => by rw [(hS .path (by simp)).2]; rfl,
      fun o => (hS (.opt o) (by simp)).1, fun o => by rw [(hS (.opt o) (by simp)).2, fresh_opt],
      fun pr h => by simp [freshC] at h, rfl, rfl⟩
  · simp only [l, List.map_map, List.mem_map]
    rintro ⟨sl, -, he⟩
    exact hb (he ▸ arr_inSlot q sl)

end OrderMaintenance.Impl
