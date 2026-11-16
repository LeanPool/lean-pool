/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Algebra.Order.Ring.Nat

public import LeanPool.OrderMaintenance.ArrayLemmas
public import LeanPool.OrderMaintenance.Proof.Correct.Monad
public import LeanPool.OrderMaintenance.Impl.Compile


/-!
# M6: notation for the core language, and procedures
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)

instance {n : Nat} : OfNat Exp n := ⟨.lit n⟩
instance : Coe Reg Exp := ⟨.var⟩
instance : Add Exp := ⟨.bin .add⟩
instance : Sub Exp := ⟨.bin .sub⟩
instance : Mul Exp := ⟨.bin .mul⟩
instance : Div Exp := ⟨.bin .div⟩
instance : Mod Exp := ⟨.bin .mod⟩

@[simp] theorem Exp.ofNat_def (n : Nat) : (OfNat.ofNat n : Exp) = .lit n := rfl
@[simp] theorem Exp.add_def (a b : Exp) : a + b = .bin .add a b := rfl
@[simp] theorem Exp.sub_def (a b : Exp) : a - b = .bin .sub a b := rfl
@[simp] theorem Exp.mul_def (a b : Exp) : a * b = .bin .mul a b := rfl
@[simp] theorem Exp.div_def (a b : Exp) : a / b = .bin .div a b := rfl
@[simp] theorem Exp.mod_def (a b : Exp) : a % b = .bin .mod a b := rfl

/-- Strict comparison of two machine expressions. -/
infix:50 " <ₑ " => Exp.bin BinOp.lt
/-- Non-strict comparison of two machine expressions. -/
infix:50 " ≤ₑ " => Exp.bin BinOp.le
/-- Equality comparison of two machine expressions. -/
infix:50 " =ₑ " => Exp.bin BinOp.eq
/-- Boolean conjunction of two machine expressions. -/
infixr:35 " &&ₑ " => Exp.bin BinOp.and
/-- Boolean disjunction of two machine expressions. -/
infixr:30 " ||ₑ " => Exp.bin BinOp.or
/-- Boolean negation of a machine expression. -/
prefix:max "!ₑ" => Exp.un UnOp.not

/-- Sequential composition of two machine statements. -/
infixr:20 ";; " => Stm.seq
/-- Assignment of a machine expression to a local register. -/
infix:40 " ::= " => Stm.assign

/-- `max a b`, without branches. -/
def Exp.max (a b : Exp) : Exp := (a <ₑ b) * b + (1 - (a <ₑ b)) * a
/-- Truncated subtraction (Level F's `-` on `Nat`). -/
def Exp.monus (a b : Exp) : Exp := Exp.max a b - b
/-- `if c then a else 0`, for a condition `c` worth 0 or 1. -/
def Exp.ifz (c a : Exp) : Exp := c * a

/-- Scalar `k` of the core. -/
def Exp.sc (k : SF) : Exp := .rd (.s k) 0
/-- Assign a typed expression to a core scalar field. -/
def Stm.wsc (k : SF) (e : Exp) : Stm := .wr (.s k) 0 e
/-- Read one entry of a selected plain numeric array. -/
def Exp.ar (k : AF) (i : Exp) : Exp := .rd (.a k) i
/-- Write one entry of a selected plain numeric array. -/
def Stm.war (k : AF) (i e : Exp) : Stm := .wr (.a k) i e
/-- Field `k` of element, group or chunk `i`, and writes to it. -/
def Exp.eF (k : EF) (i : Exp) : Exp := .rd (.e k) i
/-- Read a selected numeric field of a group record. -/
def Exp.gF (k : GF) (i : Exp) : Exp := .rd (.g k) i
/-- Read a selected numeric field of a chunk record. -/
def Exp.cF (k : CF) (i : Exp) : Exp := .rd (.c k) i
/-- Write a selected numeric field of an element record. -/
def Stm.weF (k : EF) (i e : Exp) : Stm := .wr (.e k) i e
/-- Write a selected numeric field of a group record. -/
def Stm.wgF (k : GF) (i e : Exp) : Stm := .wr (.g k) i e
/-- Write a selected numeric field of a chunk record. -/
def Stm.wcF (k : CF) (i e : Exp) : Stm := .wr (.c k) i e

theorem Exp.ev_max (κ : Caps) (s : Core) (L : Loc) {a b : Exp} {x y : Nat}
    (ha : a.ev κ s L = some x)
    (hb : b.ev κ s L = some y) : (Exp.max a b).ev κ s L = some (Nat.max x y) := by
  simp only [Exp.max, Exp.ev, ha, hb, Option.bind_some, BinOp.eval,
    Exp.add_def,
    Exp.mul_def, Exp.sub_def, Exp.ofNat_def]
  by_cases h : x < y
  · simp [h, Nat.max_eq_right (Nat.le_of_lt h)]
  · simp [h, Nat.max_eq_left (Nat.le_of_not_gt h)]

theorem Exp.ev_monus (κ : Caps) (s : Core) (L : Loc) {a b : Exp} {x y : Nat}
    (ha : a.ev κ s L = some x)
    (hb : b.ev κ s L = some y) : (Exp.monus a b).ev κ s L = some (x - y) := by
  simp only [Exp.monus, Exp.sub_def, Exp.ev, Exp.ev_max κ s L ha hb, hb, Option.bind_some,
    BinOp.eval]
  have h1 : y ≤ Nat.max x y := Nat.le_max_right x y
  have h2 : Nat.max x y = if x ≤ y then y else x := rfl
  rw [ite_eq_left h1]; congr 1; split at h2 <;> omega

@[simp] theorem Exp.cost_monus (a b : Exp) :
    (Exp.monus a b).cost = 8 + 3 * a.cost + 4 * b.cost := by
  simp [Exp.monus, Exp.max, Exp.cost]; omega

/-- A procedure of the core language. -/
structure Proc where
  /-- Diagnostic name carried by a procedure call. -/
  name : String
  /-- Local registers receiving the argument values. -/
  params : List Reg
  /-- Local registers whose final values are returned. -/
  rets : List Reg
  /-- Statement executed in the procedure’s local frame. -/
  body : Stm

/-- Invoke a typed procedure with argument expressions and destination locals. -/
def Proc.call (q : Proc) (args : List Exp) (dsts : List Reg) : Stm :=
  .call q.name q.params q.body q.rets args dsts

end OrderMaintenance.Impl

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg State)

/-! ### Stepping through `evalF` -/

theorem evalF_seq_ok {κ : Caps} {A B : Stm} {s s1 : Core} {L L1 : Loc} {c1 : Nat}
    (h : evalF κ A s L = .ok s1 L1 c1) :
    evalF κ (A;; B) s L = (evalF κ B s1 L1).addCost c1 := by
  simp [evalF, h, Res.bind]

theorem evalF_call_ok {κ : Caps} {q : Proc} {args : List Exp} {ds : List Reg} {s s' : Core}
    {L L' : Loc} {vs : List Nat} {c : Nat} (ha : evList κ s L args = some vs)
    (hb : evalF κ q.body s (State.setLocs (fun _ => 0) q.params vs) = .ok s' L' c) :
    evalF κ (q.call args ds) s L =
      .ok s' (State.setLocs L ds (q.rets.map L')) (1 + costList args + ds.length + c) := by
  simp [Proc.call, evalF, ha, hb]

theorem Res.addCost_ok {s : Core} {L : Loc} {c c' : Nat} :
    (Res.ok s L c').addCost c = .ok s L (c + c') :=
  rfl

/-- A Level F `bind` that succeeded: both parts succeeded. -/
theorem run_bind_ok {α β : Type} {m : CM α} {f : α → CM β} {s s' : Core} {b : β}
    (h : (m >>= f).run s = .ok b s') : ∃ a s1, m.run s = .ok a s1 ∧ (f a).run s1 = .ok b s' := by
  rw [OrderMaintenance.Proof.run_bind] at h
  revert h
  cases m.run s with
  | ok a s1 => intro h; exact ⟨a, s1, rfl, h⟩
  | error e s1 => intro h; simp at h

end OrderMaintenance.Impl
