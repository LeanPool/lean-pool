/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.Syntax


/-!
# Cost semantics

`exec c s` runs statement `c` from state `s`. It returns the final state, the number of steps
taken, and a status. The cost is part of the semantics: every expression node, assignment,
array access, allocation, branch, loop iteration, call, returned value and handler entry
costs one step. No other computation is available to a program.

Two kinds of abnormal termination:
* `fail` is an algorithmic guard. It propagates to the nearest `catch`.
* `err` is a machine error: an array access beyond the capacity, or a subtraction that would go
  below 0. The proofs show that it never happens.
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-- Array memory, capacities, local registers and the ghost peak value of the RAM. -/
structure State where
  /-- Total natural-number contents of every named machine array. -/
  mem : Arr → Nat → Nat
  /-- Allocated capacity of each named machine array. -/
  cap : Arr → Nat
  /-- Natural-number value of each local register. -/
  loc : Reg → Nat
  /-- The largest value computed so far (ghost; read only by the word-size theorem). -/
  peak : Nat

namespace State

/-- The zero-filled initial RAM with zero capacities and zero locals. -/
def init : State := ⟨fun _ _ => 0, fun _ => 0, fun _ => 0, 0⟩

/-- Update one point of a function. -/
def upd {α : Type} [DecidableEq α] (f : α → Nat) (a : α) (v : Nat) : α → Nat :=
  fun b => if b = a then v else f b

/-- Write one local register without changing array memory. -/
def setLoc (s : State) (x : Reg) (v : Nat) : State := { s with loc := upd s.loc x v }

/-- Write one array cell without changing capacities or locals. -/
def write (s : State) (a : Arr) (i v : Nat) : State :=
  { s with mem := fun b => if b = a then upd (s.mem a) i v else s.mem b }

/-- Reset one named array to zero and assign its capacity. -/
def alloc (s : State) (a : Arr) (n : Nat) : State :=
  { s with mem := fun b => if b = a then fun _ => 0 else s.mem b, cap := upd s.cap a n }

/-- Record a computed value in the ghost peak bound. -/
def bump (s : State) (v : Nat) : State := { s with peak := max s.peak v }

/-- Assign values to a list of locals, left to right. -/
def setLocs (f : Reg → Nat) : List Reg → List Nat → Reg → Nat
  | x :: xs, v :: vs => setLocs (upd f x v) xs vs
  | _, _ => f

/-- The callee's frame: parameters bound to the argument values, every other local 0. -/
def enter (s : State) (params : List Reg) (vs : List Nat) : State :=
  { s with loc := setLocs (fun _ => 0) params vs }

/-- Return to the caller's frame `caller`, copying the callee's locals `rets` to `dsts`. -/
def leave (s : State) (caller : Reg → Nat) (rets dsts : List Reg) : State :=
  { s with loc := setLocs caller dsts (rets.map s.loc) }

end State

/-- Evaluate a binary natural-number primitive, rejecting invalid arithmetic. -/
def BinOp.eval : BinOp → Nat → Nat → Option Nat
  | .add, a, b => some (a + b)
  | .sub, a, b => if b ≤ a then some (a - b) else none
  | .mul, a, b => some (a * b)
  | .div, a, b => some (a / b)
  | .mod, a, b => some (a % b)
  | .shl, a, b => some (a * 2 ^ b)
  | .shr, a, b => some (a / 2 ^ b)
  | .lt, a, b => some (if a < b then 1 else 0)
  | .le, a, b => some (if a ≤ b then 1 else 0)
  | .eq, a, b => some (if a = b then 1 else 0)
  | .and, a, b => some (if a ≠ 0 ∧ b ≠ 0 then 1 else 0)
  | .or, a, b => some (if a ≠ 0 ∨ b ≠ 0 then 1 else 0)

/-- Evaluate Boolean negation or the most-significant-bit index. -/
def UnOp.eval : UnOp → Nat → Nat
  | .not, a => if a = 0 then 1 else 0
  | .msb, a => Nat.log2 a

namespace Expr

/-- Evaluate a RAM expression, rejecting out-of-bounds reads and invalid arithmetic. -/
def eval (s : State) : Expr → Option Nat
  | lit n => some n
  | var x => some (s.loc x)
  | load a i => (i.eval s).bind fun j => if j < s.cap a then some (s.mem a j) else none
  | bin op e₁ e₂ => (e₁.eval s).bind fun a => (e₂.eval s).bind fun b => op.eval a b
  | un op e => (e.eval s).map op.eval

/-- The cost of evaluating an expression depends only on its syntax. -/
def cost : Expr → Nat
  | lit _ | var _ => 1
  | load _ i => 1 + i.cost
  | bin _ e₁ e₂ => 1 + e₁.cost + e₂.cost
  | un _ e => 1 + e.cost

/-- The largest value among the expression and all its subexpressions. -/
def maxv (s : State) : Expr → Nat
  | lit n => n
  | var x => s.loc x
  | e@(load _ i) => max (i.maxv s) ((e.eval s).getD 0)
  | e@(bin _ e₁ e₂) => max (max (e₁.maxv s) (e₂.maxv s)) ((e.eval s).getD 0)
  | e@(un _ e₁) => max (e₁.maxv s) ((e.eval s).getD 0)

end Expr

/-- Evaluate all argument expressions, failing if any expression is invalid. -/
def evalList (s : State) (es : List Expr) : Option (List Nat) := es.mapM (·.eval s)
/-- Sum the static instruction costs of the argument expressions. -/
def costList (es : List Expr) : Nat := (es.map Expr.cost).sum
/-- Largest intermediate value produced by evaluating the argument expressions. -/
def maxvList (s : State) (es : List Expr) : Nat := (es.map (Expr.maxv s)).foldr max 0

/-- Normal termination, recoverable failure or an internal machine error. -/
inductive Status where
  | ok | fail | err
  deriving DecidableEq, Repr

/-- A RAM execution outcome with its reached state and charged instruction cost. -/
structure Out where
  /-- Machine state reached on normal or abnormal termination. -/
  st : State
  /-- Total number of charged machine instructions. -/
  cost : Nat
  /-- Normal, recoverable-failure or internal-error termination status. -/
  status : Status

/-- Sequential composition of outcomes: costs add; abnormal termination propagates. -/
def Out.bind (o : Out) (g : State → Out) : Out :=
  match o.status with
  | .ok => let o' := g o.st; ⟨o'.st, o.cost + o'.cost, o'.status⟩
  | _ => o

/-- Iterations `k, k+1, …, k+n-1` of a loop with counter `x` and body `f`; each costs
one step plus the body. -/
def runFor (f : State → Out) (x : Reg) : Nat → Nat → State → Out
  | _, 0, s => ⟨s, 0, .ok⟩
  | k, n + 1, s => (Out.bind ⟨s, 1, .ok⟩ fun s => f (s.setLoc x k)).bind (runFor f x (k + 1) n)

/-- Execute the RAM statement with explicit costs and guarded memory access. -/
def exec : Stmt → State → Out
  | .skip, s => ⟨s, 1, .ok⟩
  | .assign x e, s =>
    match e.eval s with
    | some v => ⟨(s.bump (e.maxv s)).setLoc x v, 1 + e.cost, .ok⟩
    | none => ⟨s, 1 + e.cost, .err⟩
  | .store a i e, s =>
    match i.eval s, e.eval s with
    | some j, some v =>
      if j < s.cap a then ⟨((s.bump (i.maxv s)).bump (e.maxv s)).write a j v,
        1 + i.cost + e.cost, .ok⟩
      else ⟨s, 1 + i.cost + e.cost, .err⟩
    | _, _ => ⟨s, 1 + i.cost + e.cost, .err⟩
  | .alloc a n, s =>
    match n.eval s with
    | some k => ⟨(s.bump (n.maxv s)).alloc a k, 1 + n.cost, .ok⟩
    | none => ⟨s, 1 + n.cost, .err⟩
  | .seq c d, s => (exec c s).bind (exec d)
  | .ite c t f, s =>
    match c.eval s with
    | some v => Out.bind ⟨s.bump (c.maxv s), 1 + c.cost, .ok⟩ (if v ≠ 0 then exec t else exec f)
    | none => ⟨s, 1 + c.cost, .err⟩
  | .loop x n b, s =>
    match n.eval s with
    | some k => Out.bind ⟨s.bump (n.maxv s), 1 + n.cost, .ok⟩ (runFor (exec b) x 0 k)
    | none => ⟨s, 1 + n.cost, .err⟩
  | .call _ ps b rs args ds, s =>
    match evalList s args with
    | some vs =>
      let o := exec b ((s.bump (maxvList s args)).enter ps vs)
      let c := 1 + costList args + ds.length + o.cost
      match o.status with
      | .ok => ⟨o.st.leave s.loc rs ds, c, .ok⟩
      | .fail => ⟨{ o.st with loc := s.loc }, c, .fail⟩
      | .err => ⟨o.st, c, .err⟩
    | none => ⟨s, 1 + costList args, .err⟩
  | .fail, s => ⟨s, 1, .fail⟩
  | .catch c h, s =>
    let o := exec c s
    match o.status with
    | .fail => let o' := exec h o.st; ⟨o'.st, 1 + o.cost + o'.cost, o'.status⟩
    | _ => ⟨o.st, 1 + o.cost, o.status⟩

end OrderMaintenance.Machine
