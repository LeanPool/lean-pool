/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.Exec


/-!
# The machine with `w`-bit words

`execW w` is `exec` (`Exec.lean`) on a machine whose words have `w` bits. It is `exec` verbatim,
with one change: wherever `exec` evaluates an expression (`e.eval s`, `evalList s args`) and then
records its values in the peak (`bump`), `execW` evaluates it with `evalW w` (`evalListW w`),
which also fails when the expression or one of its subexpressions has a value `≥ 2^w`, i.e. when
a value `maxv` would record does not fit in a word. Such an expression is treated like any other
expression that fails to evaluate (an array access beyond the capacity, a subtraction below 0): the
statement ends with the machine error `.err`, at the same cost.

Every value a program handles is the value of an evaluated expression: a local or memory cell
is read only through an expression, and the loop counter stays below the loop bound. So `execW w`
never holds a value `≥ 2^w` that it has computed.

`execW_agree` (`Impl/PeakWord.lean`): if the run of `exec` computes no value `≥ 2^w`
(`dpk c s < 2^w`), then `execW w c s = exec c s`: same state, cost and status.
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-- **Evaluation on `w`-bit words**: `e.eval s`, or `none` if a value of the expression or of a
subexpression (a value `maxv` records) is `≥ 2^w`. -/
def Expr.evalW (w : Nat) (s : State) (e : Expr) : Option Nat :=
  if e.maxv s < 2 ^ w then e.eval s else none

/-- `evalList` on `w`-bit words. -/
def evalListW (w : Nat) (s : State) (es : List Expr) : Option (List Nat) :=
  if maxvList s es < 2 ^ w then evalList s es else none

/-- **The `w`-bit machine**: `exec` with `evalW w` for `eval` and `evalListW w` for `evalList`. -/
def execW (w : Nat) : Stmt → State → Out
  | .skip, s => ⟨s, 1, .ok⟩
  | .assign x e, s =>
    match e.evalW w s with
    | some v => ⟨(s.bump (e.maxv s)).setLoc x v, 1 + e.cost, .ok⟩
    | none => ⟨s, 1 + e.cost, .err⟩
  | .store a i e, s =>
    match i.evalW w s, e.evalW w s with
    | some j, some v =>
      if j < s.cap a then ⟨((s.bump (i.maxv s)).bump (e.maxv s)).write a j v,
        1 + i.cost + e.cost, .ok⟩
      else ⟨s, 1 + i.cost + e.cost, .err⟩
    | _, _ => ⟨s, 1 + i.cost + e.cost, .err⟩
  | .alloc a n, s =>
    match n.evalW w s with
    | some k => ⟨(s.bump (n.maxv s)).alloc a k, 1 + n.cost, .ok⟩
    | none => ⟨s, 1 + n.cost, .err⟩
  | .seq c d, s => (execW w c s).bind (execW w d)
  | .ite c t f, s =>
    match c.evalW w s with
    | some v => Out.bind ⟨s.bump (c.maxv s), 1 + c.cost, .ok⟩ (if v ≠ 0 then execW w t else execW w f)
    | none => ⟨s, 1 + c.cost, .err⟩
  | .loop x n b, s =>
    match n.evalW w s with
    | some k => Out.bind ⟨s.bump (n.maxv s), 1 + n.cost, .ok⟩ (runFor (execW w b) x 0 k)
    | none => ⟨s, 1 + n.cost, .err⟩
  | .call _ ps b rs args ds, s =>
    match evalListW w s args with
    | some vs =>
      let o := execW w b ((s.bump (maxvList s args)).enter ps vs)
      let c := 1 + costList args + ds.length + o.cost
      match o.status with
      | .ok => ⟨o.st.leave s.loc rs ds, c, .ok⟩
      | .fail => ⟨{ o.st with loc := s.loc }, c, .fail⟩
      | .err => ⟨o.st, c, .err⟩
    | none => ⟨s, 1 + costList args, .err⟩
  | .fail, s => ⟨s, 1, .fail⟩
  | .catch c h, s =>
    let o := execW w c s
    match o.status with
    | .fail => let o' := execW w h o.st; ⟨o'.st, 1 + o.cost + o'.cost, o'.status⟩
    | _ => ⟨o.st, 1 + o.cost, o.status⟩

end OrderMaintenance.Machine
