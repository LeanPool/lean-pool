/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4RowBuilder

/-!
# Data terms for the `1/40` certificate

The certificate data of Theorem S4 (grid points, bands, chord conditions and the weighted row
tags of each case) is written in the generated Lean files as string literals. The term
elaborators of this file turn such a string into a term:

* `s4_qtree% "n d …"`: an `LTree ℚ` of the rationals `n/d` (one pair per line);
* `s4_ntree3% "a b c …"`: an `LTree (Nat × Nat × Nat)` (one triple per line);
* `s4_ctree% "n₁ d₁ n₂ d₂ n₃ d₃ …"`: an `LTree (ℚ × ℚ × ℚ)` (one triple per line);
* `s4_rows% "z tag args …"`: a balanced `WTree Tag` of weighted row tags (one per line).

The elaborators only build terms; the kernel checks every use of the data. `LTree` stores
the entry of index `i` at the path of the binary digits of `i`, lowest digit first, so that
`LTree.get` is a short kernel computation.
-/

@[expose] public section

namespace Esgk.S4

open Lean Elab Term Meta

/-- A binary tree with values at the leaves. -/
inductive LTree (α : Type) where
  | leaf (a : α)
  | node (l r : LTree α)

/-- The entry of index `k`: the lowest binary digit of `k` picks the subtree. -/
noncomputable def LTree.get {α : Type} (t : LTree α) : Nat → α :=
  LTree.rec (motive := fun _ ↦ Nat → α) (fun a _ ↦ a)
    (fun _ _ fl fr k ↦ bif Nat.beq (k % 2) 0 then fl (k / 2) else fr (k / 2)) t

meta section

def naturalExpression (n : Nat) : Expr := mkRawNatLit n

def rationalExpression (n d : Nat) : Expr :=
  mkApp2 (Lean.mkConst ``mkRat) (mkApp (Lean.mkConst ``Int.ofNat) (naturalExpression n))
    (naturalExpression d)

def splitWords (line : String) : List String :=
  (line.splitOn " ").filter (· ≠ "")

def splitNonemptyLines (s : String) : List (List String) :=
  ((s.splitOn "\n").map splitWords).filter (· ≠ [])

def parseNatural (w : String) : Nat := w.toNat!

/-- The tree with `xs[i]` at the path of the binary digits of `i` (lowest first); `xs` is
padded to a power of two with its last entry. -/
def lowBitExpressionTree (ty : Expr) (xs : Array Expr) : Expr :=
  let leafE (a : Expr) : Expr := mkApp2 (Lean.mkConst ``LTree.leaf) ty a
  let rec go (ys : Array Expr) : Expr :=
    if ys.size ≤ 1 then leafE ys[0]!
    else
      let ev := (Array.range (ys.size / 2)).map (fun i ↦ ys[2 * i]!)
      let od := (Array.range (ys.size / 2)).map (fun i ↦ ys[2 * i + 1]!)
      mkApp3 (Lean.mkConst ``LTree.node) ty (go ev) (go od)
    termination_by ys.size
    decreasing_by all_goals simp only [Array.size_map, Array.size_range]; omega
  Id.run do
    let mut ys := xs
    let mut sz := 1
    while sz < ys.size do sz := 2 * sz
    while ys.size < sz do ys := ys.push ys[ys.size - 1]!
    return go ys

def productExpression (α β : Expr) (a b : Expr) : Expr :=
  mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b

def productType (α β : Expr) : Expr := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) α β

elab "s4_qtree% " s:str : term => do
  let xs := (splitNonemptyLines s.getString).toArray.map fun ws ↦
    rationalExpression (parseNatural ws[0]!) (parseNatural ws[1]!)
  return lowBitExpressionTree (Lean.mkConst ``Rat) xs

elab "s4_ntree3% " s:str : term => do
  let nat := Lean.mkConst ``Nat
  let xs := (splitNonemptyLines s.getString).toArray.map fun ws ↦
    productExpression nat (productType nat nat) (naturalExpression (parseNatural ws[0]!))
      (productExpression nat nat (naturalExpression (parseNatural ws[1]!))
        (naturalExpression (parseNatural ws[2]!)))
  return lowBitExpressionTree (productType nat (productType nat nat)) xs

elab "s4_ctree% " s:str : term => do
  let q := Lean.mkConst ``Rat
  let xs := (splitNonemptyLines s.getString).toArray.map fun ws ↦
    productExpression q (productType q q)
      (rationalExpression (parseNatural ws[0]!) (parseNatural ws[1]!))
      (productExpression q q (rationalExpression (parseNatural ws[2]!) (parseNatural ws[3]!))
        (rationalExpression (parseNatural ws[4]!) (parseNatural ws[5]!)))
  return lowBitExpressionTree (productType q (productType q q)) xs

/-- The constructor and the number of arguments of a tag name. -/
def tagConstructor : String → Option (Name × Nat)
  | "amono" => some (``Tag.amono, 2)
  | "xmono" => some (``Tag.xmono, 2)
  | "xpos" => some (``Tag.xpos, 1)
  | "xleq" => some (``Tag.xleq, 1)
  | "a2lo" => some (``Tag.a2lo, 1)
  | "mlo" => some (``Tag.mlo, 0)
  | "layer" => some (``Tag.layer, 2)
  | "pa" => some (``Tag.pa, 4)
  | "pb" => some (``Tag.pb, 4)
  | "pc" => some (``Tag.pc, 4)
  | "aa" => some (``Tag.aa, 5)
  | "jj" => some (``Tag.jj, 5)
  | "ab1" => some (``Tag.ab1, 2)
  | "ab2" => some (``Tag.ab2, 1)
  | "ab3" => some (``Tag.ab3, 3)
  | "ab4" => some (``Tag.ab4, 3)
  | "ab6u" => some (``Tag.ab6u, 2)
  | "ab6v" => some (``Tag.ab6v, 3)
  | "caselo" => some (``Tag.caselo, 0)
  | "casehi" => some (``Tag.casehi, 0)
  | _ => none

def balancedExpressionTree (node : Expr → Expr → Expr) (xs : Array Expr) (lo hi : Nat) :
    Expr :=
  if hi - lo ≤ 1 then xs[lo]!
  else
    let m := (lo + hi) / 2
    node (balancedExpressionTree node xs lo m) (balancedExpressionTree node xs m hi)
termination_by hi - lo
decreasing_by all_goals omega

elab "s4_rows% " s:str : term => do
  let tagT := Lean.mkConst ``Tag
  let mut leaves : Array Expr := #[]
  for ws in splitNonemptyLines s.getString do
    let some (c, k) := tagConstructor ws[1]! | throwError "unknown tag {ws[1]!}"
    unless ws.length == k + 2 do throwError "tag {ws[1]!}: expected {k} arguments"
    let tag := mkAppN (Lean.mkConst c)
      ((ws.drop 2).toArray.map fun w ↦ naturalExpression (parseNatural w))
    leaves := leaves.push
      (mkApp3 (Lean.mkConst ``FarkasPackedCheck.WTree.leaf) tagT
        (naturalExpression (parseNatural ws[0]!)) tag)
  if leaves.isEmpty then throwError "no rows"
  return balancedExpressionTree (mkApp3 (Lean.mkConst ``FarkasPackedCheck.WTree.node) tagT)
    leaves 0 leaves.size

end

end Esgk.S4
