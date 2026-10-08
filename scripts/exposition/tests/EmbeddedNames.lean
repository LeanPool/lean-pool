/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module

import all Extract

open Lean

namespace ExpositionTests

/-- The previous tree traversal provides a semantic oracle on small inputs. -/
partial def treeNames (e : Expr) : Array Name := Id.run do
  let mut names := #[]
  if let some name := Exposition.evalNameExpr? e then names := names.push name
  match e with
  | .app f a => return names ++ treeNames f ++ treeNames a
  | .lam _ t b _ => return names ++ treeNames t ++ treeNames b
  | .forallE _ t b _ => return names ++ treeNames t ++ treeNames b
  | .letE _ t v b _ => return names ++ treeNames t ++ treeNames v ++ treeNames b
  | .mdata _ b => return names ++ treeNames b
  | .proj _ _ b => return names ++ treeNames b
  | _ => return names

def normalize (names : Array Name) : List String :=
  (names.toList.map Name.toString).eraseDups.mergeSort (· ≤ ·)

def sharedExpression (depth : Nat) (leaf : Expr) : Expr := Id.run do
  let mut expression := leaf
  for _ in [:depth] do
    expression := mkApp2 (mkConst `pair) expression expression
  return expression

def check : IO Unit := do
  let anonymous := mkConst ``Name.anonymous
  let short := mkApp (mkConst ``Name.mkStr1) (mkStrLit "payload")
  let nested := mkApp2 (mkConst ``Name.str) short (mkStrLit "child")
  let numbered := mkApp2 (mkConst ``Name.num) nested (mkNatLit 7)
  let expressions := #[
    anonymous, short, nested, numbered,
    mkApp2 (mkConst ``Name.mkNum) nested (mkNatLit 9),
    mkApp2 (mkConst ``Name.mkStr2) (mkStrLit "one") (mkStrLit "two"),
    mkApp3 (mkConst ``Name.mkStr3) (mkStrLit "one") (mkStrLit "two") (mkStrLit "three"),
    mkApp4 (mkConst ``Name.mkStr4) (mkStrLit "one") (mkStrLit "two")
      (mkStrLit "three") (mkStrLit "four"),
    mkLambda `binder .default short numbered,
    mkForall `binder .default nested numbered,
    mkLet `binder short nested numbered,
    mkMData {} numbered,
    mkProj `structure 0 numbered
  ]
  for expression in expressions do
    for depth in [:8] do
      let value := sharedExpression depth expression
      unless normalize (Exposition.collectEmbeddedNames value) == normalize (treeNames value) do
        throw <| IO.userError "memoized traversal lost an embedded name"
  -- Only 18 pair nodes are stored, although the expanded tree has 262144 leaves.
  let found := Exposition.collectEmbeddedNames (sharedExpression 18 short)
  unless found == #[`payload] do
    throw <| IO.userError s!"shared expressions were expanded repeatedly: {found.size} names"
  IO.println "embedded-name semantics and shared-expression regression passed"

end ExpositionTests

#eval ExpositionTests.check
