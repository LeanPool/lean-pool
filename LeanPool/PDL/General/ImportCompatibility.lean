/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public meta import Lean

/-! # Retaining auxiliary declarations across module splits -/

public meta section

open Lean

namespace PDL.ImportCompatibility

private def mappedExpression (source target : Name) (expression : Expr) : Expr :=
  expression.replace fun expression =>
    match expression with
    | .const name levels =>
      if source.isPrefixOf name then some (.const (name.replacePrefix source target) levels)
      else none
    | _ => none

private def mappedDeclaration (source target : Name) (info : ConstantInfo) : CoreM Declaration := do
  let name := info.name.replacePrefix source target
  let type := mappedExpression source target info.type
  match info with
  | .defnInfo value =>
    return .defnDecl {value with
      name := name
      type := type
      value := mappedExpression source target value.value
      all := value.all.map (fun n => n.replacePrefix source target)}
  | .thmInfo value =>
    return .thmDecl {value with
      name := name
      type := type
      value := mappedExpression source target value.value
      all := value.all.map (fun n => n.replacePrefix source target)}
  | _ => throwError "unsupported auxiliary declaration: {info.name}"

private def privateDeclarations (moduleName : Name) : CoreM (Array ConstantInfo) := do
  let env ← getEnv
  unless env.header.moduleNames.contains moduleName do
    throwError "module is not imported: {moduleName}"
  let modulePrefix := `_private ++ moduleName
  let mut result := #[]
  for (name, data) in env.header.moduleNames.zip env.header.moduleData do
    unless name == moduleName do continue
    for declaration in data.constNames do
      if modulePrefix.isPrefixOf declaration then
        result := result.push (← getConstInfo declaration)
  return result

/-- Retain original auxiliary names after moving their parent declarations to another module.
The kernel checks every copied type and value; existing declarations are never replaced. -/
def retainPrivateDeclarations (sourceModule targetModule : Name) : CoreM Unit := do
  let source := `_private ++ sourceModule
  let target := `_private ++ targetModule
  let mut pending ← privateDeclarations sourceModule
  for _ in [:pending.size] do
    if pending.isEmpty then break
    let mut remaining := #[]
    let mut progress := false
    for info in pending do
      let env ← getEnv
      let name := info.name.replacePrefix source target
      if let some existing := env.find? name then
        unless existing.type == mappedExpression source target info.type &&
            existing.levelParams == info.levelParams && existing.isUnsafe == info.isUnsafe &&
            existing.isPartial == info.isPartial do
          throwError "incompatible auxiliary declaration: {name}"
        progress := true
        continue
      let references := info.type.getUsedConstants ++
        (info.value? (allowOpaque := true)).toArray.flatMap Expr.getUsedConstants
      if !(references.all fun n => !source.isPrefixOf n ||
          env.contains (n.replacePrefix source target)) then
        remaining := remaining.push info
        continue
      -- Match the kernel declarations produced by Lean's auxiliary generators, without
      -- compiling recursor helpers that are used only while constructing proofs.
      addDecl (← mappedDeclaration source target info)
      progress := true
    if !progress then throwError "cyclic auxiliary declarations in {sourceModule}"
    pending := remaining
  unless pending.isEmpty do throwError "incomplete auxiliary declarations in {sourceModule}"

end PDL.ImportCompatibility
