/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4PackedCertificateSummary
public import LeanPool.DistinctDistances.S4CertificateParams
meta import LeanPool.DistinctDistances.S4RowBuilder
public meta import LeanPool.DistinctDistances.S4DataElab

/-!
# Executable certificate subtree summaries

Propose the four values checked by the kernel for a weighted certificate subtree.
-/

namespace Esgk.S4

open Lean Elab Term FarkasPackedCheck

meta section

private def slotWidth : Nat := 256

private def trieDepth : Nat := 4

private def chunkCount : Nat := 2 ^ trieDepth

private def constructorArguments (expression : Expr) (constructor : Name) (arity : Nat) :
    TermElabM (Array Expr) := do
  let expression := expression.consumeMData
  unless expression.isAppOfArity constructor arity do
    throwError "expected certificate constructor {constructor} with {arity} arguments"
  return expression.getAppArgs

private def decodeNat (expression : Expr) : TermElabM Nat := do
  let some literal := Lean.Meta.getRawNatValue? expression
    | throwError "expected a natural literal in certificate data"
  return literal

private def decodeRat (expression : Expr) : TermElabM ℚ := do
  let fields ← constructorArguments expression ``mkRat 2
  let numerator ← constructorArguments fields[0]! ``Int.ofNat 1
  return mkRat (Int.ofNat (← decodeNat numerator[0]!)) (← decodeNat fields[1]!)

private def decodeTriple {α : Type} (item : Expr → TermElabM α) (expression : Expr) :
    TermElabM (α × α × α) := do
  let outer ← constructorArguments expression ``Prod.mk 4
  let inner ← constructorArguments outer[3]! ``Prod.mk 4
  return (← item outer[2]!, ← item inner[2]!, ← item inner[3]!)

private def decodeLookupTree {α : Type} (element : Expr → TermElabM α) :
    Nat → Expr → TermElabM (LTree α)
  | 0, _ => throwError "unexpected depth in certificate lookup tree"
  | fuel + 1, expression => do
    let expression := expression.consumeMData
    if expression.isAppOfArity ``LTree.leaf 2 then
      return .leaf (← element (expression.getArg! 1))
    let children ← constructorArguments expression ``LTree.node 3
    return .node (← decodeLookupTree element fuel children[1]!)
      (← decodeLookupTree element fuel children[2]!)

private def parameterScalar (projection : Name) : TermElabM Nat := do
  let expression := mkApp (Lean.mkConst projection) (Lean.mkConst ``params)
  let value ← Lean.Meta.whnfD expression
  let some literal ← Lean.Meta.getNatValue? value
    | throwError "expected certificate parameter {projection} to be a natural number"
  return literal

private def lookup {α : Type} : LTree α → Nat → α
  | .leaf value, _ => value
  | .node left right, index =>
    if index % 2 == 0 then lookup left (index / 2) else lookup right (index / 2)

private def readParameters : TermElabM Params := do
  let grid ← decodeLookupTree decodeRat 32 (← getConstInfoDefn ``gridT).value
  let bands ← decodeLookupTree (decodeTriple decodeNat) 32 (← getConstInfoDefn ``bandT).value
  let chords ← decodeLookupTree (decodeTriple decodeRat) 32 (← getConstInfoDefn ``chordConds).value
  let gridCount ← parameterScalar ``Params.ng
  let bandCount ← parameterScalar ``Params.nb
  let chordCount ← parameterScalar ``Params.nch
  return {
    ng := gridCount
    g := lookup grid
    nb := bandCount
    bLam band := (lookup bands band).1
    bLo band := (lookup bands band).2.1
    bHi band := (lookup bands band).2.2
    nch := chordCount
    ch := lookup chords
  }

private def decodeTag (expression : Expr) : TermElabM Tag := do
  let expression := expression.consumeMData
  let constructor := expression.getAppFn
  let arguments ← expression.getAppArgs.mapM decodeNat
  let tag : Option Tag := match arguments.toList with
    | [] =>
      if constructor.isConstOf ``Tag.mlo then some .mlo
      else if constructor.isConstOf ``Tag.caselo then some .caselo
      else if constructor.isConstOf ``Tag.casehi then some .casehi else none
    | [first] =>
      if constructor.isConstOf ``Tag.xpos then some (.xpos first)
      else if constructor.isConstOf ``Tag.xleq then some (.xleq first)
      else if constructor.isConstOf ``Tag.a2lo then some (.a2lo first)
      else if constructor.isConstOf ``Tag.ab2 then some (.ab2 first) else none
    | [first, second] =>
      if constructor.isConstOf ``Tag.amono then some (.amono first second)
      else if constructor.isConstOf ``Tag.xmono then some (.xmono first second)
      else if constructor.isConstOf ``Tag.layer then some (.layer first second)
      else if constructor.isConstOf ``Tag.ab1 then some (.ab1 first second)
      else if constructor.isConstOf ``Tag.ab6u then some (.ab6u first second) else none
    | [first, second, third] =>
      if constructor.isConstOf ``Tag.ab3 then some (.ab3 first second third)
      else if constructor.isConstOf ``Tag.ab4 then some (.ab4 first second third)
      else if constructor.isConstOf ``Tag.ab6v then some (.ab6v first second third) else none
    | [first, second, third, fourth] =>
      if constructor.isConstOf ``Tag.pa then some (.pa first second third fourth)
      else if constructor.isConstOf ``Tag.pb then some (.pb first second third fourth)
      else if constructor.isConstOf ``Tag.pc then some (.pc first second third fourth) else none
    | [first, second, third, fourth, fifth] =>
      if constructor.isConstOf ``Tag.aa then some (.aa first second third fourth fifth)
      else if constructor.isConstOf ``Tag.jj then some (.jj first second third fourth fifth)
      else none
    | _ => none
  let some decoded := tag | throwError "unexpected constructor or arity in certificate row tag"
  return decoded

private structure SummaryAccumulator where
  positive : Array (Option Nat)
  negative : Array (Option Nat)
  cost : Nat
  rhs : Int

private def packRow (parameters : Params) (lower upper : ℚ)
    (summary : SummaryAccumulator) (weight : Nat) (tag : Tag) :
    SummaryAccumulator := Id.run do
  let some row := parameters.build lower upper tag
    | return { summary with cost := summary.cost + 2 ^ slotWidth }
  let denominator := row.ent.foldl (fun common entry ↦ Nat.lcm entry.2.den common) row.rhs.den
  let chunkLength := chunkLen parameters.nv trieDepth
  let rhs := summary.rhs + (weight : Int) * QRow.scaleNumerator denominator row.rhs
  let mut cost := summary.cost
  let mut positive := summary.positive
  let mut negative := summary.negative
  for (index, coefficient) in row.ent do
    if coefficient = 0 then
      continue
    -- PackTrie.single routes indices beyond its depth to the rightmost leaf.
    let chunk := min (index / chunkLength) (chunkCount - 1)
    let magnitude := (QRow.scaleNumerator denominator coefficient).natAbs
    let weighted := weight * magnitude
    let penalty := bif Nat.blt index parameters.nv then 0 else 2 ^ slotWidth
    cost := cost + (weighted + penalty)
    let shifted := weighted <<< (slotWidth * (index % chunkLength))
    let addToBucket (previous : Option Nat) := some (previous.getD 0 + shifted)
    if 0 < coefficient then
      positive := positive.modify chunk addToBucket
    else
      negative := negative.modify chunk addToBucket
  return ⟨positive, negative, cost, rhs⟩

private def packRows (addRow : SummaryAccumulator → Nat → Tag → SummaryAccumulator) :
    Nat → Expr → SummaryAccumulator → TermElabM SummaryAccumulator
  | 0, _, _ => throwError "unexpected depth in certificate row tree"
  | fuel + 1, expression, summary => do
    let expression := expression.consumeMData
    let expression ←
      if expression.isAppOfArity ``WTree.leaf 3 || expression.isAppOfArity ``WTree.node 3 then
        pure expression
      else
        Lean.Meta.whnfD expression
    if expression.isAppOfArity ``WTree.leaf 3 then
      let weight ← decodeNat (expression.getArg! 1)
      let tag ← decodeTag (expression.getArg! 2)
      return addRow summary weight tag
    let children ← constructorArguments expression ``WTree.node 3
    let summary ← packRows addRow fuel children[1]! summary
    packRows addRow fuel children[2]! summary

private def quoteTrie (buckets : Array (Option Nat)) : Nat → Nat → Option Expr
  | 0, start => buckets[start]!.map fun value ↦
    mkApp (Lean.mkConst ``PackTrie.leaf) (mkRawNatLit value)
  | depth + 1, start =>
    let left := quoteTrie buckets depth start
    let right := quoteTrie buckets depth (start + 2 ^ depth)
    if left.isNone && right.isNone then none
    else
      let zero := Lean.mkConst ``PackTrie.zero
      some (mkApp2 (Lean.mkConst ``PackTrie.node) (left.getD zero) (right.getD zero))

private def quoteInteger : Int → Expr
  | .ofNat value => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit value)
  | .negSucc value => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit value)

end

elab "s4_summary% " caseIndex:num ", " rows:term : term => do
  let rowsType := mkApp (Lean.mkConst ``WTree) (Lean.mkConst ``Tag)
  let expression ← elabTermEnsuringType rows rowsType
  let quarter ← match expression.consumeMData with
    | .const name _ => pure (← getConstInfoDefn name).value
    | expression => pure expression
  let runtimeParams ← readParameters
  let caseBounds ← decodeLookupTree decodeRat 32 (← getConstInfoDefn ``caseY).value
  let index := caseIndex.getNat
  let lower := lookup caseBounds index
  let upper := lookup caseBounds (index + 1)
  let empty := Array.replicate chunkCount none
  let summary ← packRows (packRow runtimeParams lower upper) 32 quarter ⟨empty, empty, 0, 0⟩
  let zero := Lean.mkConst ``PackTrie.zero
  return mkApp4 (Lean.mkConst ``PackedSummary.mk)
    (mkRawNatLit summary.cost) (quoteInteger summary.rhs)
    ((quoteTrie summary.positive trieDepth 0).getD zero)
    ((quoteTrie summary.negative trieDepth 0).getD zero)

-- Balanced certificate trees already have the required subtree boundaries.
elab "s4_subtree% " rows:ident levels:num index:num : term => do
  let mut tree ← elabTerm rows none
  let levels := levels.getNat
  let index := index.getNat
  unless index < 2 ^ levels do throwError "unexpected certificate subtree index"
  for offset in List.range levels do
    let exposed ← Lean.Meta.whnfD tree
    unless exposed.isAppOfArity ``WTree.node 3 do
      throwError "expected a node at the certificate split"
    let branch := (index / 2 ^ (levels - offset - 1)) % 2
    tree := exposed.getArg! (branch + 1)
  return tree

end Esgk.S4
