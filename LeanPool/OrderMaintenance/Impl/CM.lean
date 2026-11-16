/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public meta import Lean
public import LeanPool.OrderMaintenance.Impl.Notation


/-!
# M6: concrete syntax for the core language

`cm{ … }` writes a statement of the core language and `cme{ … }` an expression:

```
cm{ gp := G[g].prev
    if gp ≠ 0 then G[gp].next := gl
    if C[c].first = g then C[c].first := gl else { x := 1; fail }
    labL ← labBeforeP(g) }
```

Statements are separated by newlines (aligned) or `;`, and `{ … }` groups them. This is
notation only: each form expands to the constructor term written with the helpers of
`Notation.lean` (`Exp.gF`, `Stm.wgF`, `;;`, `::=`, `=ₑ`, …), so the proofs see the same terms.

* Registers are identifiers: `x` is `.var "x"`. `P.k` is parameter `k`, `S.k` is scalar `k`.
* `E[i].f`, `G[i].f`, `C[i].f`, `N[i].f` are field `f` of record `i` of a table;
  `a[i]` is cell `i` of the core array `a` (`AF`).
* `k[i]` with `k : LK` is a list: `len k[i]`, `k[i][j].fst`, `append k[i] (a, b)`, `pop k[i]`;
  `k` is an `LK` constructor or a Lean variable.
* `x := new T` appends a fresh record to table `T`; `x ← p(args)` calls procedure `p`.
* `for x < n do s` is the bounded loop, `try s catch h` the handler.
* `O.k` is field `k` of the pending job or path preparation, `size T` the number of records of
  table `T`, `path(c, j)` level `j` of chunk `c`'s path; `max(a, b)`, `msb(a)`, and `a ∸ b` is
  truncated subtraction (`Exp.monus`). The other statements of `Stm` (`pcSet(…)`,
  `prepCommit`, …) keep their constructor names.
* `skip`, `fail` and `bug` are the statements of those names; any other bare identifier in
  statement position is a `Stm` defined elsewhere, and `‹t›` embeds a Lean term (an `Exp`, a
  `Stm`, or a field name).
* `x ← ‹q›(args)`, `(x, y) ← ‹q›(args)` and `call ‹q›(args)` call a procedure given by a
  Lean term `q : Proc` (e.g. `‹findP k›`, a procedure family applied to its list kind).
* `‹r› := e` assigns to the register named by the Lean term `r : Reg` (a parameter of the
  definition), as `‹r›` reads it.
* Comparisons, `!`, `&&`, `||` return 0 or 1, as `<ₑ`, `!ₑ`, … do.
-/


public meta section

namespace OrderMaintenance.Impl.CM

open Lean

/-- Field selectors in the core-program surface syntax. -/
declare_syntax_cat cmF
/-- Expressions in the core-program surface syntax. -/
declare_syntax_cat cmE (behavior := both)
/-- Statements in the core-program surface syntax. -/
declare_syntax_cat cmS (behavior := both)

open Lean.Parser in
/-- Statements separated by `;` or by line breaks at the same column. -/
def cmSeq := leading_parser sepBy1Indent (categoryParser `cmS 0) "; "

/-- A field given by its identifier. -/
syntax (name := fId) ident : cmF
/-- A field supplied as an embedded Lean term. -/
syntax (name := fTm) "‹" term "›" : cmF

/-- A natural-number literal in a core expression. -/
syntax (name := eNum) num : cmE
/-- A register, parameter, scalar or optional-job field in a core expression. -/
syntax (name := eVar) ident : cmE
/-- A parenthesized core expression. -/
syntax (name := ePar) "(" cmE ")" : cmE
/-- An embedded Lean expression term. -/
syntax (name := eTm) "‹" term "›" : cmE
/-- A field read from an indexed core record. -/
syntax (name := eFld) ident "[" cmE "]" "." cmF : cmE
/-- A read from a core array. -/
syntax (name := eArr) ident "[" cmE "]" : cmE
/-- A first or second component read from a stored list entry. -/
syntax (name := eLst) ident "[" cmE "]" "[" cmE "]" "." cmF : cmE
/-- The length of a stored core list. -/
syntax (name := eLen) &"len" ident "[" cmE "]" : cmE
/-- The number of allocated table records. -/
syntax (name := eSize) &"size" ident : cmE
/-- A read of one chunk ancestor-path entry. -/
syntax (name := ePath) &"path" "(" cmE ", " cmE ")" : cmE
/-- The maximum of two core expressions. -/
syntax (name := eMax) &"max" "(" cmE ", " cmE ")" : cmE
/-- The most-significant-bit index of a core expression. -/
syntax (name := eMsb) &"msb" "(" cmE ")" : cmE
-- The operand is at `lead` (not `max`) precedence: the forms that start with an identifier
-- (`x`, `G[i].f`, …) sit at `lead`, so `!x` and `!G[i].f` parse without parentheses.
/-- Boolean negation, represented by zero or one. -/
syntax:max (name := eNot) "!" cmE:lead : cmE
/-- Left shift of a core expression. -/
syntax:75 (name := eShl) cmE:75 " <<< " cmE:76 : cmE
/-- Right shift of a core expression. -/
syntax:75 (name := eShr) cmE:75 " >>> " cmE:76 : cmE
/-- Multiplication of core expressions. -/
syntax:70 (name := eMul) cmE:70 " * " cmE:71 : cmE
/-- Natural-number division of core expressions. -/
syntax:70 (name := eDiv) cmE:70 " / " cmE:71 : cmE
/-- Natural-number remainder of core expressions. -/
syntax:70 (name := eMod) cmE:70 " % " cmE:71 : cmE
/-- Addition of core expressions. -/
syntax:65 (name := eAdd) cmE:65 " + " cmE:66 : cmE
/-- Guarded subtraction of core expressions. -/
syntax:65 (name := eSub) cmE:65 " - " cmE:66 : cmE
/-- Truncated subtraction of core expressions. -/
syntax:65 (name := eMonus) cmE:65 " ∸ " cmE:66 : cmE
/-- Strict comparison of core expressions, returning zero or one. -/
syntax:50 (name := eLt) cmE:51 " < " cmE:51 : cmE
/-- Nonstrict comparison of core expressions, returning zero or one. -/
syntax:50 (name := eLe) cmE:51 " ≤ " cmE:51 : cmE
/-- Equality comparison of core expressions, returning zero or one. -/
syntax:50 (name := eEq) cmE:51 " = " cmE:51 : cmE
/-- Inequality comparison of core expressions, returning zero or one. -/
syntax:50 (name := eNe) cmE:51 " ≠ " cmE:51 : cmE
/-- Boolean conjunction of core expressions. -/
syntax:35 (name := eAnd) cmE:36 " && " cmE:35 : cmE
/-- Boolean disjunction of core expressions. -/
syntax:30 (name := eOr) cmE:31 " || " cmE:30 : cmE

/-- An existing core statement named by an identifier. -/
syntax (name := sId) ident : cmS
/-- An embedded Lean statement term. -/
syntax (name := sTm) "‹" term "›" : cmS
/-- A grouped sequence of core statements. -/
syntax (name := sBlk) "{" cmSeq "}" : cmS
/-- Assignment to a local register named by an identifier. -/
syntax (name := sAsg) ident " := " cmE : cmS
/-- Assignment to a register supplied as a Lean term. -/
syntax (name := sAsgT) "‹" term "›" " := " cmE : cmS
/-- Allocation of a fresh core record with its index assigned to a local. -/
syntax (name := sNew) ident " := " &"new" ident : cmS
/-- Assignment to an indexed core-record field. -/
syntax (name := sFld) ident "[" cmE "]" "." cmF " := " cmE : cmS
/-- Assignment to a core-array entry. -/
syntax (name := sArr) ident "[" cmE "]" " := " cmE : cmS
/-- Assignment to a first or second component of a stored list entry. -/
syntax (name := sLst) ident "[" cmE "]" "[" cmE "]" "." cmF " := " cmE : cmS
/-- Appending a pair to a stored core list. -/
syntax (name := sApp) &"append" ident "[" cmE "]" " (" cmE ", " cmE ")" : cmS
/-- Removing the last stored-list entry. -/
syntax (name := sPop) &"pop" ident "[" cmE "]" : cmS
/-- Clearing a stored core list. -/
syntax (name := sClr) &"clear" ident "[" cmE "]" : cmS
/-- Conditional execution of core statements. -/
syntax (name := sIf) "if " cmE " then " cmS (" else " cmS)? : cmS
/-- A bounded core loop with a local counter. -/
syntax (name := sFor) "for " ident " < " cmE " do " cmS : cmS
/-- Handling a recoverable core guard failure. -/
syntax (name := sTry) "try " cmS " catch " cmS : cmS
/-- Assignment to a chunk ancestor-path entry. -/
syntax (name := sPath) &"path" "(" cmE ", " cmE ")" " := " cmE : cmS
/-- A core statement constructor applied to expression arguments. -/
syntax (name := sCon) ident "(" cmE,* ")" : cmS
/-- A named procedure call returning one local. -/
syntax (name := sCall1) ident " ← " ident "(" cmE,* ")" : cmS
/-- A named procedure call returning a tuple of locals. -/
syntax (name := sCallN) "(" ident,* ")" " ← " ident "(" cmE,* ")" : cmS
/-- A named procedure call without returned locals. -/
syntax (name := sCall0) &"call" ident "(" cmE,* ")" : cmS
/-- An embedded procedure call returning one local. -/
syntax (name := sCall1T) ident " ← " "‹" term "›" "(" cmE,* ")" : cmS
/-- An embedded procedure call returning a tuple of locals. -/
syntax (name := sCallNT) "(" ident,* ")" " ← " "‹" term "›" "(" cmE,* ")" : cmS
/-- An embedded procedure call without returned locals. -/
syntax (name := sCall0T) &"call" "‹" term "›" "(" cmE,* ")" : cmS

/-- `ns.f` for a field identifier `f`, or the embedded term. -/
def expF (ns : Name) (f : Syntax) : MacroM Term :=
  match f.getKind with
  | ``fId => pure (mkIdent (ns ++ f[0].getId))
  | ``fTm => pure ⟨f[1]⟩
  | _ => Macro.throwErrorAt f "unexpected field"

/-- The single name component of an identifier, as a string. -/
def str (x : Syntax) : Term := Syntax.mkStrLit x.getId.toString

/-- `P.k` and `S.k`: the table prefix and the field. -/
def dotted (x : Syntax) : Option (String × Name) :=
  match x.getId with
  | .str (.str .anonymous p) k => some (p, .mkSimple k)
  | _ => none

/-- Recognize built-in stored-list kind identifiers in core syntax. -/
def isLK (k : Syntax) : Bool :=
  k.getId ∈ [`children, `table, `inTab, `side, `cin, `freeG]

/-- A list kind: an `LK` constructor, or else a Lean variable of type `LK`. -/
def lk (k : Syntax) : Term := if isLK k then mkIdent (`OrderMaintenance.Impl.LK ++ k.getId) else ⟨k⟩

/-- Decode a list-component selector, rejecting names other than `fst` and `snd`. -/
def sndOf (f : Syntax) : MacroM Term :=
  match f.getKind, f[0].getId with
  | ``fId, `fst => `(false)
  | ``fId, `snd => `(true)
  | _, _ => Macro.throwErrorAt f "expected `fst` or `snd`"

/-- Construct a core binary expression with the named machine primitive. -/
def bin (op : Name) (a b : Term) : MacroM Term :=
  `(Exp.bin $(mkIdent (`OrderMaintenance.Machine.BinOp ++ op)) $a $b)

/-- Count syntax nodes without depending on the non-executable `SizeOf Syntax` instance. -/
def syntaxWeight : Syntax → Nat
  | .node _ _ args => 1 + args.attach.foldl (fun total child =>
      total + syntaxWeight child.val) 0
  | _ => 1
termination_by s => sizeOf s
decreasing_by
  simp_wf
  have hchild := Array.sizeOf_lt_of_mem child.property
  omega

/-- Expand a core expression using structural syntax fuel. -/
def expandExpression : Nat → Syntax → MacroM Term
  | 0, s => Macro.throwErrorAt s "invalid expression nesting"
  | fuel + 1, s => do
    match s.getKind with
    | ``eNum => `(($(⟨s[0]⟩) : Exp))
    | ``eVar =>
      match dotted s[0] with
      | some ("P", k) => `(Exp.prm $(mkIdent (`OrderMaintenance.Impl.PF ++ k)))
      | some ("S", k) => `(Exp.sc $(mkIdent (`OrderMaintenance.Impl.SF ++ k)))
      | some ("O", k) => `(Exp.opt $(mkIdent (`OrderMaintenance.Impl.OF ++ k)))
      | _ => `(Exp.var $(str s[0]))
    | ``ePar => expandExpression fuel s[1]
    | ``eTm => `(($(⟨s[1]⟩) : Exp))
    | ``eFld =>
      let i ← expandExpression fuel s[2]
      match s[0].getId with
      | `E => `(Exp.eF $(← expF `OrderMaintenance.Impl.EF s[5]) $i)
      | `G => `(Exp.gF $(← expF `OrderMaintenance.Impl.GF s[5]) $i)
      | `C => `(Exp.cF $(← expF `OrderMaintenance.Impl.CF s[5]) $i)
      | `N => `(Exp.rd (Fld.n $(← expF `OrderMaintenance.Impl.NF s[5])) $i)
      | _ => Macro.throwErrorAt s[0] "expected a table: E, G, C or N"
    | ``eArr =>
      if isLK s[0] then Macro.throwErrorAt s "a list is not a value; use `len` or `[j].fst`"
      `(Exp.rd (Fld.a $(mkIdent (`OrderMaintenance.Impl.AF ++ s[0].getId)))
        $(← expandExpression fuel s[2]))
    | ``eLst => `(Exp.lrd $(lk s[0]) $(← sndOf s[8])
        $(← expandExpression fuel s[2]) $(← expandExpression fuel s[5]))
    | ``eLen => `(Exp.llen $(lk s[1]) $(← expandExpression fuel s[3]))
    | ``eSize => `(Exp.size $(mkIdent (`OrderMaintenance.Impl.Tbl ++ s[1].getId)))
    | ``ePath => `(Exp.prd $(← expandExpression fuel s[2]) $(← expandExpression fuel s[4]))
    | ``eMax => `(Exp.max $(← expandExpression fuel s[2]) $(← expandExpression fuel s[4]))
    | ``eMsb => `(Exp.un Machine.UnOp.msb $(← expandExpression fuel s[2]))
    | ``eMonus => `(Exp.monus $(← expandExpression fuel s[0]) $(← expandExpression fuel s[2]))
    | ``eNot => `(Exp.un Machine.UnOp.not $(← expandExpression fuel s[1]))
    | ``eShl => bin `shl (← expandExpression fuel s[0]) (← expandExpression fuel s[2])
    | ``eShr => bin `shr (← expandExpression fuel s[0]) (← expandExpression fuel s[2])
    | ``eMul => `(($(← expandExpression fuel s[0]) * $(← expandExpression fuel s[2]) : Exp))
    | ``eDiv => `(($(← expandExpression fuel s[0]) / $(← expandExpression fuel s[2]) : Exp))
    | ``eMod => `(($(← expandExpression fuel s[0]) % $(← expandExpression fuel s[2]) : Exp))
    | ``eAdd => `(($(← expandExpression fuel s[0]) + $(← expandExpression fuel s[2]) : Exp))
    | ``eSub => `(($(← expandExpression fuel s[0]) - $(← expandExpression fuel s[2]) : Exp))
    | ``eLt => bin `lt (← expandExpression fuel s[0]) (← expandExpression fuel s[2])
    | ``eLe => bin `le (← expandExpression fuel s[0]) (← expandExpression fuel s[2])
    | ``eEq => bin `eq (← expandExpression fuel s[0]) (← expandExpression fuel s[2])
    | ``eNe => do
      let a ← expandExpression fuel s[0]
      let b ← expandExpression fuel s[2]
      `(Exp.un Machine.UnOp.not $(← bin `eq a b))
    | ``eAnd => bin `and (← expandExpression fuel s[0]) (← expandExpression fuel s[2])
    | ``eOr => bin `or (← expandExpression fuel s[0]) (← expandExpression fuel s[2])
    | _ => Macro.throwErrorAt s "unexpected expression"

/-- Expand an expression with a structural bound from its syntax tree. -/
def expE (s : Syntax) : MacroM Term := expandExpression (syntaxWeight s + 1) s

/-- Expand a sequence of core-expression arguments. -/
def expArgs (args : Syntax) : MacroM Term := do
  let es ← args.getSepArgs.mapM expE
  `([$es,*])

/-- `p.call [args] [dsts]`. -/
def call (p args : Syntax) (ds : Array Syntax) : MacroM Term := do
  let p : Term := ⟨p⟩
  let as ← expArgs args
  let ds : Array Term := ds.map str
  `(Proc.call $p $as [$ds,*])

mutual

/-- Expand a statement sequence using structural syntax fuel. -/
def expandStatements : Nat → Array Syntax → MacroM Term
  | 0, _ => Macro.throwError "invalid statement nesting"
  | fuel + 1, ss => do
    let some last := ss.back? | Macro.throwError "empty block"
    ss.pop.foldrM (fun s acc => do `(Stm.seq $(← expandStatement fuel s) $acc))
      (← expandStatement fuel last)

/-- Expand one core statement using structural syntax fuel. -/
def expandStatement : Nat → Syntax → MacroM Term
  | 0, s => Macro.throwErrorAt s "invalid statement nesting"
  | fuel + 1, s => do
    match s.getKind with
    | ``sId =>
      match s[0].getId with
      | `skip => `(Stm.skip)
      | `fail => `(Stm.fail)
      | `bug => `(Stm.bug)
      | `prepCommit => `(Stm.prepCommit)
      | `jobClear => `(Stm.jobClear)
      | _ => pure ⟨s[0]⟩
    | ``sTm => `(($(⟨s[1]⟩) : Stm))
    | ``sBlk => expandStatements fuel s[1][0].getSepArgs
    | ``sAsg =>
      match dotted s[0] with
      | some ("S", k) => `(Stm.wsc $(mkIdent (`OrderMaintenance.Impl.SF ++ k)) $(← expE s[2]))
      | _ => `(Stm.assign $(str s[0]) $(← expE s[2]))
    | ``sAsgT => `(Stm.assign $(⟨s[1]⟩) $(← expE s[4]))
    | ``sNew => `(Stm.push $(mkIdent (`OrderMaintenance.Impl.Tbl ++ s[3].getId)) $(str s[0]))
    | ``sFld =>
      let i ← expE s[2]
      let e ← expE s[7]
      match s[0].getId with
      | `E => `(Stm.weF $(← expF `OrderMaintenance.Impl.EF s[5]) $i $e)
      | `G => `(Stm.wgF $(← expF `OrderMaintenance.Impl.GF s[5]) $i $e)
      | `C => `(Stm.wcF $(← expF `OrderMaintenance.Impl.CF s[5]) $i $e)
      | `N => `(Stm.wr (Fld.n $(← expF `OrderMaintenance.Impl.NF s[5])) $i $e)
      | _ => Macro.throwErrorAt s[0] "expected a table: E, G, C or N"
    | ``sArr =>
      let a := mkIdent (`OrderMaintenance.Impl.AF ++ s[0].getId)
      `(Stm.wr (Fld.a $a) $(← expE s[2]) $(← expE s[5]))
    | ``sLst =>
      `(Stm.lwr $(lk s[0]) $(← sndOf s[8]) $(← expE s[2]) $(← expE s[5]) $(← expE s[10]))
    | ``sApp => `(Stm.lgrow $(lk s[1]) $(← expE s[3]) $(← expE s[6]) $(← expE s[8]))
    | ``sPop => `(Stm.lshrink $(lk s[1]) $(← expE s[3]))
    | ``sClr => `(Stm.lclear $(lk s[1]) $(← expE s[3]))
    | ``sIf =>
      let c ← expE s[1]
      let t ← expandStatement fuel s[3]
      let e ← if s[4].getNumArgs == 0 then `(Stm.skip) else expandStatement fuel s[4][1]
      `(Stm.ite $c $t $e)
    | ``sFor => `(Stm.loop $(str s[1]) $(← expE s[3]) $(← expandStatement fuel s[5]))
    | ``sTry => `(Stm.catch $(← expandStatement fuel s[1]) $(← expandStatement fuel s[3]))
    | ``sPath => `(Stm.pwr $(← expE s[2]) $(← expE s[4]) $(← expE s[7]))
    | ``sCon =>
      unless s[0].getId ∈ [`rowReset, `prepInit, `prepSet, `prepPath, `jobSet, `pcSet] do
        Macro.throwErrorAt s[0] "not a statement constructor; call a procedure with `call p(…)`"
      let args ← s[2].getSepArgs.mapM expE
      `($(mkIdent (`OrderMaintenance.Impl.Stm ++ s[0].getId)) $args*)
    | ``sCall1 => call s[2] s[4] #[(s[0])]
    | ``sCallN => call s[4] s[6] s[1].getSepArgs
    | ``sCall0 => call s[1] s[3] #[]
    | ``sCall1T => call s[3] s[6] #[(s[0])]
    | ``sCallNT => call s[5] s[8] s[1].getSepArgs
    | ``sCall0T => call s[2] s[5] #[]
    | _ => Macro.throwErrorAt s "unexpected statement"

end

/-- Expand a statement sequence with a structural bound from its syntax tree. -/
def expSeq (ss : Array Syntax) : MacroM Term :=
  expandStatements (ss.foldl (fun total s => total + syntaxWeight s) 1) ss

/-- Expand a statement with a structural bound from its syntax tree. -/
def expS (s : Syntax) : MacroM Term := expandStatement (syntaxWeight s + 1) s

/-- Surface notation embedding a core statement sequence as a Lean term. -/
syntax (name := cmStm) "cm{" cmSeq "}" : term
/-- Surface notation embedding a core expression as a Lean term. -/
syntax (name := cmExp) "cme{" cmE "}" : term

/-- Expand a complete core statement with fuel derived from its syntax tree. -/
@[macro cmStm] def expandStm : Macro := fun s => expSeq s[1][0].getSepArgs
/-- Expand a complete core expression with fuel derived from its syntax tree. -/
@[macro cmExp] def expandExp : Macro := fun s => expE s[1]

end OrderMaintenance.Impl.CM
