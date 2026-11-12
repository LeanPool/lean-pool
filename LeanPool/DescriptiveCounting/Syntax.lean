/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

/-!
# A surface syntax for first-order formulas

Mathlib's `FirstOrder.Language.BoundedFormula` is locally nameless: a variable
bound by the `k`-th enclosing block is written `Sum.inr i` under `k - 1`
applications of `Sum.inl`. Writing a clause by hand therefore means counting
blocks, and reading one means counting them back.

`fo%` removes the counting. It is a *macro*: it elaborates to exactly the
`DescriptiveComplexity.Formula.iAlls` / `Term.var (Sum.inr _)` term one would
have written, so a definition converted to it is unchanged, its equation lemma
is unchanged, and every proof about it – `simp only [myClause,
Formula.realize_iAlls, …]` – keeps working verbatim.

```
fo% ∀ x₀ x₁ x₂ x₃,
  (((patV(x₀) ∧ patV(x₁)) ∧ patE(x₀, x₁)) ∧ map(x₀, x₂)) ∧ map(x₁, x₃) →
    hostE(x₂, x₃)
```

## The syntax

Connectives are `∧ ∨ ¬ → ↔` (for `⊓ ⊔ ∼ .imp .iff`), with `⊤ᶠ` and `⊥ᶠ` for the
constants; `∧` and `∨` associate to the right, so a left-nested conjunction
needs its parentheses. `∀ x y z, φ` and `∃ x y z, φ` each bind *one* block, so
they produce a single `iAlls (Fin 3)` and `Formula.realize_iAlls` fires once,
as it does today. `⋀ i : T, φ` and `⋁ i : T, φ` are the finite `Formula.iInf`
and `Formula.iSup` over a Lean type; their binder is a Lean variable, not an
object variable.

Atoms come in two forms, matching the two conventions of the library:

* `R(x, y)` applies a *relation symbol*, giving `Relations.formula₂ R
  (Term.var x) (Term.var y)`. Every arity is accepted: arity 1 and 2 go to
  Mathlib's `formula₁` and `formula₂`, and anything else to `Relations.formula`
  on a vector, which is what a hand-written arity-3 atom does anyway.
* `f⟨x, y⟩` applies a *formula builder*, one of the `α`-polymorphic
  abbreviations a problem file defines for its own atoms; it is plain function
  application, the builder receiving the *variables* (the library is
  relational, so a builder never needs a term: every term is a variable).
* `f⦃φ, ψ⦄` applies a builder that takes *formulas*, such as a three-way
  exclusive or, to formulas of the surface syntax, translated where they
  stand: a variable bound outside the braces is in scope inside them.

In both forms the symbol may be an applied term rather than a bare name,
written in parentheses: `(kcColorSym i)(x)` for the `i`-th of a family of
relation variables, `(conflict positive)⟨x, y⟩` for a builder taking a
parameter.

`x ≐ y` is `Term.equal`, and `!e` escapes to an arbitrary Lean term – as a
whole formula, or (inside an atom's argument list) as a variable that the
macro should pass through untouched. `if c then φ else ψ` chooses between two
formulas by a Lean proposition, as the defining formula of an interpretation
does by its tags.

## Free variables

The variables a formula does *not* bind have to be declared, since the macro
must lift them under every block:

* `fo%[t, t'] φ` declares `t` and `t'` as variables of the ambient
  free-variable type. This is the shape of a builder such as
  `fun (t t' : α) => …`.
* `fo%⟨u, v⟩ φ` declares the *arguments* of an interpretation's defining
  formula, whose free-variable type is `Fin n × Fin dim`: `u` is the coordinate
  `(0, 0)`, `v` is `(1, 0)`, and `v[1]` is `(1, 1)`.

Both clauses may appear, the arguments first. An identifier that is neither
bound nor declared is an error rather than a silently captured Lean constant.

## What it does not do

The macro is source-level only: goals, `#print` and the documentation still
show the underlying `iAlls` term. Terms are out of scope, the library being
relational throughout.
-/

public meta section

namespace DescriptiveComplexity

open Lean

/-- An object variable: a name bound by `fo%`, a coordinate of a declared
interpretation argument, or `!e` for a verbatim Lean term. -/
declare_syntax_cat fovar
/-- A named object variable. -/
syntax ident : fovar
/-- A coordinate of an interpretation argument. -/
syntax ident noWs "[" num "]" : fovar
/-- An embedded Lean variable term. -/
syntax "!" term:max : fovar

/-- A first-order formula in surface syntax; see the module docstring. -/
declare_syntax_cat foform
/-- A parenthesized formula. -/
syntax:max "(" foform ")" : foform
/-- The true formula. -/
syntax:max "⊤ᶠ" : foform
/-- The false formula. -/
syntax:max "⊥ᶠ" : foform
/-- An atomic relation named by an identifier. -/
syntax:max ident noWs "(" fovar,* ")" : foform
/-- A formula builder named by an identifier. -/
syntax:max ident noWs "⟨" fovar,* "⟩" : foform
/-- An atomic relation supplied as a Lean term. -/
syntax:max "(" term ")" noWs "(" fovar,* ")" : foform
/-- A formula builder supplied as a Lean term. -/
syntax:max "(" term ")" noWs "⟨" fovar,* "⟩" : foform
/-- A named connective applied to formulas. -/
syntax:max ident noWs "⦃" foform,* "⦄" : foform
/-- A Lean connective applied to formulas. -/
syntax:max "(" term ")" noWs "⦃" foform,* "⦄" : foform
/-- A conditional formula. -/
syntax:max "if " term " then " foform " else " foform : foform
/-- An embedded Lean formula. -/
syntax:max "!" term:max : foform
/-- Equality of object variables. -/
syntax:max fovar " ≐ " fovar : foform
/-- Negation of a formula. -/
syntax:40 "¬ " foform:41 : foform
/-- Conjunction of formulas. -/
syntax:35 foform:36 " ∧ " foform:35 : foform
/-- Disjunction of formulas. -/
syntax:30 foform:31 " ∨ " foform:30 : foform
/-- Equivalence of formulas. -/
syntax:25 foform:26 " ↔ " foform:26 : foform
/-- Implication between formulas. -/
syntax:20 foform:21 " → " foform:20 : foform
/-- Conjunction indexed by a Lean type. -/
syntax:max "⋀ " ident (" : " term)? ", " foform : foform
/-- Disjunction indexed by a Lean type. -/
syntax:max "⋁ " ident (" : " term)? ", " foform : foform
/-- Universal quantification over object variables. -/
syntax:max "∀ " ident+ ", " foform : foform
/-- Existential quantification over object variables. -/
syntax:max "∃ " ident+ ", " foform : foform

/-- `fo%⟨u, v⟩[t, t'] φ` is the formula `φ`, written with named variables:
`u` and `v` name the arguments of an interpretation's defining formula, `t`
and `t'` the free variables of the ambient formula. See the module docstring. -/
syntax (name := foTerm) "fo%" ("⟨" ident,* "⟩")? ("[" ident,* "]")? foform : term

namespace FOSurface

/-- `Sum.inl` applied `d` times to `e`: the lift of a variable of an outer
block to the free-variable type of the `d`-th block inside it. -/
def liftIn : Nat → Term → MacroM Term
  | 0, e => pure e
  | d + 1, e => do liftIn d (← `(Sum.inl $e))

/-- What the macro knows at a point of the formula: how many blocks are open,
which names they bound (with the depth at which each was bound and its index in
its block), which names are free variables of the ambient formula, and which
name the arguments of an interpretation. -/
structure Env where
  /-- The number of quantifier blocks open at this point. -/
  depth : Nat
  /-- The bound names, each with its birth depth and its index in its block. -/
  vars : List (Name × Nat × Nat)
  /-- The declared free variables of the ambient formula. -/
  free : List Name
  /-- The declared arguments of an interpretation's defining formula. -/
  args : List Name

/-- Open one more block, binding `xs` in order. -/
def Env.push (env : Env) (xs : Array Ident) : Env :=
  { env with
    depth := env.depth + 1,
    vars := env.vars ++ xs.toList.zipIdx.map fun (x, i) => (x.getId, env.depth, i) }

/-- Translate one occurrence of an object variable. -/
def transVar (env : Env) (t : TSyntax `fovar) : MacroM Term := do
  if let `(fovar| !$e) := t then return e
  let coord : Nat := if let `(fovar| $_:ident[$j]) := t then j.getNat else 0
  unless t.raw[0].isIdent do Macro.throwErrorAt t "expected an object variable"
  let i : Name := t.raw[0].getId
  if let some k := env.args.idxOf? i then
    return ← liftIn env.depth
      (← `(($(Syntax.mkNumLit (toString k)), $(Syntax.mkNumLit (toString coord)))))
  match env.vars.reverse.find? (fun (p : Name × Nat × Nat) => p.1 == i) with
  | some (_, born, idx) =>
      liftIn (env.depth - born - 1) (← `(Sum.inr $(Syntax.mkNumLit (toString idx))))
  | none =>
      if env.free.contains i then
        liftIn env.depth (mkIdent i)
      else
        Macro.throwErrorAt t s!"'{i}' is not an object variable in scope: bind it, \
          or declare it in the ⟨…⟩ or […] clause of fo%"

/-- Translate an atom applying the relation symbol `r` to object variables. -/
def transRel (env : Env) (r : Term) (args : Array (TSyntax `fovar)) : MacroM Term := do
  let vs ← args.mapM (transVar env)
  let ts ← vs.mapM fun v => `(FirstOrder.Language.Term.var $v)
  match ts.size with
  | 1 => `(FirstOrder.Language.Relations.formula₁ $r $(ts[0]!))
  | 2 => `(FirstOrder.Language.Relations.formula₂ $r $(ts[0]!) $(ts[1]!))
  | _ => `(FirstOrder.Language.Relations.formula $r ![$ts,*])

/-- Translate an atom applying the formula builder `f` to object variables. -/
def transBuilder (env : Env) (f : Term) (args : Array (TSyntax `fovar)) :
    MacroM Term := do
  let vs ← args.mapM (transVar env)
  `($f $vs*)

/-- A structural bound also covers synthetic syntax without source positions. -/
private def syntaxDepth : Syntax → Nat
  | .node _ _ args => 1 + args.attach.foldl (fun n s => max n (syntaxDepth s.val)) 0
  | _ => 1
termination_by s => sizeOf s
decreasing_by
  simp_wf
  have h := Array.sizeOf_lt_of_mem s.property
  omega

/-- Translate a formula of the surface syntax to the term it abbreviates. -/
private def trans (fuel : Nat) (env : Env) (stx : TSyntax `foform) : MacroM Term := do
  match fuel with
  | 0 => Macro.throwErrorAt stx "first-order syntax exceeds its syntax-tree bound"
  | fuel + 1 =>
    match stx with
    | `(foform| ($φ)) => trans fuel env φ
    | `(foform| ⊤ᶠ) => `(Top.top)
    | `(foform| ⊥ᶠ) => `(Bot.bot)
    | `(foform| !$t) => pure t
    | `(foform| ¬ $φ) => do `(FirstOrder.Language.BoundedFormula.not $(← trans fuel env φ))
    | `(foform| $φ ∧ $ψ) => do `($(← trans fuel env φ) ⊓ $(← trans fuel env ψ))
    | `(foform| $φ ∨ $ψ) => do `($(← trans fuel env φ) ⊔ $(← trans fuel env ψ))
    | `(foform| $φ → $ψ) => do `(($(← trans fuel env φ)).imp $(← trans fuel env ψ))
    | `(foform| $φ ↔ $ψ) => do `(($(← trans fuel env φ)).iff $(← trans fuel env ψ))
    | `(foform| $x:fovar ≐ $y:fovar) => do
        `(FirstOrder.Language.Term.equal
            (FirstOrder.Language.Term.var $(← transVar env x))
            (FirstOrder.Language.Term.var $(← transVar env y)))
    | `(foform| $r:ident($args,*)) => transRel env r args.getElems
    | `(foform| ($r:term)($args,*)) => transRel env r args.getElems
    | `(foform| $f:ident⟨$args,*⟩) => transBuilder env f args.getElems
    | `(foform| ($f:term)⟨$args,*⟩) => transBuilder env f args.getElems
    | `(foform| $f:ident⦃$φs,*⦄) => do `($f $(← φs.getElems.mapM (trans fuel env))*)
    | `(foform| ($f:term)⦃$φs,*⦄) => do `($f $(← φs.getElems.mapM (trans fuel env))*)
    | `(foform| if $c then $φ else $ψ) => do
        let φ' ← trans fuel env φ
        let ψ' ← trans fuel env ψ
        `(if $c then $φ' else $ψ')
    | `(foform| ⋀ $i $[: $t]?, $φ) => do
        `(FirstOrder.Language.Formula.iInf (fun $i $[: $t]? => $(← trans fuel env φ)))
    | `(foform| ⋁ $i $[: $t]?, $φ) => do
        `(FirstOrder.Language.Formula.iSup (fun $i $[: $t]? => $(← trans fuel env φ)))
    | `(foform| ∀ $xs*, $φ) => do
        let body ← trans fuel (env.push xs) φ
        `(FirstOrder.Language.Formula.iAlls (Fin $(Syntax.mkNumLit (toString xs.size))) $body)
    | `(foform| ∃ $xs*, $φ) => do
        let body ← trans fuel (env.push xs) φ
        `(FirstOrder.Language.Formula.iExs (Fin $(Syntax.mkNumLit (toString xs.size))) $body)
    | _ => Macro.throwErrorAt stx "unsupported first-order syntax"

/-- The names of an optional comma-separated declaration clause. -/
def declared (o : Option (Syntax.TSepArray `ident ",")) : List Name :=
  match o with
  | some xs => xs.getElems.toList.map (·.getId)
  | none => []

end FOSurface

macro_rules
  | `(fo% $[⟨$as,*⟩]? $[[$fs,*]]? $φ) =>
      FOSurface.trans (FOSurface.syntaxDepth φ.raw)
        { depth := 0, vars := [], free := FOSurface.declared fs,
          args := FOSurface.declared as } φ

end DescriptiveComplexity
