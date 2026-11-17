/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public meta import Lean.Elab.Command
public import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
public import Lean.CoreM
public import Lean.Data.Name
public import Lean.Data.OpenDecl
public import Lean.Declaration
public import Lean.Elab.Util
public import Lean.Environment
public import Lean.Exception
public import Lean.Expr
public import Lean.ResolveName

/-!
# Declaring a vocabulary

A relational vocabulary is always declared the same way: an inductive of
relation symbols indexed by arity, a `Language` whose function symbols are
`Empty`, its `IsRelational` instance, one abbreviation naming each symbol at
its arity, and one predicate reading each symbol off a structure. Only the
names and the arities differ.

`fo_language` takes those and writes the rest:

```
/-- The relational language of pattern-and-host graphs. -/
fo_language twoGraphs with tg where
  /-- `patV a`: `a` is a vertex of the pattern graph. -/
  patV : 1
  /-- `hostV a`: `a` is a vertex of the host graph. -/
  hostV : 1
```

declares `twoGraphsRel` (with `DecidableEq`), `Language.twoGraphs` with its
`IsRelational` instance, and the symbols `tgPatV` and `tgHostV`. The prefix is
the one the library's convention asks for, `tg` naming the symbols of
`Language.twoGraphs`. The docstring of the command becomes the docstring of the
language, and each symbol's becomes that of its constructor and its
abbreviation.

A vocabulary lives in `namespace FirstOrder.Language`, next to Mathlib's, while
the predicates reading it off a structure live with the problem, in
`namespace DescriptiveComplexity`. So they are two commands, and
`fo_predicates Language.twoGraphs tg` writes the second half:

```
def TGPatV {A : Type} [Language.twoGraphs.Structure A] (a₀ : A) : Prop :=
  RelMap tgPatV ![a₀]
```

one predicate per symbol, named by the prefix in upper case, as the catalog
names them throughout. It reads the symbols out of the environment, so it takes
no list; the vocabulary must have been declared by `fo_language`, or by hand
following the same convention.

The generated declarations are the hand-written ones, so a vocabulary
converted to these commands changes nothing that reads it.
-/

public meta section

namespace DescriptiveComplexity

open Lean Elab Command

/-- One symbol of a vocabulary: `patV : 1`. -/
syntax foSymDecl := (docComment)? ident " : " num

/-- Declare a relational language and its symbols; see the module docstring. -/
syntax (name := foLanguage) (docComment)?
  "fo_language " ident " with " ident " where" manyIndent(ppLine foSymDecl) : command

/-- Declare the predicates reading a vocabulary's symbols off a structure; see
the module docstring. -/
syntax (name := foPredicates) "fo_predicates " ident ident : command

namespace FOVocabulary

/-- `patV` under the prefix `tg` gives `tgPatV`; under `TG`, `TGPatV`. -/
def prefixed (p n : Name) : Name :=
  Name.mkSimple (p.toString ++ n.toString.capitalize)

/-- A docstring node carrying the given text, for a declaration the user does
not name. -/
def mkDoc (s : String) : TSyntax `Lean.Parser.Command.docComment :=
  ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]⟩

/-- The user's docstring, or a generic one when there is none. -/
def docOr (d? : Option Syntax) (fallback : String) :
    TSyntax `Lean.Parser.Command.docComment :=
  match d? with
  | some d => ⟨d⟩
  | none => mkDoc fallback

/-- The constructors of a vocabulary's symbol inductive, each with its arity
and its docstring: the full name, so that a caller can look the constructor up,
and the short one, which the symbol and predicate names are built from. -/
def baseSymbols (relName : Name) : CommandElabM (Array (Name × Nat × Option String)) := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? relName
    | throwError "'{relName}' is not an inductive type: was the vocabulary \
        declared by `fo_language`?"
  liftTermElabM <| iv.ctors.toArray.mapM fun c => do
    let some ci := env.find? c | throwError "missing constructor '{c}'"
    let some k := (← Meta.whnf ci.type).appArg!.nat?
      | throwError "cannot read the arity of '{c}'"
    return (c.updatePrefix .anonymous, k, ← findDocString? env c)

/-- The symbol inductive of a vocabulary, from the vocabulary's name. -/
def relInductive (langId : Ident) : CommandElabM Name :=
  return (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo langId).appendAfter "Rel"

end FOVocabulary

open FOVocabulary in
/-- Elaborate `fo_language`. -/
@[command_elab foLanguage]
def elabFoLanguage : CommandElab := fun stx => do
  let langId : Ident := ⟨stx[2]⟩
  let pfx : Name := stx[4].getId
  let relId := mkIdentFrom langId (Name.mkSimple (langId.getId.toString ++ "Rel"))
  let syms := stx[6].getArgs.map fun d =>
    (d[0].getOptional?, (⟨d[1]⟩ : Ident), (⟨d[3]⟩ : TSyntax `num))
  let ctors ← syms.mapM fun (d?, n, k) =>
    `(Lean.Parser.Command.ctor|
      $(docOr d? "A relation symbol."):docComment | $n:ident : $relId $k)
  elabCommand (← `(command|
    $(mkDoc "The relation symbols of the language."):docComment
    inductive $relId : ℕ → Type where $ctors* deriving DecidableEq))
  elabCommand (← `(command|
    $(docOr (stx[0].getOptional?) "A relational language."):docComment
    protected def $langId : FirstOrder.Language := ⟨fun _ => Empty, $relId⟩))
  -- `protected` obliges every later reference to use the qualified name
  let langFull := mkIdentFrom langId (`_root_ ++ (← getCurrNamespace) ++ langId.getId)
  elabCommand (← `(command|
    instance : FirstOrder.Language.IsRelational $langFull :=
      fun _ => (inferInstance : IsEmpty Empty)))
  for (d?, n, k) in syms do
    let symId := mkIdentFrom n (prefixed pfx n.getId)
    elabCommand (← `(command| $(docOr d? "A relation symbol."):docComment
      abbrev $symId : ($langFull).Relations $k := .$n))

open FOVocabulary in
/-- Elaborate `fo_predicates`. -/
@[command_elab foPredicates]
def elabFoPredicates : CommandElab := fun stx => do
  let langId : Ident := ⟨stx[1]⟩
  let pfx : Name := stx[2].getId
  let upper := Name.mkSimple pfx.toString.toUpper
  for (c, k, doc?) in ← baseSymbols (← relInductive langId) do
    let predId := mkIdentFrom langId (prefixed upper c)
    let symId := mkIdentFrom langId (prefixed pfx c)
    let xs := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
    let args ← xs.mapM fun x => `(term| $x:ident)
    -- `A` is written out rather than quoted, so that it stays a usable
    -- argument name at the call sites (`TGPatV (A := A)`)
    let aId := mkIdent `A
    let aTy : Term := ⟨aId.raw⟩
    let binders ← xs.mapM fun x =>  `(Lean.Parser.Term.bracketedBinderF| ($x : $aTy))
    elabCommand (← `(command|
      $(mkDoc (doc?.getD s!"The `{c}` relation.")):docComment
      def $predId {$aId : Type} [($langId).Structure $aTy] $binders* : Prop :=
        FirstOrder.Language.Structure.RelMap $symId ![$args,*]))

end DescriptiveComplexity
