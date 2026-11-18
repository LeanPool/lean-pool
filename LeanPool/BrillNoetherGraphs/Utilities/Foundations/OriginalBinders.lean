/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public meta import Lean.Elab.Term

/-!
# Stable internal binders for relocated cover data

Anonymous functions and long list literals acquire hygienic binder labels containing their
source module. Moving the fixed-cover data should preserve even those labels in the elaborated
values and generated equation theorems. This elaborator restores the original module component
in synthetic lambda and let binders; it leaves constants, universes and bound-variable indices
untouched. The term wrapper itself consumes one hygiene index, which is also restored.
-/

public meta section

namespace Utilities.Certificate

open Lean Meta Elab Term

private def originalBinderModule : Name → Name
  | .anonymous => .anonymous
  | .str parent component =>
      .str (originalBinderModule parent) (component.replace "FixedCoverData" "FixedCover")
  | .num parent index => .num (originalBinderModule parent) index

private def originalBinderName (name : Name) : Name :=
  match name with
  | .num (.str parent "_hyg") index =>
      .num (.str (originalBinderModule parent) "_hyg") (index - 1)
  | _ => originalBinderModule name

private def originalBinders : Expr → Expr
  | .lam name type body information =>
      .lam (if name.hasMacroScopes then originalBinderName name else name)
        (originalBinders type) (originalBinders body) information
  | .letE name type value body nondependent =>
      .letE (if name.hasMacroScopes then originalBinderName name else name)
        (originalBinders type) (originalBinders value) (originalBinders body) nondependent
  | .forallE name type body information =>
      .forallE name (originalBinders type) (originalBinders body) information
  | .app function argument => .app (originalBinders function) (originalBinders argument)
  | .mdata data inner => .mdata data (originalBinders inner)
  | .proj name index inner => .proj name index (originalBinders inner)
  | expression => expression

/-- Retain the synthetic binder labels of a fixed-cover definition moved into its data module. -/
syntax (name := originalBinderTerm) "original_binders% " term : term

/-- Elaborate relocated cover data with the original synthetic binder labels. -/
@[term_elab originalBinderTerm]
def elabOriginalBinderTerm : TermElab := fun termSyntax expectedType => do
  let expression ← elabTerm termSyntax[1] expectedType
  return originalBinders (← instantiateMVars expression)

end Utilities.Certificate
