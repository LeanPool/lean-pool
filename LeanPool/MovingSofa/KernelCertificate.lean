/-
Copyright (c) 2020 Microsoft Corporation, 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Lean Pool contributors
-/
module

import Lean.Exception
public meta import Lean.Elab.Tactic.ElabTerm

/-! # Closed certificates checked by Lean's ordinary kernel queue

Adapted from Lean's closed decision proof construction in `Lean.Elab.Tactic.Decide`.
-/

public meta section

open Lean Meta Elab Tactic

namespace GerverSofa.PartE.Certificate

/-- Retain the original closed proposition and auxiliary name while checking the supplied proof. -/
def closeCertificate (tacticName : Name) (buildProof : Expr → MetaM Expr) : TacticM Unit := do
  closeMainGoalUsing tacticName fun expectedType _ => do
    let expectedType ← instantiateMVars expectedType
    let expectedType ← zetaReduce expectedType
    if expectedType.hasFVar || expectedType.hasMVar then
      throwError "Expected a closed certificate proposition"
    let proof ← buildProof expectedType
    let parameters := (collectLevelParams {} expectedType).params
    let levels := (← Term.getLevelNames).reverse.filter parameters.contains
    let name ← mkAuxLemma levels expectedType proof
    return mkConst name (levels.map .param)

/-- Construct the standard decision proof and use Lean's normal kernel checking queue.
This avoids blocking the elaborator on each individual arithmetic check.
-/
elab (name := certificateKernel) "certificate_kernel" : tactic =>
  closeCertificate `certificate_kernel mkDecideProof

end GerverSofa.PartE.Certificate
