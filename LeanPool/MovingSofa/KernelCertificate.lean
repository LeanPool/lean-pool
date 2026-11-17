/-
Copyright (c) 2020 Microsoft Corporation and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, OpenAI
-/
module -- shake: keep-downstream

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.AuxLemma

/-!
# Closed kernel certificates

The interval leaves are independent closed computations. Ordinary auxiliary-lemma scheduling
allows their kernel checks to proceed concurrently, without a synchronous barrier at each leaf.
The proof construction and auxiliary-lemma cache match `decide +kernel`.
-/

public meta section

open Lean Meta Elab Tactic

/-- Decide a closed proposition using an ordinary kernel-checked auxiliary theorem. -/
elab (name := gerverKernelDecide) "gerver_kernel_decide" : tactic =>
  closeMainGoalUsing `gerver_kernel_decide fun expectedType _ => do
    let mut expectedType ← instantiateMVars expectedType
    if expectedType.hasFVar then
      expectedType ← zetaReduce expectedType
    if expectedType.hasMVar || expectedType.hasFVar then
      throwError "expected a closed proposition"
    let proof ← mkDecideProof expectedType
    let levelsInType := (collectLevelParams {} expectedType).params
    let levels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    let name ← mkAuxLemma levels expectedType proof
    pure (mkConst name (levels.map Level.param))
