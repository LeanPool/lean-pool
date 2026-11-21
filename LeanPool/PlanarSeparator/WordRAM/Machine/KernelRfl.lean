/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public meta import Lean.Elab.Tactic.Basic

/-!
# `kernel_rfl`: closing `a = b` by the kernel's definitional unfolding

`kernel_rfl` closes a goal `a = b` with `Eq.refl a` **without** asking the elaborator to check
`a ≡ b`; the kernel checks the definitional equality when the declaration is added (so nothing
is assumed: no axiom, no `native_decide`). It is meant for syntactic checks of large structured
programs with free parameters (`Stmt.regsOK U (prog B n …) = true`), which the kernel unfolds
quickly but on which the elaborator's lazy unfolding is very slow. If the equality does not
hold, the declaration is rejected by the kernel.
-/

public meta section

open Lean Elab Tactic Meta

/-- Close `a = b` by `Eq.refl a`, leaving the check `a ≡ b` to the kernel. -/
elab (name := kernelReflexivity) "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | throwError "kernel_rfl: the goal is not an equality"
  g.assign (← mkEqRefl lhs)
  replaceMainGoal []

end
