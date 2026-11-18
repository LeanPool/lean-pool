/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedFormulaRename.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteTuple

/-!
# Bounded Formula Rename
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

@[simp] theorem Formula.eval_rename_comp (p : Formula) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (p.rename r).Eval e ↔ p.Eval (e ∘ r) := Formula.eval_rename p r e
end TuringRigidity.BoundedSetTheory

end OAI
