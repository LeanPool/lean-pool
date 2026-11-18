/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCheckedValue.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.WeakCheckedValue

/-!
# Internal Checked Value
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

theorem checkedValue_complete (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hv : e 0 = checkedCode (e 2) (e 1)) :
    checkedValueFormula.Sat (M : Set ZFSet) e := by
  exact checkedValue_complete_without_choice M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity e he hv

theorem checkedValue_spec (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    checkedValueFormula.Sat (M : Set ZFSet) e ↔ e 0 = checkedCode (e 2) (e 1) := by
  exact checkedValue_spec_without_choice M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity e he

end TuringRigidity.ElementaryModel

end OAI
