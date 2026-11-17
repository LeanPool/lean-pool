/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalInverseIso.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalInverseGraph
public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseConditions

/-!
# Internal Inverse Iso
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalInverseIso
open TransitiveNameModel BoundedSetTheory CountableForcing InternalInverseGraph
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem inverse_graph (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p) :
    inverse a b f ∈ M ∧ ∀ p q,
      ZFSet.pair (label b p) (label a q) ∈ inverse a b f ↔ q = e.symm p := by
  refine ⟨inverse_mem M a b f hM hT ha hb hf,?_⟩
  intro p q
  rw [pair_inverse]
  simp only [label_mem,true_and,he]
  constructor
  · intro h
    apply e.injective
    rw [OrderIso.apply_symm_apply]
    exact h.symm
  · intro h
    rw [h,OrderIso.apply_symm_apply]

end TuringRigidity.InternalInverseIso

end OAI
