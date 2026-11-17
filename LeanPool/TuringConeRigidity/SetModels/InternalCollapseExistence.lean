/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCollapseExistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseCounting
public import LeanPool.TuringConeRigidity.Representation.CountableGroundGeneric

/-!
# Internal Collapse Existence
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem exists_internal_counting_extension (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {A : ZFSet.{u}} (hA : A ∈ M)
    (hne : ∃ x, x ∈ A) :
    ∃ c ∈ M, orderSet c ∈ M ∧
      (∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) ∧
      ∃ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G ∧
        M ⊆ genericExtensionSet M c G.carrier ∧
        Transitive (genericExtensionSet M c G.carrier) ∧
        SourceT (genericExtensionSet M c G.carrier) ∧
        InternallyCountable (genericExtensionSet M c G.carrier) A := by
  classical
  obtain ⟨c,hcM,hc⟩ := conditions_exist M hM hT hA
  have h0M : (∅ : ZFSet.{u}) ∈ M := hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero
  have h0 : (∅ : ZFSet.{u}) ∈ c := (hc ∅).mpr ⟨h0M,prefix_empty A⟩
  let _ := top c h0
  obtain ⟨G,htop,hG⟩ := AtomicForcing.countable_ground_generic M ⟨∅,h0M⟩ (⊤ : Conditions c)
  refine ⟨c,hcM,orderSet_mem M hM hT hcM,hc,G,hG,?_,?_,?_,?_⟩
  · exact ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcM G.carrier htop
  · exact genericExtensionSet_transitive M c hM G.carrier
  · exact extension_sourceT M hM hT hcM (orderSet_mem M hM hT hcM) (orderSet_pair c) G hG htop
  · exact internal_counting M hM hT hA hcM hc hne G hG

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
