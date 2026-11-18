/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenManyAbsorption.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnAbsorption
public import LeanPool.TuringConeRigidity.CohenForcing.CohenPartitionJoint
public import LeanPool.TuringConeRigidity.SetModels.InternalInverseIso

/-!
# Cohen Many Absorption
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenManyAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem same_generics_absorption (M q A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) (hA : A ∈ M) (ha : a ∈ M)
    (hBA : ZFSet.prod {a} ZFSet.omega ⊆ A)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (L : GenericFilter (Conditions (conditions A)))
    (hL : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) L) :
    ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (conditions A) U.carrier =
        genericExtensionSet (genericExtensionSet M q G.carrier) (conditions A) L.carrier := by
  let B := ZFSet.prod {a} ZFSet.omega
  let R := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) L
  obtain ⟨W,hW,hR,hWR⟩ := CohenColumnAbsorption.absorb_column M q A a hM hT hq hct hA ha hBA G hG
    L hL
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hω
  have hcB := conditions_mem M B hM hT hB
  have hcω := conditions_mem M ZFSet.omega hM hT hω
  obtain ⟨e,f,hf,hfe⟩ := InternalSingletonColumn.internal_column_iso M a hM hT ha
  obtain ⟨hfi,hfie⟩ := InternalInverseIso.inverse_graph M _ _ f hM hT hcB hcω hf e hfe
  let J := AutomorphismName.mapFilter e.symm W
  have hJ := InternalOrderIsoTransport.map_ground_generic M _ _ _ hM hT hcω hcB hfi e.symm hfie W hW
  have hJe := InternalOrderIsoTransport.extension_eq M _ _ _ hM hT hcω hcB hfi e.symm hfie W hW
  have hRJ : AtomicForcing.GroundGeneric (genericExtensionSet M (conditions B) J.carrier) R := by
    rw [hJe]; exact hR
  obtain ⟨U,hU,hUe⟩ := CohenPartitionJoint.reassemble M A B hM hT hA hB hBA J hJ R hRJ
  refine ⟨U,hU,hUe.trans ?_⟩
  rw [hJe]
  exact hWR

end TuringRigidity.CohenManyAbsorption

end OAI
