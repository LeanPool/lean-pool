/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenColumnAbsorption.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenLiteralAbsorption
public import LeanPool.TuringConeRigidity.SetModels.InternalOrderIsoTransport
public import LeanPool.TuringConeRigidity.SetModels.InternalSingletonColumn
public import LeanPool.TuringConeRigidity.CohenForcing.CohenFactorIteration

/-!
# Cohen Column Absorption
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenColumnAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem absorb_column (M q A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) (hA : A ∈ M) (ha : a ∈ M)
    (hBA : ZFSet.prod {a} ZFSet.omega ⊆ A)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (L : GenericFilter (Conditions (conditions A)))
    (hL : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) L) :
    let B := ZFSet.prod {a} ZFSet.omega
    let R := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) L
    ∃ W : GenericFilter (Conditions (conditions ZFSet.omega)),
      AtomicForcing.GroundGeneric M W ∧
      AtomicForcing.GroundGeneric (genericExtensionSet M (conditions ZFSet.omega) W.carrier) R ∧
      genericExtensionSet (genericExtensionSet M (conditions ZFSet.omega) W.carrier)
        (conditions (A \ B)) R.carrier =
          genericExtensionSet (genericExtensionSet M q G.carrier) (conditions A) L.carrier := by
  let N := genericExtensionSet M q G.carrier
  let B := ZFSet.prod {a} ZFSet.omega
  let J := projected A B hBA L
  let R := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) L
  obtain ⟨hN,hTN,hMN,_⟩ := RegularTreeExtension.extension_properties M q hM hT hq G hG
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hω
  have hcB := conditions_mem M B hM hT hB
  have hcω := conditions_mem M ZFSet.omega hM hT hω
  have hJ := projected_groundGeneric N A B hN hTN (hMN hA) (hMN hB) hBA L hL
  have hR := CohenUntouchedGeneric.untouched_ground_generic N A B hN hTN (hMN hA) (hMN hB) hBA L hL
  have hLR := CohenFactorIteration.extension_eq N A B hN hTN (hMN hA) (hMN hB) hBA L hL
  obtain ⟨e,f,hf,hfe⟩ := InternalSingletonColumn.internal_column_iso M a hM hT ha
  let H := AutomorphismName.mapFilter e J
  have hH := InternalOrderIsoTransport.map_ground_generic N _ _ f hN hTN
    (hMN hcB) (hMN hcω) (hMN hf) e hfe J hJ
  have hHe := InternalOrderIsoTransport.extension_eq N _ _ f hN hTN
    (hMN hcB) (hMN hcω) (hMN hf) e hfe J hJ
  obtain ⟨W,hW,hWe⟩ := CohenLiteralAbsorption.same_generics_absorption M q hM hT hq hct G hG H hH
  have he : genericExtensionSet M (conditions ZFSet.omega) W.carrier =
      genericExtensionSet N (conditions B) J.carrier := hWe.trans hHe
  refine ⟨W,hW,?_,?_⟩
  · rw [he]; exact hR
  · rw [he]; exact hLR

end TuringRigidity.CohenColumnAbsorption

end OAI
