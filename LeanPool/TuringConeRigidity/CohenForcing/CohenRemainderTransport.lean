/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenRemainderTransport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenFreshColumn
public import LeanPool.TuringConeRigidity.SetModels.InternalOrderIsoTransport

/-!
# Cohen Remainder Transport
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.CohenRemainderTransport
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
  InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem transport_to_remainder (M N K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C)
    (U : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hU : AtomicForcing.GroundGeneric N U) :
    ∃ R : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C
      ZFSet.omega))),
      AtomicForcing.GroundGeneric N R ∧
        genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega))
          R.carrier =
          genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega)) U.carrier := by
  rw [CohenFreshColumn.product_difference]
  obtain ⟨_,_,_,_,_,_,e,g,hg,hge,horders⟩ :=
    InternalCohenUnusedColumns.unused_columns_forcing M K C hM hT hK hC hCK hct
  have hfi := InternalInverseGraph.inverse_mem M _ _ g hM hT
    horders.1 horders.2.2.1 hg
  have hfie (sourceCondition : Conditions (conditions (K.prod ZFSet.omega)))
      (targetCondition : Conditions (conditions ((K \ C).prod ZFSet.omega))) :
      ZFSet.pair (label _ sourceCondition) (label _ targetCondition) ∈
        InternalInverseGraph.inverse (conditions ((K \ C).prod ZFSet.omega))
          (conditions (K.prod ZFSet.omega)) g ↔ targetCondition = e.symm sourceCondition := by
    rw [InternalInverseGraph.pair_inverse]
    simp only [label_mem,true_and,hge]
    constructor
    · intro inversePair
      apply e.injective
      rw [OrderIso.apply_symm_apply]
      exact inversePair.symm
    · intro inversePair
      rw [inversePair,OrderIso.apply_symm_apply]
  exact ⟨AutomorphismName.mapFilter e.symm U,
    InternalOrderIsoTransport.map_ground_generic N _ _ _ hN hTN
      (hMN horders.2.2.1) (hMN horders.1) (hMN hfi) e.symm hfie U hU,
    InternalOrderIsoTransport.extension_eq N _ _ _ hN hTN
      (hMN horders.2.2.1) (hMN horders.1) (hMN hfi) e.symm hfie U hU⟩

end TuringRigidity.CohenRemainderTransport

end OAI
