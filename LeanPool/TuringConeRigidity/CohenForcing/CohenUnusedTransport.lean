/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenUnusedTransport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenFreshColumn
public import LeanPool.TuringConeRigidity.SetModels.InternalOrderIsoTransport

/-!
# Cohen Unused Transport
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenUnusedTransport
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
  InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem transport (M N K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C)
    (U : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C
      ZFSet.omega))))
    (hU : AtomicForcing.GroundGeneric N U) :
    ∃ GX : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
      AtomicForcing.GroundGeneric N GX ∧
        genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega)) GX.carrier =
          genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega))
            U.carrier := by
  generalize hD : ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega = D at U hU ⊢
  have hDe : D = ZFSet.prod (K \ C) ZFSet.omega := hD.symm.trans
    (CohenFreshColumn.product_difference K C ZFSet.omega)
  clear hD
  subst D
  obtain ⟨_,_,_,_,_,_,e,g,hg,hge,horders⟩ :=
    InternalCohenUnusedColumns.unused_columns_forcing M K C hM hT hK hC hCK hct
  exact ⟨AutomorphismName.mapFilter e U,
    InternalOrderIsoTransport.map_ground_generic N _ _ g hN hTN
      (hMN horders.1) (hMN horders.2.2.1) (hMN hg) e hge U hU,
    InternalOrderIsoTransport.extension_eq N _ _ g hN hTN
      (hMN horders.1) (hMN horders.2.2.1) (hMN hg) e hge U hU⟩

end TuringRigidity.CohenUnusedTransport

end OAI
